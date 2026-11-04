//! Frontier vs threshold, linear-space reconstruction, and shape dispatch, on parsed fixtures.
//!
//! usage: frontier_exp <diffs-dir> <omnidiff-baseline.csv> <out-dir> [limit] [reps]
//!
//! Writes `per_fixture.csv`, `aligns_by_bucket.csv`, `memory.csv`, `dispatch_e2e.csv`, `summary.txt`.

use difffold::frontier::{Algo, Frontier, Orient, Policy};
use difffold::{distance_with, Arena, Config, Id};
use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use tree_sitter::{Language, Node, Parser};

/// One memory sample: (nodes, held bytes, rows peak, linear peak, rows ms, linear ms).
type MemRow = (usize, usize, f64, f64, usize, usize);

struct Counting;
static CUR: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            let c = CUR.fetch_add(l.size(), Ordering::Relaxed) + l.size();
            PEAK.fetch_max(c, Ordering::Relaxed);
        }
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) };
        if !p.is_null() {
            let c = CUR.fetch_add(l.size(), Ordering::Relaxed) + l.size();
            PEAK.fetch_max(c, Ordering::Relaxed);
        }
        p
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, new) };
        if !q.is_null() {
            CUR.fetch_sub(l.size(), Ordering::Relaxed);
            let c = CUR.fetch_add(new, Ordering::Relaxed) + new;
            PEAK.fetch_max(c, Ordering::Relaxed);
        }
        q
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        CUR.fetch_sub(l.size(), Ordering::Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

fn reset_peak() -> usize {
    let c = CUR.load(Ordering::Relaxed);
    PEAK.store(c, Ordering::Relaxed);
    c
}

struct Interner(HashMap<(u16, Option<Vec<u8>>), u32>);
impl Interner {
    fn label(&mut self, kind: u16, text: Option<&[u8]>) -> u32 {
        let next = u32::try_from(self.0.len()).unwrap();
        *self
            .0
            .entry((kind, text.map(<[u8]>::to_vec)))
            .or_insert(next)
    }
}

fn convert(n: Node, src: &[u8], arena: &mut Arena, it: &mut Interner) -> Id {
    if n.child_count() == 0 {
        let l = it.label(n.kind_id(), Some(&src[n.byte_range()]));
        return arena.mk(l, &[]);
    }
    let mut c = n.walk();
    let kids: Vec<Id> = n
        .children(&mut c)
        .map(|ch| convert(ch, src, arena, it))
        .collect();
    let l = it.label(n.kind_id(), None);
    arena.mk(l, &kids)
}

fn lang(ext: &str) -> Option<Language> {
    match ext {
        "java" => Some(tree_sitter_java::LANGUAGE.into()),
        "go" => Some(tree_sitter_go::LANGUAGE.into()),
        "c" | "h" => Some(tree_sitter_c::LANGUAGE.into()),
        _ => None,
    }
}

fn find(dir: &PathBuf, stem: &str) -> Option<PathBuf> {
    std::fs::read_dir(dir)
        .ok()?
        .flatten()
        .map(|e| e.path())
        .find(|p| {
            p.file_name()
                .and_then(|f| f.to_str())
                .is_some_and(|f| f.starts_with(stem))
        })
}

fn median(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

fn quant(v: &mut [f64], q: f64) -> f64 {
    v.sort_by(f64::total_cmp);
    v[((v.len() - 1) as f64 * q).round() as usize]
}

fn bucket(k: usize) -> usize {
    match k {
        0..=1 => 0,
        2 => 1,
        3..=4 => 2,
        5..=8 => 3,
        9..=16 => 4,
        17..=32 => 5,
        33..=64 => 6,
        _ => 7,
    }
}
const BUCKET_NAMES: [&str; 8] = ["1", "2", "3-4", "5-8", "9-16", "17-32", "33-64", "65+"];

fn strip<'a>(a: &'a [Id], b: &'a [Id]) -> (&'a [Id], &'a [Id]) {
    let (n, m) = (a.len(), b.len());
    let mut p = 0;
    while p < n.min(m) && a[p] == b[p] {
        p += 1;
    }
    let mut s = 0;
    while s < n.min(m) - p && a[n - 1 - s] == b[m - 1 - s] {
        s += 1;
    }
    (&a[p..n - s], &b[p..m - s])
}

#[derive(Default, Clone)]
struct BucketAgg {
    aligns: u64,
    cells: [u64; 4],
    best: u64,
}

fn run(args: Vec<String>) {
    let (dir, base, out) = (PathBuf::from(&args[1]), &args[2], PathBuf::from(&args[3]));
    let limit: usize = args
        .get(4)
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);
    let reps: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(3);
    std::fs::create_dir_all(&out).unwrap();
    let text = std::fs::read_to_string(base).unwrap();
    let mut rows: Vec<Vec<String>> = text
        .lines()
        .skip(1)
        .map(|l| l.split(',').map(str::to_string).collect())
        .collect();
    rows.retain(|r| r.len() > 10 && r[9] == "ok");
    rows.sort_by(|a, b| {
        b[10]
            .parse::<f64>()
            .unwrap()
            .total_cmp(&a[10].parse::<f64>().unwrap())
    });

    let mut pf = std::fs::File::create(out.join("per_fixture.csv")).unwrap();
    writeln!(pf, "language,fixture,nodes_before,nodes_after,cost,drs_ms,drs_cells,drs_pairs,drs_rounds,thr_ms,thr_cells,thr_pairs,ast_ms,ast_cells,ast_pairs,ast_pushes,aligns").unwrap();
    let mut mf = std::fs::File::create(out.join("memory.csv")).unwrap();
    writeln!(mf, "fixture,n,m,nm,rows_held_cells,linear_peak_cells,rows_peak_bytes,linear_peak_bytes,rows_ms,linear_ms,extra_pairs_linear,whole_run_peak_bytes").unwrap();
    let mut ef = std::fs::File::create(out.join("dispatch_e2e.csv")).unwrap();
    writeln!(ef, "fixture,policy,ms,cells,pairs").unwrap();

    let mut buckets: Vec<BucketAgg> = vec![BucketAgg::default(); 8];
    let policies_e2e: Vec<(String, Policy)> = {
        let mut v = vec![];
        for (an, algo) in [("thr", Algo::Threshold), ("ast", Algo::AStar)] {
            for (on, o) in [
                ("keep", Orient::Keep),
                ("shorter", Orient::ShorterRows),
                ("longer", Orient::LongerRows),
                ("smallsize", Orient::SmallerSizeRows),
            ] {
                v.push((
                    format!("{an}/{on}"),
                    Policy {
                        algo,
                        orient: o,
                        sym: true,
                    },
                ));
            }
        }
        for k in [3usize, 5, 9, 17, 33, 65] {
            v.push((
                format!("hybrid{k}/keep"),
                Policy {
                    algo: Algo::Hybrid(k),
                    orient: Orient::Keep,
                    sym: true,
                },
            ));
        }
        v
    };
    let mut e2e: HashMap<String, (f64, u64, u64)> = HashMap::new();

    struct Rec {
        nodes: u32,
        cost: u32,
        drs: (f64, u64, u64, u64),
        thr: (f64, u64, u64),
        ast: (f64, u64, u64),
    }
    let mut recs: Vec<Rec> = vec![];
    let mut mem_rows: Vec<MemRow> = vec![];
    let mut done = 0usize;
    let mut verified = 0usize;

    for r in rows {
        if done >= limit {
            break;
        }
        let d = dir.join(&r[2]).join(&r[4]);
        let (Some(bp), Some(ap)) = (find(&d, "before."), find(&d, "after.")) else {
            continue;
        };
        let ext = bp
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .split('.')
            .nth(1)
            .unwrap_or("");
        let Some(l) = lang(ext) else { continue };
        let (bs, as_) = (std::fs::read(&bp).unwrap(), std::fs::read(&ap).unwrap());
        let mut parser = Parser::new();
        parser.set_language(&l).unwrap();
        let (tb, ta) = (
            parser.parse(&bs, None).unwrap(),
            parser.parse(&as_, None).unwrap(),
        );
        let mut arena = Arena::new();
        let mut it = Interner(HashMap::new());
        let (x, y) = (
            convert(tb.root_node(), &bs, &mut arena, &mut it),
            convert(ta.root_node(), &as_, &mut arena, &mut it),
        );
        let (nb, na) = (arena.size(x), arena.size(y));

        // Three solvers on the same pair, in a rotating order. Each repetition is a cold run.
        let mut drs = (0.0, 0, 0, 0, 0u32);
        let mut thr = (0.0, 0, 0, 0u32, 0u64);
        let mut ast = (0.0, 0, 0, 0u32, 0u64);
        let mut aligns = 0;
        for k in 0..3 {
            match (k + done) % 3 {
                0 => {
                    let mut ts = vec![];
                    let mut last = None;
                    for _ in 0..reps {
                        let t = Instant::now();
                        let res = distance_with(&arena, Config::PRODUCTION, x, y);
                        ts.push(t.elapsed().as_secs_f64() * 1e3);
                        last = Some(res);
                    }
                    let (c, s) = last.unwrap();
                    drs = (median(&mut ts), s.cells, s.pairs, s.rounds, c);
                }
                1 => {
                    let mut ts = vec![];
                    let mut last = None;
                    for _ in 0..reps {
                        let mut f = Frontier::new(&arena, Policy::THRESHOLD);
                        let t = Instant::now();
                        let c = f.dist(x, y);
                        ts.push(t.elapsed().as_secs_f64() * 1e3);
                        last = Some((c, f.stats));
                    }
                    let (c, s) = last.unwrap();
                    aligns = s.aligns;
                    thr = (median(&mut ts), s.cells, s.pairs, c, s.rounds);
                }
                _ => {
                    let mut ts = vec![];
                    let mut last = None;
                    for _ in 0..reps {
                        let mut f = Frontier::new(&arena, Policy::ASTAR);
                        let t = Instant::now();
                        let c = f.dist(x, y);
                        ts.push(t.elapsed().as_secs_f64() * 1e3);
                        last = Some((c, f.stats));
                    }
                    let (c, s) = last.unwrap();
                    ast = (median(&mut ts), s.cells, s.pairs, c, s.pushes);
                }
            }
        }
        assert_eq!(
            drs.4, thr.3,
            "threshold re-implementation cost differs from diff.rs on {}",
            r[4]
        );
        assert_eq!(
            drs.4, ast.3,
            "best-first cost differs from diff.rs on {}",
            r[4]
        );
        assert_eq!(
            (drs.1, drs.2, drs.3),
            (thr.1, thr.2, thr.4),
            "threshold re-implementation counters differ from diff.rs on {}",
            r[4]
        );
        verified += 1;
        writeln!(
            pf,
            "{},{},{nb},{na},{},{:.4},{},{},{},{:.4},{},{},{:.4},{},{},{},{aligns}",
            r[0],
            r[4],
            drs.4,
            drs.0,
            drs.1,
            drs.2,
            drs.3,
            thr.0,
            thr.1,
            thr.2,
            ast.0,
            ast.1,
            ast.2,
            ast.4
        )
        .unwrap();
        recs.push(Rec {
            nodes: nb + na,
            cost: drs.4,
            drs: (drs.0, drs.1, drs.2, drs.3),
            thr: (thr.0, thr.1, thr.2),
            ast: (ast.0, ast.1, ast.2),
        });

        // Dispatch end to end, cold memo, one rep each (cells and pairs are deterministic).
        for (name, p) in &policies_e2e {
            let mut f = Frontier::new(&arena, *p);
            let t = Instant::now();
            let c = f.dist(x, y);
            let ms = t.elapsed().as_secs_f64() * 1e3;
            assert_eq!(c, drs.4, "policy {name} cost differs");
            writeln!(
                ef,
                "{},{name},{ms:.4},{},{}",
                r[4], f.stats.cells, f.stats.pairs
            )
            .unwrap();
            let e = e2e.entry(name.clone()).or_insert((0.0, 0, 0));
            e.0 += ms;
            e.1 += f.stats.cells;
            e.2 += f.stats.pairs;
        }

        // Per-align comparison with a warm memo: every unequal pair that the best-first run memoised.
        let mut warm = Frontier::new(
            &arena,
            Policy {
                algo: Algo::AStar,
                orient: Orient::Keep,
                sym: true,
            },
        );
        warm.dist(x, y);
        let mut pairs = warm.memo_pairs();
        pairs.sort();
        let variants = [
            Policy {
                algo: Algo::Threshold,
                orient: Orient::Keep,
                sym: true,
            },
            Policy {
                algo: Algo::Threshold,
                orient: Orient::ShorterRows,
                sym: true,
            },
            Policy {
                algo: Algo::AStar,
                orient: Orient::Keep,
                sym: true,
            },
            Policy {
                algo: Algo::AStar,
                orient: Orient::ShorterRows,
                sym: true,
            },
        ];
        let mut top: Vec<(usize, Id, Id)> = vec![];
        for &(p, q) in &pairs {
            let (ka, kb) = (arena.kids(p), arena.kids(q));
            let (ma, mb) = strip(ka, kb);
            if ma.is_empty() || mb.is_empty() {
                continue;
            }
            let mut cells = [0u64; 4];
            let mut cost0 = None;
            for (vi, v) in variants.iter().enumerate() {
                warm.policy = *v;
                let res = warm.align(ka, kb);
                cells[vi] = res.cells;
                if let Some(c) = cost0 {
                    assert_eq!(c, res.cost, "variant costs differ");
                }
                cost0 = Some(res.cost);
            }
            let k = ma.len().max(mb.len());
            let b = &mut buckets[bucket(k)];
            b.aligns += 1;
            for (dst, src) in b.cells.iter_mut().zip(cells.iter()) {
                *dst += src;
            }
            b.best += *cells.iter().min().unwrap();
            top.push((ma.len() * mb.len(), p, q));
        }

        // Memory: stored rows against linear space on the three biggest aligns, memo warm.
        top.sort_by(|a, b| b.0.cmp(&a.0));
        warm.policy = Policy {
            algo: Algo::Threshold,
            orient: Orient::Keep,
            sym: true,
        };
        reset_peak();
        let whole_peak = {
            let base0 = CUR.load(Ordering::Relaxed);
            let mut f = Frontier::new(&arena, Policy::THRESHOLD);
            reset_peak();
            f.dist(x, y);
            PEAK.load(Ordering::Relaxed).saturating_sub(base0)
        };
        for &(nm, p, q) in top.iter().take(3).filter(|t| t.0 >= 16) {
            let (ka, kb) = (arena.kids(p), arena.kids(q));
            let (ma, mb) = strip(ka, kb);
            // Warm up both so that every pair they need is memoised; record the pair delta of the
            // linear pass, which may need pairs that the forward pass pruned.
            let _ = warm.align_rows(ma, mb);
            let before = warm.stats.pairs;
            let _ = warm.align_linear(ma, mb);
            let extra = warm.stats.pairs - before;
            let mut tr = vec![];
            let mut tl = vec![];
            let (mut held, mut lpeak) = (0, 0);
            let (mut brow, mut blin) = (0, 0);
            for _ in 0..5 {
                let b0 = reset_peak();
                let t = Instant::now();
                let (_, _, h) = warm.align_rows(ma, mb);
                tr.push(t.elapsed().as_secs_f64() * 1e3);
                brow = PEAK.load(Ordering::Relaxed) - b0;
                held = h;
                let b0 = reset_peak();
                let t = Instant::now();
                let (_, _, lp) = warm.align_linear(ma, mb);
                tl.push(t.elapsed().as_secs_f64() * 1e3);
                blin = PEAK.load(Ordering::Relaxed) - b0;
                lpeak = lp;
            }
            let (mr, ml) = (median(&mut tr), median(&mut tl));
            writeln!(
                mf,
                "{},{},{},{nm},{held},{lpeak},{brow},{blin},{mr:.4},{ml:.4},{extra},{whole_peak}",
                r[4],
                ma.len(),
                mb.len()
            )
            .unwrap();
            mem_rows.push((nm, held, mr, ml, brow, blin));
        }
        done += 1;
        if done % 100 == 0 {
            eprintln!("{done} fixtures");
        }
    }

    // ------------------------------------------------------------------------------ summary
    let mut s = String::new();
    writeln!(s, "fixtures measured: {done} (threshold re-implementation matched diff.rs cells, pairs, rounds and cost on {verified})").unwrap();
    let sum = |f: &dyn Fn(&Rec) -> f64| recs.iter().map(f).sum::<f64>();
    writeln!(
        s,
        "\n== (a) frontier vs threshold, whole-tree distance, cold memo, ordered keys =="
    )
    .unwrap();
    writeln!(s, "total cells : diff.rs {:.0}  threshold-reimpl {:.0}  best-first {:.0}  (best-first / threshold = {:.3})", sum(&|r| r.drs.1 as f64), sum(&|r| r.thr.1 as f64), sum(&|r| r.ast.1 as f64), sum(&|r| r.ast.1 as f64) / sum(&|r| r.thr.1 as f64)).unwrap();
    writeln!(
        s,
        "total pairs : diff.rs {:.0}  threshold-reimpl {:.0}  best-first {:.0}  (ratio {:.3})",
        sum(&|r| r.drs.2 as f64),
        sum(&|r| r.thr.2 as f64),
        sum(&|r| r.ast.2 as f64),
        sum(&|r| r.ast.2 as f64) / sum(&|r| r.thr.2 as f64)
    )
    .unwrap();
    writeln!(s, "total ms    : diff.rs {:.1}  threshold-reimpl {:.1}  best-first {:.1}  (best-first / diff.rs = {:.3}; / reimpl = {:.3})", sum(&|r| r.drs.0), sum(&|r| r.thr.0), sum(&|r| r.ast.0), sum(&|r| r.ast.0) / sum(&|r| r.drs.0), sum(&|r| r.ast.0) / sum(&|r| r.thr.0)).unwrap();
    let mut rc: Vec<f64> = recs
        .iter()
        .filter(|r| r.thr.1 > 0)
        .map(|r| r.ast.1 as f64 / r.thr.1 as f64)
        .collect();
    let mut rt: Vec<f64> = recs.iter().map(|r| r.ast.0 / r.drs.0.max(1e-9)).collect();
    let mut rp: Vec<f64> = recs
        .iter()
        .filter(|r| r.thr.2 > 0)
        .map(|r| r.ast.2 as f64 / r.thr.2 as f64)
        .collect();
    for (nm, v) in [
        ("cells best-first/threshold", &mut rc),
        ("pairs best-first/threshold", &mut rp),
        ("time best-first/diff.rs", &mut rt),
    ] {
        writeln!(s, "per-fixture ratio {nm}: min {:.3} p10 {:.3} p25 {:.3} median {:.3} p75 {:.3} p90 {:.3} max {:.3}", quant(v, 0.0), quant(v, 0.1), quant(v, 0.25), quant(v, 0.5), quant(v, 0.75), quant(v, 0.9), quant(v, 1.0)).unwrap();
    }
    let cell_wins = recs.iter().filter(|r| r.ast.1 < r.thr.1).count();
    let cell_ties = recs.iter().filter(|r| r.ast.1 == r.thr.1).count();
    let time_wins = recs.iter().filter(|r| r.ast.0 < r.drs.0).count();
    writeln!(s, "best-first fewer cells on {cell_wins} fixtures, equal on {cell_ties}, more on {}; faster on {time_wins} of {done}", done - cell_wins - cell_ties).unwrap();
    writeln!(s, "by fixture size (nodes before+after):").unwrap();
    for (lo, hi) in [
        (0u32, 1000u32),
        (1000, 5000),
        (5000, 20000),
        (20000, u32::MAX),
    ] {
        let sel: Vec<&Rec> = recs
            .iter()
            .filter(|r| r.nodes >= lo && r.nodes < hi)
            .collect();
        if sel.is_empty() {
            continue;
        }
        let f = |g: &dyn Fn(&Rec) -> f64| sel.iter().map(|r| g(r)).sum::<f64>();
        writeln!(
            s,
            "  [{lo},{hi}) n={} cells thr {:.0} ast {:.0} ({:.3}); ms drs {:.1} ast {:.1} ({:.3})",
            sel.len(),
            f(&|r| r.thr.1 as f64),
            f(&|r| r.ast.1 as f64),
            f(&|r| r.ast.1 as f64) / f(&|r| r.thr.1 as f64),
            f(&|r| r.drs.0),
            f(&|r| r.ast.0),
            f(&|r| r.ast.0) / f(&|r| r.drs.0)
        )
        .unwrap();
    }
    writeln!(s, "by distance:").unwrap();
    for (lo, hi) in [(0u32, 10u32), (10, 100), (100, 1000), (1000, u32::MAX)] {
        let sel: Vec<&Rec> = recs
            .iter()
            .filter(|r| r.cost >= lo && r.cost < hi)
            .collect();
        if sel.is_empty() {
            continue;
        }
        let f = |g: &dyn Fn(&Rec) -> f64| sel.iter().map(|r| g(r)).sum::<f64>();
        writeln!(s, "  cost [{lo},{hi}) n={} cells thr {:.0} ast {:.0} ({:.3}); ms drs {:.1} ast {:.1} ({:.3})", sel.len(), f(&|r| r.thr.1 as f64), f(&|r| r.ast.1 as f64), f(&|r| r.ast.1 as f64) / f(&|r| r.thr.1 as f64), f(&|r| r.drs.0), f(&|r| r.ast.0), f(&|r| r.ast.0) / f(&|r| r.drs.0)).unwrap();
    }

    writeln!(
        s,
        "\n== (b) linear space vs stored rows, warm memo, biggest aligns per fixture (nm >= 16) =="
    )
    .unwrap();
    if !mem_rows.is_empty() {
        let n = mem_rows.len();
        let tot = |f: &dyn Fn(&MemRow) -> f64| mem_rows.iter().map(f).sum::<f64>();
        writeln!(s, "samples {n}; sum peak bytes rows {:.0} linear {:.0} (linear/rows {:.3}); sum ms rows {:.2} linear {:.2} (linear/rows {:.2})", tot(&|m| m.4 as f64), tot(&|m| m.5 as f64), tot(&|m| m.5 as f64) / tot(&|m| m.4 as f64), tot(&|m| m.2), tot(&|m| m.3), tot(&|m| m.3) / tot(&|m| m.2)).unwrap();
        let mut ratio: Vec<f64> = mem_rows
            .iter()
            .map(|m| m.5 as f64 / (m.4 as f64).max(1.0))
            .collect();
        writeln!(
            s,
            "per-sample linear/rows bytes: min {:.3} median {:.3} p90 {:.3} max {:.3}",
            quant(&mut ratio, 0.0),
            quant(&mut ratio, 0.5),
            quant(&mut ratio, 0.9),
            quant(&mut ratio, 1.0)
        )
        .unwrap();
        let big = mem_rows.iter().max_by_key(|m| m.0).unwrap();
        writeln!(
            s,
            "largest align nm={} rows peak {} B, linear peak {} B, rows {:.3} ms, linear {:.3} ms",
            big.0, big.4, big.5, big.2, big.3
        )
        .unwrap();
        let mut tr: Vec<f64> = mem_rows.iter().map(|m| m.3 / m.2.max(1e-9)).collect();
        writeln!(
            s,
            "per-sample linear/rows time: min {:.2} median {:.2} p90 {:.2} max {:.2}",
            quant(&mut tr, 0.0),
            quant(&mut tr, 0.5),
            quant(&mut tr, 0.9),
            quant(&mut tr, 1.0)
        )
        .unwrap();
    }

    writeln!(
        s,
        "\n== (c) dispatch by fan-out, per-align cells with warm memo (max(n,m) after strip) =="
    )
    .unwrap();
    writeln!(
        s,
        "{:>6} {:>9} {:>12} {:>12} {:>12} {:>12} {:>12}",
        "fanout", "aligns", "thr/keep", "thr/shorter", "ast/keep", "ast/shorter", "best-of-4"
    )
    .unwrap();
    let mut tot = BucketAgg::default();
    for (i, b) in buckets.iter().enumerate() {
        writeln!(
            s,
            "{:>6} {:>9} {:>12} {:>12} {:>12} {:>12} {:>12}",
            BUCKET_NAMES[i], b.aligns, b.cells[0], b.cells[1], b.cells[2], b.cells[3], b.best
        )
        .unwrap();
        tot.aligns += b.aligns;
        for k in 0..4 {
            tot.cells[k] += b.cells[k];
        }
        tot.best += b.best;
    }
    writeln!(
        s,
        "{:>6} {:>9} {:>12} {:>12} {:>12} {:>12} {:>12}",
        "all", tot.aligns, tot.cells[0], tot.cells[1], tot.cells[2], tot.cells[3], tot.best
    )
    .unwrap();
    writeln!(s, "(thr counts cells filled over all rounds; ast counts cells closed; units are both 'grid cells evaluated' but not the same work per cell)").unwrap();
    writeln!(
        s,
        "\n== (c) end-to-end policies, cold memo, symmetric keys, totals over fixtures =="
    )
    .unwrap();
    let mut names: Vec<_> = e2e.keys().cloned().collect();
    names.sort();
    for n in names {
        let (ms, c, p) = e2e[&n];
        writeln!(s, "{n:>16}: ms {ms:9.1}  cells {c:12}  pairs {p:10}").unwrap();
    }
    print!("{s}");
    std::fs::write(out.join("summary.txt"), &s).unwrap();
    let mut bf = std::fs::File::create(out.join("aligns_by_bucket.csv")).unwrap();
    writeln!(
        bf,
        "fanout,aligns,thr_keep,thr_shorter,ast_keep,ast_shorter,best_of_4"
    )
    .unwrap();
    for (i, b) in buckets.iter().enumerate() {
        writeln!(
            bf,
            "{},{},{},{},{},{},{}",
            BUCKET_NAMES[i], b.aligns, b.cells[0], b.cells[1], b.cells[2], b.cells[3], b.best
        )
        .unwrap();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(move || run(args))
        .unwrap()
        .join()
        .unwrap();
}
