//! Same-objective ablation ladder on parsed fixtures.
//!
//! usage: ablate <diffs-dir> <omnidiff-baseline.csv> <out.csv> [limit] [reps] [full-cap]
//!
//! Every config computes the SAME distance (asserted). What varies is only how much work it takes:
//! structural equality, id equality, memoisation, threshold pruning, and the threshold schedule.
//! Fixtures are taken slowest-first by OmniDiff's recorded time; configs run in a per-fixture
//! shuffled order. Full-DP configs are skipped above `full-cap` combined nodes.

use difffold::{apply, diff_with, distance_with, Arena, Config, Id, Tau0};
use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use tree_sitter::{Language, Node, Parser};

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
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        CUR.fetch_sub(l.size(), Ordering::Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

fn reset_peak() {
    PEAK.store(CUR.load(Ordering::Relaxed), Ordering::Relaxed);
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

fn run(args: Vec<String>) {
    let (dir, base, out) = (PathBuf::from(&args[1]), &args[2], &args[3]);
    let limit: usize = args
        .get(4)
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);
    let reps: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(3);
    let full_cap: u32 = args.get(6).and_then(|s| s.parse().ok()).unwrap_or(3000);
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

    let configs: Vec<(&str, Config)> = vec![
        ("full_structural", Config::FULL_STRUCTURAL),
        ("full_interned", Config::FULL_INTERNED),
        ("full_memo", Config::FULL_MEMO),
        ("threshold_bound_x2", Config::PRODUCTION),
        (
            "threshold_one_x2",
            Config {
                tau0: Tau0::One,
                ..Config::PRODUCTION
            },
        ),
        (
            "threshold_bound_x4",
            Config {
                growth: 4,
                ..Config::PRODUCTION
            },
        ),
        (
            "threshold_bound_x2_nomemo",
            Config {
                memo: false,
                ..Config::PRODUCTION
            },
        ),
    ];

    let mut f = std::fs::File::create(out).unwrap();
    writeln!(f, "language,fixture,nodes_before,nodes_after,unique_nodes,config,mode,time_ms,cost,aligns,rounds,max_rounds,first_round,memo_hits,memo_misses,pairs,cells,kept,pruned,peak_bytes,intern_ms,replay_ms").unwrap();
    let mut done = 0;
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
        let t_int = Instant::now();
        let (x, y) = (
            convert(tb.root_node(), &bs, &mut arena, &mut it),
            convert(ta.root_node(), &as_, &mut arena, &mut it),
        );
        let intern_ms = t_int.elapsed().as_secs_f64() * 1e3;
        let (nb, na) = (arena.size(x), arena.size(y));
        // Deterministic per-fixture shuffle of the config order.
        let mut order: Vec<usize> = (0..configs.len()).collect();
        let mut seed = (done as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        for i in (1..order.len()).rev() {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            order.swap(i, (seed % (i as u64 + 1)) as usize);
        }
        let mut reference: Option<u32> = None;
        for &ci in &order {
            let (name, cfg) = configs[ci];
            let full = !cfg.threshold;
            if full && nb + na > full_cap {
                continue;
            }
            let n_reps = if full { 1 } else { reps };
            // Distance only.
            let mut ts = Vec::new();
            let mut last = None;
            for _ in 0..n_reps {
                reset_peak();
                let t = Instant::now();
                let res = distance_with(&arena, cfg, x, y);
                ts.push(t.elapsed().as_secs_f64() * 1e3);
                last = Some((res, PEAK.load(Ordering::Relaxed)));
            }
            let ((cost, s), peak) = last.unwrap();
            if let Some(rc) = reference {
                assert_eq!(rc, cost, "configs disagree on {name}");
            }
            reference = Some(cost);
            let ms = median(&mut ts);
            writeln!(f, "{},{},{nb},{na},{},{name},distance,{ms:.3},{cost},{},{},{},{},{},{},{},{},{},{},{peak},{intern_ms:.3},", r[0], r[4], arena.len(), s.aligns, s.rounds, s.max_rounds, s.first_round, s.memo_hits, s.memo_misses, s.pairs, s.cells, s.kept, s.pruned).unwrap();
            // Script, then production-path replay validation.
            let mut ts = Vec::new();
            let mut res = None;
            for _ in 0..n_reps {
                let t = Instant::now();
                let r2 = diff_with(&arena, cfg, x, y);
                ts.push(t.elapsed().as_secs_f64() * 1e3);
                res = Some(r2);
            }
            let r2 = res.unwrap();
            assert_eq!(r2.cost, cost);
            let t = Instant::now();
            let rebuilt = apply(&mut arena, x, &r2.edit).expect("replay");
            let replay_ms = t.elapsed().as_secs_f64() * 1e3;
            assert_eq!(rebuilt, y, "replay must rebuild the after-tree");
            writeln!(f, "{},{},{nb},{na},{},{name},script,{:.3},{cost},{},{},{},{},{},{},{},{},{},{},0,{intern_ms:.3},{replay_ms:.3}", r[0], r[4], arena.len(), median(&mut ts), r2.stats.aligns, r2.stats.rounds, r2.stats.max_rounds, r2.stats.first_round, r2.stats.memo_hits, r2.stats.memo_misses, r2.stats.pairs, r2.stats.cells, r2.stats.kept, r2.stats.pruned).unwrap();
        }
        done += 1;
    }
    eprintln!("measured {done} fixtures");
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
