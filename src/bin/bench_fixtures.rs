//! Times `difffold` on OmniDiff's fixture corpus, next to OmniDiff's own recorded time.
//!
//! usage: bench_fixtures <diffs-dir> <omnidiff-baseline.csv> <out.csv> [limit] [reps]
//!
//! The baseline CSV is `benchmark_diff_pairs --fixtures` output. Rows are taken slowest first.
//! Parsing is timed separately and excluded from `diff_ms`. The distance objective differs from
//! OmniDiff's (top-down, unit cost), so `cost` is not comparable to OmniDiff's mapping; accuracy
//! is not scored here.

use difffold::{diff_checked, Arena, Id};
use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::time::Instant;
use tree_sitter::{Language, Node, Parser};

struct Interner {
    labels: HashMap<(u16, Option<Vec<u8>>), u32>,
}

impl Interner {
    fn label(&mut self, kind: u16, text: Option<&[u8]>) -> u32 {
        let next = u32::try_from(self.labels.len()).unwrap();
        *self.labels.entry((kind, text.map(<[u8]>::to_vec))).or_insert(next)
    }
}

fn convert(n: Node, src: &[u8], arena: &mut Arena, it: &mut Interner) -> Id {
    if n.child_count() == 0 {
        let l = it.label(n.kind_id(), Some(&src[n.byte_range()]));
        return arena.mk(l, &[]);
    }
    let mut kids = Vec::with_capacity(n.child_count());
    let mut c = n.walk();
    for ch in n.children(&mut c) {
        kids.push(convert(ch, src, arena, it));
    }
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
    std::fs::read_dir(dir).ok()?.flatten().map(|e| e.path()).find(|p| {
        p.file_name().and_then(|f| f.to_str()).is_some_and(|f| f.starts_with(stem))
    })
}

fn run(args: Vec<String>) {
    let (dir, base, out) = (PathBuf::from(&args[1]), &args[2], &args[3]);
    let limit: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(usize::MAX);
    let reps: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(3);
    let text = std::fs::read_to_string(base).unwrap();
    let mut rows: Vec<Vec<String>> = text.lines().skip(1).map(|l| l.split(',').map(str::to_string).collect()).collect();
    rows.retain(|r| r.len() > 10 && r[9] == "ok");
    rows.sort_by(|a, b| b[10].parse::<f64>().unwrap().total_cmp(&a[10].parse::<f64>().unwrap()));
    let mut f = std::fs::File::create(out).unwrap();
    writeln!(f, "language,fixture,omni_nodes,omni_ms,nodes_before,nodes_after,parse_ms,intern_ms,diff_ms,cost,pairs,cells,first_round,widenings,pruned").unwrap();
    let mut done = 0;
    for r in rows {
        if done >= limit {
            break;
        }
        let d = dir.join(&r[2]).join(&r[4]);
        let (Some(bp), Some(ap)) = (find(&d, "before."), find(&d, "after.")) else { continue };
        let ext = bp.file_name().unwrap().to_str().unwrap().split('.').nth(1).unwrap_or("");
        let Some(l) = lang(ext) else { continue };
        let (bs, as_) = (std::fs::read(&bp).unwrap(), std::fs::read(&ap).unwrap());
        let mut parser = Parser::new();
        parser.set_language(&l).unwrap();
        let t0 = Instant::now();
        let (tb, ta) = (parser.parse(&bs, None).unwrap(), parser.parse(&as_, None).unwrap());
        let parse_ms = t0.elapsed().as_secs_f64() * 1e3;
        let mut intern_samples = Vec::new();
        let mut keep = None;
        for _ in 0..reps {
            let mut arena = Arena::new();
            let mut it = Interner { labels: HashMap::new() };
            let t1 = Instant::now();
            let ids = (convert(tb.root_node(), &bs, &mut arena, &mut it), convert(ta.root_node(), &as_, &mut arena, &mut it));
            intern_samples.push(t1.elapsed().as_secs_f64() * 1e3);
            keep = Some((arena, ids));
        }
        intern_samples.sort_by(f64::total_cmp);
        let intern_ms = intern_samples[intern_samples.len() / 2];
        let (mut arena, (x, y)) = keep.unwrap();
        let (nb, na) = (arena.size(x), arena.size(y));
        let mut times = Vec::new();
        let mut last = None;
        for _ in 0..reps {
            let t = Instant::now();
            let res = difffold::diff(&arena, x, y);
            times.push(t.elapsed().as_secs_f64() * 1e3);
            last = Some(res);
        }
        times.sort_by(f64::total_cmp);
        // Enforce C3 once per fixture, outside the timed region.
        let checked = diff_checked(&mut arena, x, y);
        let res = last.unwrap();
        assert_eq!(checked.cost, res.cost);
        let s = res.stats;
        writeln!(
            f,
            "{},{},{},{},{},{},{:.3},{:.3},{:.3},{},{},{},{},{},{}",
            r[0], r[4], r[7].parse::<u64>().unwrap() + r[8].parse::<u64>().unwrap(), r[10], nb, na, parse_ms, intern_ms,
            times[times.len() / 2], res.cost, s.pairs, s.cells, s.first_round, s.widenings, s.pruned
        )
        .unwrap();
        done += 1;
    }
    eprintln!("measured {done} fixtures");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    std::thread::Builder::new().stack_size(512 << 20).spawn(move || run(args)).unwrap().join().unwrap();
}
