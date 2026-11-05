//! Similarity-search benchmark of the threshold filter in `difffold::tedfilter`.
//!
//! usage: `cargo run --release --example ted_filter_bench [--features ts]`
//!
//! Each workload is one query tree against N candidates. Three methods answer "is TED(query, candidate)
//! at most tau, and if so, what is it?" for every candidate:
//!
//! * `A`: the full exact distance [`ted`] for every candidate, then a comparison with tau. No threshold
//!   search and no filter. Its time does not depend on tau.
//! * `B`: [`ted_within`], the exact solver's own threshold search, with no filter.
//! * `F`: [`within_stats`], the filter pipeline, then [`ted_within`] on the survivors.
//!
//! The three result sets are asserted identical. Times are medians over 5 timed runs, after one warm-up
//! run. Per-stage counts come from the same runs and do not vary between them.
//!
//! The synthetic workload mutates a random query at known edit counts and adds unrelated trees. The real
//! workload (with `--features ts`) takes function subtrees of this crate's own Rust sources, parsed with
//! tree-sitter, and uses each of a few functions as a query against all the others.

use difffold::ted::{ted, ted_within, PostTree};
use difffold::tedfilter::{within_stats, FilterStats};
use std::time::Instant;

const RUNS: usize = 5;

#[derive(Clone, Debug)]
struct T {
    label: u32,
    kind: u32,
    kids: Vec<T>,
}

fn node(label: u32, kind: u32, kids: Vec<T>) -> T {
    T { label, kind, kids }
}

fn size(t: &T) -> usize {
    1 + t.kids.iter().map(size).sum::<usize>()
}

fn post(t: &T) -> PostTree {
    fn go(t: &T, label: &mut Vec<u32>, kind: &mut Vec<u32>, kids: &mut Vec<Vec<u32>>) -> u32 {
        let ks: Vec<u32> = t.kids.iter().map(|c| go(c, label, kind, kids)).collect();
        label.push(t.label);
        kind.push(t.kind);
        kids.push(ks);
        label.len() as u32 - 1
    }
    let (mut l, mut k, mut kids) = (Vec::new(), Vec::new(), Vec::new());
    go(t, &mut l, &mut k, &mut kids);
    PostTree::from_kids(l, &kids).with_kinds(k)
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random tree with about `target` nodes.
fn random_tree(r: &mut Rng, budget: &mut i64, labels: u64, kinds: u64) -> T {
    *budget -= 1;
    let label = r.below(labels) as u32;
    let kind = r.below(kinds) as u32;
    let mut kids = Vec::new();
    while *budget > 0 && r.below(3) != 0 {
        kids.push(random_tree(r, budget, labels, kinds));
    }
    node(label, kind, kids)
}

/// A random tree with between `lo` and `hi` nodes, by resampling.
fn sized_tree(r: &mut Rng, lo: usize, hi: i64, labels: u64, kinds: u64) -> T {
    loop {
        let mut budget = hi;
        let t = random_tree(r, &mut budget, labels, kinds);
        if size(&t) >= lo {
            return t;
        }
    }
}

fn nth_mut<'a>(t: &'a mut T, idx: &mut usize) -> Option<&'a mut T> {
    if *idx == 0 {
        return Some(t);
    }
    *idx -= 1;
    for k in &mut t.kids {
        if let Some(x) = nth_mut(k, idx) {
            return Some(x);
        }
    }
    None
}

/// Delete the node at preorder position `idx + 1` (the root is never deleted). Its children take its place.
fn delete_rec(t: &mut T, idx: &mut usize) -> bool {
    let mut j = 0;
    while j < t.kids.len() {
        if *idx == 0 {
            let removed = t.kids.remove(j);
            for (off, c) in removed.kids.into_iter().enumerate() {
                t.kids.insert(j + off, c);
            }
            return true;
        }
        *idx -= 1;
        if delete_rec(&mut t.kids[j], idx) {
            return true;
        }
        j += 1;
    }
    false
}

/// `ops` random edits: relabels (about half), deletions and wraps of a run of children.
fn mutate(r: &mut Rng, t: &mut T, ops: usize, labels: u64, kinds: u64) {
    for _ in 0..ops {
        let n = size(t) as u64;
        match r.below(4) {
            0 | 1 => {
                let mut idx = r.below(n) as usize;
                let x = nth_mut(t, &mut idx).expect("index in range");
                x.label = r.below(labels) as u32;
                if r.below(3) == 0 {
                    x.kind = r.below(kinds) as u32;
                }
            }
            2 => {
                if n > 1 {
                    let mut idx = r.below(n - 1) as usize;
                    delete_rec(t, &mut idx);
                }
            }
            _ => {
                let mut idx = r.below(n) as usize;
                let x = nth_mut(t, &mut idx).expect("index in range");
                if !x.kids.is_empty() {
                    let i = r.below(x.kids.len() as u64) as usize;
                    let j = i + r.below((x.kids.len() - i) as u64) as usize;
                    let run: Vec<T> = x.kids.drain(i..=j).collect();
                    let label = r.below(labels) as u32;
                    x.kids.insert(i, node(label, 0, run));
                }
            }
        }
    }
}

fn synthetic(seed: u64) -> (PostTree, Vec<PostTree>) {
    let mut r = Rng(seed);
    let (labels, kinds) = (24, 3);
    let query = sized_tree(&mut r, 80, 140, labels, kinds);
    let mut cands = Vec::new();
    let edits = [0usize, 1, 2, 4, 8, 16, 32];
    for i in 0..400 {
        if i % 4 == 3 {
            cands.push(post(&sized_tree(&mut r, 40, 140, labels, kinds)));
        } else {
            let mut m = query.clone();
            mutate(&mut r, &mut m, edits[i % edits.len()], labels, kinds);
            cands.push(post(&m));
        }
    }
    (post(&query), cands)
}

#[cfg(feature = "ts")]
mod real {
    use super::T;
    use std::collections::HashMap;
    use std::fs;
    use std::path::{Path, PathBuf};
    use tree_sitter::{Node, Parser};

    fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = fs::read_dir(dir) else { return };
        let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                collect_rs(&p, out);
            } else if p.extension().is_some_and(|e| e == "rs") {
                out.push(p);
            }
        }
    }

    /// The tree of `n` as an arena-free [`T`]: leaves are labelled by kind and text, inner nodes by kind.
    fn convert(n: Node, src: &[u8], labels: &mut HashMap<(u16, Option<Vec<u8>>), u32>) -> T {
        let kids: Vec<T> = {
            let mut c = n.walk();
            n.children(&mut c)
                .map(|ch| convert(ch, src, labels))
                .collect()
        };
        let text = if n.child_count() == 0 {
            Some(src[n.byte_range()].to_vec())
        } else {
            None
        };
        let next = u32::try_from(labels.len()).expect("label count fits in u32");
        let label = *labels.entry((n.kind_id(), text)).or_insert(next);
        T {
            label,
            kind: 0,
            kids,
        }
    }

    /// Function subtrees of this crate's Rust sources, between 40 and 250 nodes.
    pub fn corpus() -> Vec<(String, T)> {
        let root = env!("CARGO_MANIFEST_DIR");
        let mut files = Vec::new();
        collect_rs(&Path::new(root).join("src"), &mut files);
        collect_rs(&Path::new(root).join("tests"), &mut files);
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .expect("rust grammar loads");
        let mut labels = HashMap::new();
        let mut out = Vec::new();
        for f in files {
            let src = fs::read(&f).expect("readable source file");
            let Some(tree) = parser.parse(&src, None) else {
                continue;
            };
            let mut stack = vec![tree.root_node()];
            while let Some(n) = stack.pop() {
                if n.kind() == "function_item" {
                    let t = convert(n, &src, &mut labels);
                    let sz = super::size(&t);
                    if (40..=250).contains(&sz) {
                        out.push((format!("{}:{}", f.display(), n.start_position().row + 1), t));
                    }
                }
                let mut c = n.walk();
                stack.extend(n.children(&mut c));
            }
        }
        out
    }
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).expect("times are finite"));
    v[v.len() / 2]
}

fn ms(nanos: u64) -> f64 {
    nanos as f64 / 1e6
}

struct Workload {
    name: String,
    query: PostTree,
    candidates: Vec<PostTree>,
    taus: Vec<u32>,
}

fn run_workload(w: &Workload) {
    let n = w.candidates.len();
    let exact: Vec<u32> = w.candidates.iter().map(|c| ted(&w.query, c)).collect();
    println!(
        "\n== {} : query {} nodes, {} candidates, exact distances {}..={} (median {})",
        w.name,
        w.query.len(),
        n,
        exact.iter().min().unwrap(),
        exact.iter().max().unwrap(),
        {
            let mut s = exact.clone();
            s.sort_unstable();
            s[n / 2]
        }
    );

    // Time of method A, which is the same for every tau.
    let mut a_times = Vec::new();
    for run in 0..=RUNS {
        let t = Instant::now();
        let mut sink = 0u64;
        for c in &w.candidates {
            sink += u64::from(ted(&w.query, c));
        }
        let el = t.elapsed().as_nanos() as u64;
        std::hint::black_box(sink);
        if run > 0 {
            a_times.push(ms(el));
        }
    }
    let a_med = median(a_times);
    println!("A (full exact TED, then compare): {a_med:.1} ms for all candidates, any tau");

    for &tau in &w.taus {
        let want: Vec<(usize, u32)> = exact
            .iter()
            .enumerate()
            .filter(|&(_, &d)| d <= tau)
            .map(|(i, &d)| (i, d))
            .collect();

        let mut b_times = Vec::new();
        let mut f_times = Vec::new();
        let mut stages: Vec<FilterStats> = Vec::new();
        for run in 0..=RUNS {
            let t = Instant::now();
            let got_b: Vec<(usize, u32)> = w
                .candidates
                .iter()
                .enumerate()
                .filter_map(|(i, c)| ted_within(&w.query, c, tau).map(|d| (i, d)))
                .collect();
            let el_b = t.elapsed().as_nanos() as u64;
            assert_eq!(got_b, want, "B result set differs at tau {tau}");

            let t = Instant::now();
            let mut sum = FilterStats::default();
            let mut got_f = Vec::new();
            for (i, c) in w.candidates.iter().enumerate() {
                let (d, st) = within_stats(&w.query, c, tau);
                sum.add(&st);
                if let Some(d) = d {
                    got_f.push((i, d));
                }
            }
            let el_f = t.elapsed().as_nanos() as u64;
            assert_eq!(
                got_f, want,
                "F result set differs from the exact solver at tau {tau}"
            );
            if run > 0 {
                b_times.push(ms(el_b));
                f_times.push(ms(el_f));
                stages.push(sum);
            }
        }
        let b_med = median(b_times);
        let f_med = median(f_times);
        // Per-stage time medians across the timed runs.
        let stage_ms = |f: fn(&FilterStats) -> u64| -> f64 {
            median(stages.iter().map(|s| ms(f(s))).collect())
        };
        let counts = stages.last().copied().unwrap_or_default();
        println!(
            "tau {tau:>3}: within {:>4}/{n} | B ted_within {b_med:>9.1} ms | F filter+verify {f_med:>9.1} ms | F/B {:.2}x, F/A {:.2}x",
            want.len(),
            f_med / b_med,
            f_med / a_med,
        );
        println!(
            "         stage  entered  rejected  median ms | size {:>4} {:>4} {:>8.3} | labels {:>4} {:>4} {:>8.3} | prep {:>8.3} ms",
            counts.size.entered,
            counts.size.rejected,
            stage_ms(|s| s.size.nanos),
            counts.labels.entered,
            counts.labels.rejected,
            stage_ms(|s| s.labels.nanos),
            stage_ms(|s| s.prep_nanos),
        );
        println!(
            "                 preorder {:>4} {:>4} {:>8.3} | postorder {:>4} {:>4} {:>8.3} | exact {:>4} {:>4} {:>9.1}",
            counts.preorder.entered,
            counts.preorder.rejected,
            stage_ms(|s| s.preorder.nanos),
            counts.postorder.entered,
            counts.postorder.rejected,
            stage_ms(|s| s.postorder.nanos),
            counts.exact.entered,
            counts.exact.rejected,
            stage_ms(|s| s.exact.nanos),
        );
    }
}

fn main() {
    let mut workloads = Vec::new();
    for seed in [0x51u64, 0x77, 0xa3] {
        let (query, candidates) = synthetic(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
        workloads.push(Workload {
            name: format!("synthetic seed {seed:#x}"),
            query,
            candidates,
            taus: vec![1, 2, 4, 8, 16, 32],
        });
    }
    #[cfg(feature = "ts")]
    {
        let corpus = real::corpus();
        println!(
            "real corpus: {} function subtrees from src/ and tests/",
            corpus.len()
        );
        let step = (corpus.len() / 3).max(1);
        for k in (0..corpus.len()).step_by(step).take(3) {
            let (name, qt) = &corpus[k];
            let query = post(qt);
            let candidates: Vec<PostTree> = corpus
                .iter()
                .enumerate()
                .filter(|&(j, _)| j != k)
                .map(|(_, (_, t))| post(t))
                .collect();
            workloads.push(Workload {
                name: format!("real query {name} ({} nodes)", query.len()),
                query,
                candidates,
                taus: vec![1, 2, 4, 8, 16, 32, 64],
            });
        }
    }
    for w in &workloads {
        run_workload(w);
    }
}
