//! Benchmark for `difffold::levenshtein`: the full DP oracle, the rolling band, the bit-parallel kernel
//! and the dispatcher, on synthetic sequences and on label sequences of real Rust ASTs.
//!
//! usage:
//!   taskset -c 0 lev_bench synthetic [quick]
//!   taskset -c 0 lev_bench app <dir>
//!
//! `app` reads pairs `NAME.a.rs` and `NAME.b.rs` from `<dir>`, parses both with tree-sitter-rust, and
//! uses preorder and postorder kind ids as token sequences. Every timed result is checked against the
//! exact distance before timing, so a wrong kernel fails the run instead of looking fast.
//!
//! Output is CSV on stdout. Diagnostics go to stderr.

use std::hint::black_box;
use std::time::Instant;

use difffold::levenshtein::{
    levenshtein, levenshtein_full_dp, levenshtein_within, levenshtein_within_band,
    levenshtein_within_myers_multi, levenshtein_within_u32,
};
use difffold::ted::{ted, PostTree};
use tree_sitter::{Node, Parser};

const LIMITS: [u32; 6] = [1, 2, 4, 8, 32, 128];
const REPS: usize = 7;

#[derive(Clone, Copy)]
enum Imp {
    Oracle,
    Band,
    BitParallel,
    Dispatch,
    U32,
}

impl Imp {
    const ALL: [Imp; 5] = [
        Imp::Oracle,
        Imp::Band,
        Imp::BitParallel,
        Imp::Dispatch,
        Imp::U32,
    ];

    fn name(self) -> &'static str {
        match self {
            Imp::Oracle => "full_dp",
            Imp::Band => "band",
            Imp::BitParallel => "bitparallel",
            Imp::Dispatch => "dispatch",
            Imp::U32 => "u32_path",
        }
    }

    /// The bounded answer. The oracle ignores the limit and pays the full quadratic cost.
    fn run(self, a: &[u32], b: &[u32], k: u32) -> Option<u32> {
        match self {
            Imp::Oracle => {
                let d = u32::try_from(levenshtein_full_dp(a, b)).expect("bench distances fit u32");
                (d <= k).then_some(d)
            }
            Imp::Band => levenshtein_within_band(a, b, k),
            Imp::BitParallel => levenshtein_within_myers_multi(a, b, k),
            Imp::Dispatch => levenshtein_within(a, b, k),
            Imp::U32 => levenshtein_within_u32(a, b, k),
        }
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Alphabet kinds: a dense range of the given size, or sparse random `u32` ids (`0`).
fn token(rng: &mut Rng, alpha: usize) -> u32 {
    if alpha == 0 {
        rng.next() as u32
    } else {
        rng.below(alpha) as u32
    }
}

fn random_seq(rng: &mut Rng, len: usize, alpha: usize) -> Vec<u32> {
    (0..len).map(|_| token(rng, alpha)).collect()
}

fn mutate(rng: &mut Rng, s: &[u32], edits: usize, alpha: usize) -> Vec<u32> {
    let mut t = s.to_vec();
    for _ in 0..edits {
        let fresh = token(rng, alpha);
        match rng.below(3) {
            0 if !t.is_empty() => {
                let i = rng.below(t.len());
                t[i] = fresh;
            }
            1 => {
                let i = rng.below(t.len() + 1);
                t.insert(i, fresh);
            }
            _ if !t.is_empty() => {
                let i = rng.below(t.len());
                t.remove(i);
            }
            _ => t.push(fresh),
        }
    }
    t
}

/// Median-of-`REPS` wall time of one pass over a pair set, after a warmup pass. Returns
/// `(min, median, max)` in milliseconds.
fn time_ms(mut pass: impl FnMut() -> u64) -> (f64, f64, f64) {
    black_box(pass());
    let mut v: Vec<f64> = (0..REPS)
        .map(|_| {
            let t = Instant::now();
            black_box(pass());
            t.elapsed().as_secs_f64() * 1e3
        })
        .collect();
    v.sort_by(|x, y| x.total_cmp(y));
    (v[0], v[REPS / 2], v[REPS - 1])
}

/// One labelled pair set: every pair with its exact distance.
struct Case {
    name: &'static str,
    pairs: Vec<(Vec<u32>, Vec<u32>, u32)>,
}

/// Draws candidate pairs until `pairs_per_case` of them have a distance accepted by `want`.
fn gather(
    out: &mut Vec<Case>,
    rng: &mut Rng,
    pairs_per_case: usize,
    name: &'static str,
    want: impl Fn(u32) -> bool,
    mut make: impl FnMut(&mut Rng) -> (Vec<u32>, Vec<u32>),
) {
    let mut pairs = Vec::new();
    for _ in 0..(pairs_per_case * 200) {
        if pairs.len() == pairs_per_case {
            break;
        }
        let (a, b) = make(rng);
        let d = levenshtein(&a, &b);
        if want(d) {
            pairs.push((a, b, d));
        }
    }
    if !pairs.is_empty() {
        out.push(Case { name, pairs });
    }
}

/// Pair sets for one `(length, alphabet, limit)` cell. Labels are exact distances from the
/// levenshtein dispatcher, which the tests validate against the oracle.
fn cases(rng: &mut Rng, len: usize, alpha: usize, k: u32, pairs_per_case: usize) -> Vec<Case> {
    let kk = k as usize;
    let mut out: Vec<Case> = Vec::new();
    let ki = u32::try_from(kk).unwrap_or(u32::MAX);
    gather(
        &mut out,
        rng,
        pairs_per_case,
        "lt",
        |d| d < ki,
        |r| {
            let a = random_seq(r, len, alpha);
            let b = mutate(r, &a, kk / 2, alpha);
            (a, b)
        },
    );
    gather(
        &mut out,
        rng,
        pairs_per_case,
        "eq",
        |d| d == ki,
        |r| {
            let a = random_seq(r, len, alpha);
            let b = mutate(r, &a, kk, alpha);
            (a, b)
        },
    );
    gather(
        &mut out,
        rng,
        pairs_per_case,
        "k1",
        |d| d == ki.saturating_add(1),
        |r| {
            let a = random_seq(r, len, alpha);
            let b = mutate(r, &a, kk + 1, alpha);
            (a, b)
        },
    );
    if len >= 4 * (kk + 2) {
        gather(
            &mut out,
            rng,
            pairs_per_case,
            "far",
            |d| d > ki.saturating_mul(4),
            |r| (random_seq(r, len, alpha), random_seq(r, len, alpha)),
        );
    }
    gather(
        &mut out,
        rng,
        pairs_per_case,
        "affix",
        |d| d <= ki,
        |r| {
            // A long equal prefix and suffix hiding a small middle that differs by at most `k`.
            let half = len / 2;
            let x = random_seq(r, half, alpha);
            let y = random_seq(r, len - half, alpha);
            let mid = random_seq(r, 4, alpha);
            let edits = 1 + r.below(3);
            let mid2 = mutate(r, &mid, edits, alpha);
            let mut a = x.clone();
            a.extend(&mid);
            a.extend(&y);
            let mut b = x;
            b.extend(&mid2);
            b.extend(&y);
            (a, b)
        },
    );
    out
}

fn expected(d: u32, k: u32) -> Option<u32> {
    (d <= k).then_some(d)
}

/// Asserts every implementation returns the labelled answer for every pair. Runs once, untimed.
fn verify(case: &Case, k: u32) {
    for (a, b, d) in &case.pairs {
        let want = expected(*d, k);
        for imp in Imp::ALL {
            assert_eq!(
                imp.run(a, b, k),
                want,
                "{} disagrees: len={} k={k} d={d}",
                imp.name(),
                a.len()
            );
        }
    }
}

fn synthetic(quick: bool) {
    let lengths: &[usize] = if quick {
        &[16, 64, 256]
    } else {
        &[16, 64, 256, 1024, 4096, 20000]
    };
    let alphas: [(usize, &str); 4] = [(2, "2"), (4, "4"), (256, "256"), (0, "sparse_u32")];
    println!("section,len,alphabet,k,case,impl,pairs,min_ms,median_ms,max_ms,ns_per_pair");
    let mut rng = Rng(0x00C0_FFEE_0000_0001);
    for &len in lengths {
        for &(alpha, aname) in &alphas {
            let pairs_per_case = if len <= 1024 {
                8
            } else if len <= 4096 {
                4
            } else {
                2
            };
            // The oracle does not depend on the limit, so its cost is measured once per workload.
            let base = cases(&mut rng, len, alpha, 8, pairs_per_case);
            if let Some(c) = base.first() {
                let n = c.pairs.len();
                let (mn, md, mx) = time_ms(|| {
                    c.pairs
                        .iter()
                        .map(|(a, b, _)| levenshtein_full_dp(a, b) as u64)
                        .sum()
                });
                println!(
                    "oracle,{len},{aname},any,{},full_dp,{n},{mn:.4},{md:.4},{mx:.4},{:.0}",
                    c.name,
                    md * 1e6 / n as f64
                );
            }
            for &k in &LIMITS {
                for case in cases(&mut rng, len, alpha, k, pairs_per_case) {
                    verify(&case, k);
                    for imp in Imp::ALL {
                        if matches!(imp, Imp::Oracle) {
                            continue;
                        }
                        let n = case.pairs.len();
                        let (mn, md, mx) = time_ms(|| {
                            case.pairs
                                .iter()
                                .map(|(a, b, _)| imp.run(a, b, k).map_or(0, u64::from) + 1)
                                .sum()
                        });
                        println!(
                            "synthetic,{len},{aname},{k},{},{},{n},{mn:.4},{md:.4},{mx:.4},{:.0}",
                            case.name,
                            imp.name(),
                            md * 1e6 / n as f64
                        );
                    }
                }
            }
        }
    }
}

/// Preorder and postorder kind ids of a tree-sitter tree, with the tree in postorder for TED.
fn sequences(node: Node, pre: &mut Vec<u32>) {
    pre.push(u32::from(node.kind_id()));
    for i in 0..node.child_count() {
        if let Some(c) = node.child(i) {
            sequences(c, pre);
        }
    }
}

fn postorder(node: Node, label: &mut Vec<u32>, kids: &mut Vec<Vec<u32>>) -> u32 {
    let mut ks = Vec::with_capacity(node.child_count());
    for i in 0..node.child_count() {
        if let Some(c) = node.child(i) {
            ks.push(postorder(c, label, kids));
        }
    }
    label.push(u32::from(node.kind_id()));
    kids.push(ks);
    u32::try_from(label.len() - 1).expect("tree sizes fit u32")
}

fn parse_rust(
    parser: &mut Parser,
    path: &std::path::Path,
) -> Option<(Vec<u32>, Vec<u32>, PostTree)> {
    let src = std::fs::read(path).ok()?;
    let tree = parser.parse(&src, None)?;
    let root = tree.root_node();
    let mut pre = Vec::new();
    sequences(root, &mut pre);
    let (mut label, mut kids) = (Vec::new(), Vec::new());
    postorder(root, &mut label, &mut kids);
    let post: Vec<u32> = label.clone();
    Some((pre, post, PostTree::from_kids(label, &kids)))
}

fn app(dir: &std::path::Path) {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_rust::LANGUAGE.into())
        .expect("rust grammar loads");
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("app directory is readable")
        .filter_map(|e| e.ok()?.file_name().into_string().ok())
        .filter_map(|n| n.strip_suffix(".a.rs").map(str::to_owned))
        .collect();
    names.sort();
    let mut ted_checked = 0usize;
    let mut ted_violations = 0usize;
    let mut seqs: Vec<(String, Vec<u32>, Vec<u32>)> = Vec::new();
    for name in &names {
        let pa = dir.join(format!("{name}.a.rs"));
        let pb = dir.join(format!("{name}.b.rs"));
        let (Some((pre_a, post_a, ta)), Some((pre_b, post_b, tb))) =
            (parse_rust(&mut parser, &pa), parse_rust(&mut parser, &pb))
        else {
            eprintln!("skipped {name}: parse failed");
            continue;
        };
        // Preorder and postorder Levenshtein are lower bounds of unit-cost tree edit distance,
        // checked here on the real trees for trees small enough for the exact TED.
        if ta.len() <= 1500 && tb.len() <= 1500 {
            let d = ted(&ta, &tb);
            ted_checked += 1;
            let lp = levenshtein(&pre_a, &pre_b);
            let lq = levenshtein(&post_a, &post_b);
            if lp > d || lq > d {
                ted_violations += 1;
                eprintln!("bound violated for {name}: pre={lp} post={lq} ted={d}");
            }
        }
        seqs.push((format!("{name}.pre"), pre_a.clone(), pre_b.clone()));
        seqs.push((format!("{name}.post"), post_a, post_b));
    }
    eprintln!(
        "pairs={} sequences={} ted_checked={ted_checked} ted_bound_violations={ted_violations}",
        names.len(),
        seqs.len()
    );
    println!("section,len,alphabet,k,case,impl,pairs,min_ms,median_ms,max_ms,ns_per_pair");
    for &k in &LIMITS {
        // Real pairs: labels are the exact distances. Only pairs with a nonempty side and sequences
        // up to 20000 tokens are kept, so the oracle stays affordable.
        let mut pairs = Vec::new();
        for (_, a, b) in &seqs {
            if a.len() > 20000 || b.len() > 20000 {
                continue;
            }
            let d = levenshtein(a, b);
            pairs.push((a.clone(), b.clone(), d));
        }
        let len = pairs.iter().map(|p| p.0.len()).max().unwrap_or(0);
        let case = Case { name: "app", pairs };
        verify(&case, k);
        for imp in Imp::ALL {
            if matches!(imp, Imp::Oracle) {
                continue;
            }
            let n = case.pairs.len();
            let (mn, md, mx) = time_ms(|| {
                case.pairs
                    .iter()
                    .map(|(a, b, _)| imp.run(a, b, k).map_or(0, u64::from) + 1)
                    .sum()
            });
            println!(
                "app,{len},rust_kinds,{k},app,{},{n},{mn:.4},{md:.4},{mx:.4},{:.0}",
                imp.name(),
                md * 1e6 / n as f64
            );
        }
    }
}

fn cpu_model() -> String {
    std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("model name"))
                .map(|l| l.split(':').nth(1).unwrap_or("").trim().to_owned())
        })
        .unwrap_or_else(|| "unknown".to_owned())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    eprintln!("cpu: {}", cpu_model());
    match args.get(1).map(String::as_str) {
        Some("synthetic") => synthetic(args.get(2).is_some_and(|s| s == "quick")),
        Some("app") => app(std::path::Path::new(
            args.get(2).expect("usage: lev_bench app <dir>"),
        )),
        _ => eprintln!("usage: lev_bench synthetic [quick] | lev_bench app <dir>"),
    }
}
