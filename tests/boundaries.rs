//! Tests aimed at the places pruning could fail: threshold boundaries, bound admissibility,
//! exhaustive small shapes, a constant bucket function, and the ablation configs.

use difffold::diff::{align_within, remaining_bound};
use difffold::{diff_checked, diff_with, Arena, Config, Id, Tau0};

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

#[derive(Clone, PartialEq, Eq, Debug)]
struct Plain(u32, Vec<Plain>);

fn build(a: &mut Arena, p: &Plain) -> Id {
    let k: Vec<Id> = p.1.iter().map(|c| build(a, c)).collect();
    a.mk(p.0, &k)
}

fn gen(r: &mut Rng, depth: u32, labels: u64) -> Plain {
    let n = if depth == 0 { 0 } else { r.below(4) as usize };
    Plain(r.below(labels) as u32, (0..n).map(|_| gen(r, depth - 1, labels)).collect())
}

/// Every ordered labelled tree with exactly `n` nodes over `labels` labels.
fn all_trees(n: usize, labels: u32) -> Vec<Plain> {
    if n == 0 {
        return vec![];
    }
    let mut out = Vec::new();
    for l in 0..labels {
        for forest in all_forests(n - 1, labels) {
            out.push(Plain(l, forest));
        }
    }
    out
}

/// Every ordered forest with exactly `n` nodes in total.
fn all_forests(n: usize, labels: u32) -> Vec<Vec<Plain>> {
    if n == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for first in 1..=n {
        for t in all_trees(first, labels) {
            for rest in all_forests(n - first, labels) {
                let mut f = vec![t.clone()];
                f.extend(rest);
                out.push(f);
            }
        }
    }
    out
}

fn oracle_tree(a: &Arena, x: Id, y: Id) -> u32 {
    u32::from(a.label(x) != a.label(y)) + oracle_list(a, a.kids(x), a.kids(y))
}

fn oracle_list(a: &Arena, ka: &[Id], kb: &[Id]) -> u32 {
    let (n, m) = (ka.len(), kb.len());
    let mut d = vec![vec![0u32; m + 1]; n + 1];
    for i in 1..=n {
        d[i][0] = d[i - 1][0] + a.size(ka[i - 1]);
    }
    for j in 1..=m {
        d[0][j] = d[0][j - 1] + a.size(kb[j - 1]);
    }
    for i in 1..=n {
        for j in 1..=m {
            let del = d[i - 1][j] + a.size(ka[i - 1]);
            let ins = d[i][j - 1] + a.size(kb[j - 1]);
            let sub = d[i - 1][j - 1] + oracle_tree(a, ka[i - 1], kb[j - 1]);
            d[i][j] = del.min(ins).min(sub);
        }
    }
    d[n][m]
}

/// True minimum remaining cost `R*(i, j)` of aligning `ka[i..]` with `kb[j..]`.
fn oracle_remaining(a: &Arena, ka: &[Id], kb: &[Id]) -> Vec<Vec<u32>> {
    let (n, m) = (ka.len(), kb.len());
    let mut r = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        r[i][m] = r[i + 1][m] + a.size(ka[i]);
    }
    for j in (0..m).rev() {
        r[n][j] = r[n][j + 1] + a.size(kb[j]);
    }
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            let del = r[i + 1][j] + a.size(ka[i]);
            let ins = r[i][j + 1] + a.size(kb[j]);
            let sub = r[i + 1][j + 1] + oracle_tree(a, ka[i], kb[j]);
            r[i][j] = del.min(ins).min(sub);
        }
    }
    r
}

fn lists(r: &mut Rng, arena: &mut Arena, labels: u64, depth: u32, max_len: u64) -> (Vec<Id>, Vec<Id>) {
    let mk = |r: &mut Rng, arena: &mut Arena| -> Vec<Id> {
        (0..r.below(max_len + 1)).map(|_| { let p = gen(r, depth, labels); build(arena, &p) }).collect()
    };
    (mk(r, arena), mk(r, arena))
}

#[test]
fn threshold_below_at_and_above_the_optimum() {
    let mut r = Rng(0xC0FF_EE11);
    let mut arena = Arena::new();
    let mut checked = 0;
    for _ in 0..1500 {
        let (a, b) = lists(&mut r, &mut arena, 2, 2, 7);
        let d = oracle_list(&arena, &a, &b);
        if d > 0 {
            assert_eq!(align_within(&arena, &a, &b, d - 1), None, "tau < d must refuse, d = {d}");
        }
        for extra in [0u32, 1, 3, 40] {
            assert_eq!(align_within(&arena, &a, &b, d + extra), Some(d), "tau = d + {extra} must return the exact optimum");
        }
        checked += 1;
    }
    assert!(checked > 0);
}

#[test]
fn bound_never_exceeds_true_remaining_cost() {
    let mut r = Rng(0xB0_0B);
    let mut arena = Arena::new();
    for _ in 0..600 {
        let (a, b) = lists(&mut r, &mut arena, 3, 2, 6);
        let rem = oracle_remaining(&arena, &a, &b);
        for i in 0..=a.len() {
            for j in 0..=b.len() {
                let h = remaining_bound(&arena, &a, &b, i, j);
                assert!(h <= rem[i][j], "h({i},{j}) = {h} exceeds true remaining cost {}", rem[i][j]);
            }
        }
    }
}

#[test]
fn exhaustive_small_shapes_all_pairs() {
    // Every ordered tree with at most 5 nodes over 2 labels, every pair, every config.
    let mut shapes: Vec<Plain> = Vec::new();
    for n in 1..=5 {
        shapes.extend(all_trees(n, 2));
    }
    let mut arena = Arena::new();
    let ids: Vec<Id> = shapes.iter().map(|p| build(&mut arena, p)).collect();
    let mut pairs = 0u64;
    for &x in &ids {
        for &y in &ids {
            let want = oracle_tree(&arena, x, y);
            let got = diff_checked(&mut arena, x, y);
            assert_eq!(got.cost, want);
            for cfg in [Config::FULL_STRUCTURAL, Config::FULL_INTERNED, Config::FULL_MEMO] {
                assert_eq!(diff_with(&arena, cfg, x, y).cost, want, "config {cfg:?}");
            }
            pairs += 1;
        }
    }
    assert!(pairs > 100_000, "enumeration too small: {pairs}");
}

#[test]
fn constant_bucket_function_keeps_identity_and_distance_exact() {
    fn constant(_: u32, _: &[Id]) -> u64 {
        7
    }
    let mut r = Rng(0xFEED);
    let mut arena = Arena::with_fold(constant);
    let mut seen: Vec<(Plain, Id)> = Vec::new();
    for _ in 0..1200 {
        let p = gen(&mut r, 3, 3);
        let id = build(&mut arena, &p);
        match seen.iter().find(|(q, _)| *q == p) {
            Some((_, old)) => assert_eq!(*old, id, "equal trees must share an id"),
            None => {
                assert!(seen.iter().all(|(_, o)| *o != id), "different trees must not share an id");
                seen.push((p, id));
            }
        }
    }
    for _ in 0..300 {
        let (x, y) = (seen[r.below(seen.len() as u64) as usize].1, seen[r.below(seen.len() as u64) as usize].1);
        assert_eq!(diff_checked(&mut arena, x, y).cost, oracle_tree(&arena, x, y));
    }
}

#[test]
fn schedules_and_configs_agree_on_distance() {
    let mut r = Rng(0x5EED);
    let mut arena = Arena::new();
    let schedules = [
        Config::PRODUCTION,
        Config { tau0: Tau0::One, ..Config::PRODUCTION },
        Config { growth: 4, ..Config::PRODUCTION },
        Config { growth: 8, tau0: Tau0::One, ..Config::PRODUCTION },
        Config { memo: false, ..Config::PRODUCTION },
        Config::FULL_STRUCTURAL,
        Config::FULL_INTERNED,
        Config::FULL_MEMO,
    ];
    for _ in 0..400 {
        let (a, b) = (gen(&mut r, 4, 3), gen(&mut r, 4, 3));
        let (x, y) = (build(&mut arena, &a), build(&mut arena, &b));
        let want = oracle_tree(&arena, x, y);
        for cfg in schedules {
            assert_eq!(diff_with(&arena, cfg, x, y).cost, want, "config {cfg:?}");
        }
    }
}

#[test]
fn identical_subtrees_share_an_id_but_scripts_keep_occurrences_apart() {
    let mut arena = Arena::new();
    let leaf = arena.mk(1, &[]);
    let c = arena.mk(2, &[leaf]);
    let x = arena.mk(0, &[c, c, c]);
    let y = arena.mk(0, &[c, c]);
    let d = diff_checked(&mut arena, x, y);
    assert_eq!(d.cost, arena.size(c), "dropping one of three identical children costs one child");
}
