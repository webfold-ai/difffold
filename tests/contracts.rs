//! Executable statements of the contracts in `SPEC.md`, checked against an independent oracle.
//!
//! The oracle shares nothing with the library's aligner: no memo, no strip, no band, no size
//! pruning, plain recursion over the arena's `label`/`kids`.

use difffold::diff::{apply, cost};
use difffold::{diff, diff_checked, Arena, Id};

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

/// A plain tree used as the model for `I1`.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Plain(u32, Vec<Plain>);

fn gen_plain(r: &mut Rng, depth: u32, labels: u64) -> Plain {
    let n = if depth == 0 { 0 } else { r.below(4) as usize };
    Plain(r.below(labels) as u32, (0..n).map(|_| gen_plain(r, depth - 1, labels)).collect())
}

fn build(a: &mut Arena, p: &Plain) -> Id {
    let k: Vec<Id> = p.1.iter().map(|c| build(a, c)).collect();
    a.mk(p.0, &k)
}

/// Copy `p` with random edits: relabel, drop, duplicate, insert a fresh subtree.
fn mutate(r: &mut Rng, p: &Plain, labels: u64) -> Plain {
    let mut kids: Vec<Plain> = p.1.iter().map(|c| if r.below(4) == 0 { mutate(r, c, labels) } else { c.clone() }).collect();
    match r.below(9) {
        0 if !kids.is_empty() => {
            let i = r.below(kids.len() as u64) as usize;
            kids.remove(i);
        }
        1 => {
            let i = r.below(kids.len() as u64 + 1) as usize;
            kids.insert(i, gen_plain(r, 2, labels));
        }
        2 if !kids.is_empty() => {
            let i = r.below(kids.len() as u64) as usize;
            let c = kids[i].clone();
            kids.insert(i, c);
        }
        3 if kids.len() > 1 => {
            let i = r.below(kids.len() as u64 - 1) as usize;
            kids.swap(i, i + 1);
        }
        _ => {}
    }
    let label = if r.below(8) == 0 { r.below(labels) as u32 } else { p.0 };
    Plain(label, kids)
}

/// Independent oracle: plain recursion, full alignment DP, nothing shared with the library.
fn oracle(a: &Arena, x: Id, y: Id) -> u32 {
    let rel = u32::from(a.label(x) != a.label(y));
    let (ka, kb) = (a.kids(x), a.kids(y));
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
            let sub = d[i - 1][j - 1] + oracle(a, ka[i - 1], kb[j - 1]);
            d[i][j] = del.min(ins).min(sub);
        }
    }
    rel + d[n][m]
}

fn model_size(p: &Plain) -> u32 {
    1 + p.1.iter().map(model_size).sum::<u32>()
}

#[test]
fn i1_interning_matches_structural_equality() {
    let mut r = Rng(0x1234_5678_9ABC_DEF1);
    let mut arena = Arena::new();
    let mut items: Vec<(Plain, Id)> = Vec::new();
    for _ in 0..400 {
        let p = gen_plain(&mut r, 3, 3);
        let id = build(&mut arena, &p);
        items.push((p, id));
    }
    for _ in 0..400 {
        let base = items[r.below(items.len() as u64) as usize].0.clone();
        let p = mutate(&mut r, &base, 3);
        let id = build(&mut arena, &p);
        items.push((p, id));
    }
    for (p, id) in &items {
        assert_eq!(arena.size(*id), model_size(p), "size");
    }
    for i in 0..items.len() {
        for j in 0..items.len() {
            assert_eq!(items[i].0 == items[j].0, items[i].1 == items[j].1, "I1 violated");
        }
    }
}

#[test]
fn i1_survives_forced_fold_collisions() {
    // Many nodes over a tiny label set stress bucket chains; I1 must still hold.
    let mut r = Rng(42);
    let mut arena = Arena::new();
    let mut seen: Vec<(Plain, Id)> = Vec::new();
    for _ in 0..3000 {
        let p = gen_plain(&mut r, 4, 2);
        let id = build(&mut arena, &p);
        if let Some((_, old)) = seen.iter().find(|(q, _)| *q == p) {
            assert_eq!(*old, id);
        } else {
            assert!(seen.iter().all(|(_, o)| *o != id), "two different trees share an id");
            seen.push((p, id));
        }
    }
}

#[test]
fn c4_c3_random_pairs_match_oracle_and_replay() {
    let mut r = Rng(0xDEAD_BEEF_0BAD_F00D);
    let mut arena = Arena::new();
    for _ in 0..1500 {
        let a = gen_plain(&mut r, 4, 3);
        let mut b = mutate(&mut r, &a, 3);
        for _ in 0..r.below(4) {
            b = mutate(&mut r, &b, 3);
        }
        let (x, y) = (build(&mut arena, &a), build(&mut arena, &b));
        let want = oracle(&arena, x, y);
        let got = diff_checked(&mut arena, x, y);
        assert_eq!(got.cost, want, "C4: distance differs from oracle");
        assert!(got.cost >= arena.size(x).abs_diff(arena.size(y)), "C7: size lower bound");
        assert_eq!(got.cost == 0, x == y, "C6: zero iff equal");
    }
}

#[test]
fn c4_unrelated_trees_match_oracle() {
    let mut r = Rng(7);
    let mut arena = Arena::new();
    for _ in 0..600 {
        let (a, b) = (gen_plain(&mut r, 4, 4), gen_plain(&mut r, 4, 4));
        let (x, y) = (build(&mut arena, &a), build(&mut arena, &b));
        assert_eq!(diff_checked(&mut arena, x, y).cost, oracle(&arena, x, y));
    }
}

#[test]
fn c5_c8_symmetry_and_triangle() {
    let mut r = Rng(99);
    let mut arena = Arena::new();
    for _ in 0..400 {
        let a = gen_plain(&mut r, 3, 3);
        let b = mutate(&mut r, &a, 3);
        let c = mutate(&mut r, &b, 3);
        let (x, y, z) = (build(&mut arena, &a), build(&mut arena, &b), build(&mut arena, &c));
        let (dxy, dyx) = (diff(&arena, x, y).cost, diff(&arena, y, x).cost);
        let (dyz, dxz) = (diff(&arena, y, z).cost, diff(&arena, x, z).cost);
        assert_eq!(dxy, dyx, "C5: symmetry");
        assert!(dxz <= dxy + dyz, "C8: triangle inequality");
    }
}

/// The case that defeats "match identical children first, then fill the gaps": a large child that
/// changed slightly is better paired than a small identical child is kept.
#[test]
fn identical_first_anchoring_would_be_wrong_here() {
    let mut arena = Arena::new();
    let big = |tail: u32, arena: &mut Arena| {
        let mut leaves: Vec<Id> = (0..99).map(|_| arena.mk(1, &[])).collect();
        leaves.push(arena.mk(tail, &[]));
        arena.mk(10, &leaves)
    };
    let a_big = big(2, &mut arena);
    let a_big2 = big(3, &mut arena);
    let small = arena.mk(5, &[]);
    let x = arena.mk(0, &[a_big, small]);
    let y = arena.mk(0, &[small, a_big2]);
    let got = diff_checked(&mut arena, x, y);
    assert_eq!(got.cost, oracle(&arena, x, y));
    assert!(got.cost < 10, "optimal pairs the two large children (cost {})", got.cost);
}

#[test]
fn c2_threshold_certificate_agrees_with_full_dp() {
    // Wide, repetitive child lists make many equal-cost paths and force several threshold rounds.
    let mut r = Rng(31337);
    let mut arena = Arena::new();
    let mut widened = 0u64;
    for _ in 0..200 {
        let width = 5 + r.below(30) as usize;
        let mk_list = |r: &mut Rng, arena: &mut Arena| -> Id {
            let kids: Vec<Id> = (0..width).map(|_| {
                let p = gen_plain(r, 2, 2);
                build(arena, &p)
            }).collect();
            arena.mk(0, &kids)
        };
        let x = mk_list(&mut r, &mut arena);
        let y = mk_list(&mut r, &mut arena);
        let got = diff_checked(&mut arena, x, y);
        widened += got.stats.widenings;
        assert_eq!(got.cost, oracle(&arena, x, y), "C2: certified answer differs from full DP");
    }
    assert!(widened > 0, "the test never exercised threshold widening");
}

#[test]
fn c3_rejects_a_wrong_script() {
    let mut arena = Arena::new();
    let l = |a: &mut Arena, t: u32| a.mk(t, &[]);
    let (p, q, s) = (l(&mut arena, 1), l(&mut arena, 2), l(&mut arena, 3));
    let x = arena.mk(0, &[p, q]);
    let y = arena.mk(0, &[p, s]);
    let d = diff(&arena, x, y);
    assert_eq!(apply(&mut arena, x, &d.edit).unwrap(), y);
    // Replaying against a different tree must be refused, not silently produce something.
    let z = arena.mk(0, &[q, s]);
    assert!(apply(&mut arena, z, &d.edit).is_err());
    assert_eq!(cost(&arena, &d.edit), d.cost);
}
