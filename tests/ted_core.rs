//! `proof/extract/ted_core.rs` is the extraction-friendly copy of four functions of `src/ted.rs` (no
//! `Stats`, no closures, `while` loops). The proofs in `proof/Ted/` are about the extraction of that copy,
//! so this test ties it to the shipped code: each copied function is compared with the real one (the private
//! ones through `difffold::ted::proof_api`) on random inputs.
#![allow(dead_code, clippy::all)]

use difffold::ted::{proof_api, PostTree};

mod copy {
    include!("../proof/extract/ted_core.rs");
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

/// A random ordered tree with `size` nodes, in postorder: labels and child lists (0-based).
fn rand_tree(
    r: &mut Rng,
    size: usize,
    alphabet: u64,
    label: &mut Vec<u32>,
    kids: &mut Vec<Vec<u32>>,
) -> u32 {
    let mut ks = Vec::new();
    let mut rest = size - 1;
    while rest > 0 {
        let s = 1 + r.below(rest as u64) as usize;
        ks.push(rand_tree(r, s, alphabet, label, kids));
        rest -= s;
    }
    label.push(r.below(alphabet) as u32);
    kids.push(ks);
    label.len() as u32 - 1
}

fn rand_pair_parts(r: &mut Rng, max: u64) -> (Vec<u32>, Vec<Vec<u32>>) {
    let size = 1 + r.below(max) as usize;
    let alphabet = 1 + r.below(5);
    let (mut l, mut k) = (Vec::new(), Vec::new());
    rand_tree(r, size, alphabet, &mut l, &mut k);
    (l, k)
}

fn to_copy(t: &PostTree) -> copy::PostTree {
    copy::PostTree {
        label: t.label.clone(),
        lml: t.lml.clone(),
        keyroots: t.keyroots.clone(),
    }
}

#[test]
fn from_kids_copy_agrees_with_the_real_function() {
    let mut r = Rng(0x1234_5678_9ABC_DEF1);
    for round in 0..20_000 {
        let (l, k) = rand_pair_parts(&mut r, 30);
        let real = PostTree::from_kids(l.clone(), &k);
        let c = copy::from_kids(l, &k);
        assert_eq!(real.label, c.label, "round {round}");
        assert_eq!(real.lml, c.lml, "round {round}");
        assert_eq!(real.keyroots, c.keyroots, "round {round}");
    }
    // Forests with several roots: the proofs only assume that every child index is below its parent's.
    for round in 0..5_000 {
        let n = r.below(20) as usize;
        let l: Vec<u32> = (0..n).map(|_| r.below(4) as u32).collect();
        let k: Vec<Vec<u32>> = (0..n)
            .map(|i| {
                (0..if i == 0 { 0 } else { r.below(3) })
                    .map(|_| r.below(i as u64) as u32)
                    .collect()
            })
            .collect();
        let real = PostTree::from_kids(l.clone(), &k);
        let c = copy::from_kids(l, &k);
        assert_eq!(
            (real.lml, real.keyroots),
            (c.lml, c.keyroots),
            "forest round {round}"
        );
    }
}

#[test]
fn label_lower_bound_copy_agrees_with_the_real_function() {
    let mut r = Rng(0xDEAD_BEEF_0000_0001);
    for round in 0..20_000 {
        let (la, ka) = rand_pair_parts(&mut r, 25);
        let (lb, kb) = rand_pair_parts(&mut r, 25);
        let (a, b) = (PostTree::from_kids(la, &ka), PostTree::from_kids(lb, &kb));
        assert_eq!(
            proof_api::label_lower_bound(&a, &b),
            copy::label_lower_bound(&to_copy(&a), &to_copy(&b)),
            "round {round}"
        );
    }
}

#[test]
fn fill_window_copy_agrees_with_the_real_function_on_arbitrary_tables() {
    let mut r = Rng(0x0F0F_1234_5555_AAAA);
    for round in 0..4_000 {
        let (la, ka) = rand_pair_parts(&mut r, 14);
        let (lb, kb) = rand_pair_parts(&mut r, 14);
        let (a, b) = (PostTree::from_kids(la, &ka), PostTree::from_kids(lb, &kb));
        let (ca, cb) = (to_copy(&a), to_copy(&b));
        let (n, m) = (a.len(), b.len());
        let tau = r.below(9) as u32;
        let (t, inf) = (tau as usize, tau + 1);
        let w = 2 * t + 1;
        // Arbitrary table contents, so the writes of every cell are observable.
        let td0: Vec<u32> = (0..(n + 1) * w)
            .map(|_| r.below(u64::from(inf) + 1) as u32)
            .collect();
        let fd0: Vec<u32> = (0..(n.max(m) + 1) * w)
            .map(|_| r.below(u64::from(inf) + 1) as u32)
            .collect();
        for &i0 in &a.keyroots {
            for &j0 in &b.keyroots {
                let (i0, j0) = (i0 as usize, j0 as usize);
                let (li, lj) = (a.lml[i0 - 1] as usize, b.lml[j0 - 1] as usize);
                if li.abs_diff(lj) > 2 * t {
                    continue;
                }
                let (mut td1, mut fd1) = (td0.clone(), fd0.clone());
                let (mut td2, mut fd2) = (td0.clone(), fd0.clone());
                proof_api::fill_window(&a, &b, &mut td1, &mut fd1, i0, j0, tau);
                copy::fill_window(&ca, &cb, &mut td2, &mut fd2, i0, j0, tau);
                assert_eq!(td1, td2, "td round {round} window ({i0}, {j0}) tau {tau}");
                assert_eq!(fd1, fd2, "fd round {round} window ({i0}, {j0}) tau {tau}");
            }
        }
    }
}

#[test]
fn within_td_copy_agrees_with_the_real_function() {
    let mut r = Rng(0x7777_0000_ABCD_0123);
    for round in 0..6_000 {
        let (la, ka) = rand_pair_parts(&mut r, 16);
        let (lb, kb) = rand_pair_parts(&mut r, 16);
        let (a, b) = (PostTree::from_kids(la, &ka), PostTree::from_kids(lb, &kb));
        let (ca, cb) = (to_copy(&a), to_copy(&b));
        for tau in 0..=(a.len() + b.len()) as u32 {
            let x = proof_api::within_td(&a, &b, tau);
            let y = copy::within_td(&ca, &cb, tau);
            assert_eq!(x, y, "round {round} tau {tau}");
        }
    }
    // The empty trees.
    let e = PostTree::from_kids(Vec::new(), &[]);
    let (l, k) = rand_pair_parts(&mut r, 6);
    let b = PostTree::from_kids(l, &k);
    for tau in 0..8 {
        assert_eq!(
            proof_api::within_td(&e, &b, tau),
            copy::within_td(&to_copy(&e), &to_copy(&b), tau)
        );
        assert_eq!(
            proof_api::within_td(&b, &e, tau),
            copy::within_td(&to_copy(&b), &to_copy(&e), tau)
        );
    }
}
