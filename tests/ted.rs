//! Exactness of the banded threshold-doubling tree edit distance against the textbook forest recursion.
use difffold::ted::{ted, ted_within, PostTree};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct T(u32, Vec<T>);

fn size(f: &[T]) -> u32 {
    f.iter().map(|t| 1 + size(&t.1)).sum()
}

/// Forest edit distance by the rightmost-root recursion, memoised on the forests themselves.
fn fd(f: &[T], g: &[T], memo: &mut HashMap<(Vec<T>, Vec<T>), u32>) -> u32 {
    if f.is_empty() {
        return size(g);
    }
    if g.is_empty() {
        return size(f);
    }
    if let Some(&v) = memo.get(&(f.to_vec(), g.to_vec())) {
        return v;
    }
    let (v, fr) = (f.last().unwrap(), &f[..f.len() - 1]);
    let (w, gr) = (g.last().unwrap(), &g[..g.len() - 1]);
    // Delete v: its children replace it. Insert w likewise.
    let mut f_del = fr.to_vec();
    f_del.extend(v.1.iter().cloned());
    let mut g_ins = gr.to_vec();
    g_ins.extend(w.1.iter().cloned());
    let a = fd(&f_del, g, memo) + 1;
    let b = fd(f, &g_ins, memo) + 1;
    let c = fd(fr, gr, memo) + fd(&v.1, &w.1, memo) + u32::from(v.0 != w.0);
    let r = a.min(b).min(c);
    memo.insert((f.to_vec(), g.to_vec()), r);
    r
}

fn to_post(t: &T, label: &mut Vec<u32>, kids: &mut Vec<Vec<u32>>) -> u32 {
    let ks: Vec<u32> = t.1.iter().map(|c| to_post(c, label, kids)).collect();
    label.push(t.0);
    kids.push(ks);
    label.len() as u32 - 1
}

fn post(t: &T) -> PostTree {
    let (mut l, mut k) = (Vec::new(), Vec::new());
    to_post(t, &mut l, &mut k);
    PostTree::from_kids(l, &k)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn random_tree(r: &mut Rng, budget: &mut i32, alpha: u64) -> T {
    *budget -= 1;
    let label = (r.next() % alpha) as u32;
    let mut kids = Vec::new();
    while *budget > 0 && r.next() % 3 != 0 {
        kids.push(random_tree(r, budget, alpha));
    }
    T(label, kids)
}

#[test]
fn matches_the_forest_recursion_on_random_small_trees() {
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    let mut memo = HashMap::new();
    for round in 0..6000 {
        let alpha = 1 + r.next() % 3;
        let (mut ba, mut bb) = (1 + (r.next() % 9) as i32, 1 + (r.next() % 9) as i32);
        let (a, b) = (
            random_tree(&mut r, &mut ba, alpha),
            random_tree(&mut r, &mut bb, alpha),
        );
        let want = fd(
            std::slice::from_ref(&a),
            std::slice::from_ref(&b),
            &mut memo,
        );
        let (pa, pb) = (post(&a), post(&b));
        assert_eq!(ted(&pa, &pb), want, "round {round}: {a:?} vs {b:?}");
        // The bounded form must agree with the oracle at and around the true distance.
        for tau in [want.saturating_sub(1), want, want + 1] {
            let got = ted_within(&pa, &pb, tau);
            assert_eq!(
                got,
                (want <= tau).then_some(want),
                "round {round} tau {tau}: {a:?} vs {b:?}"
            );
        }
    }
}

#[test]
fn identical_and_degenerate() {
    let t = T(1, vec![T(2, vec![]), T(3, vec![T(4, vec![])])]);
    assert_eq!(ted(&post(&t), &post(&t)), 0);
    let chain = |n: u32| (0..n).fold(T(0, vec![]), |acc, _| T(0, vec![acc]));
    assert_eq!(ted(&post(&chain(1)), &post(&chain(9))), 8);
    let star = |n: u32| T(0, (0..n).map(|_| T(1, vec![])).collect());
    assert_eq!(ted(&post(&star(5)), &post(&star(9))), 4);
}

#[test]
fn empty_trees_do_not_panic() {
    let empty = PostTree::from_kids(vec![], &[]);
    let one = post(&T(1, vec![]));
    assert_eq!(ted(&empty, &one), 1);
    assert_eq!(ted(&one, &empty), 1);
    assert_eq!(ted(&empty, &empty), 0);
}

#[test]
fn mapping_is_legal_and_costs_the_distance() {
    use difffold::ted::{check_mapping, ted_mapping};
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let mut memo = HashMap::new();
    for round in 0..4000 {
        let alpha = 1 + r.next() % 3;
        let (mut ba, mut bb) = (1 + (r.next() % 10) as i32, 1 + (r.next() % 10) as i32);
        let (a, b) = (
            random_tree(&mut r, &mut ba, alpha),
            random_tree(&mut r, &mut bb, alpha),
        );
        let want = fd(
            std::slice::from_ref(&a),
            std::slice::from_ref(&b),
            &mut memo,
        );
        let (pa, pb) = (post(&a), post(&b));
        let m = ted_mapping(&pa, &pb);
        assert_eq!(m.cost, want, "round {round}");
        let script_cost = check_mapping(&pa, &pb, &m.pairs).unwrap_or_else(|e| {
            panic!(
                "round {round}: illegal mapping {e}: {a:?} vs {b:?} {:?}",
                m.pairs
            )
        });
        assert_eq!(
            script_cost, want,
            "round {round}: mapping cost differs from the distance: {a:?} vs {b:?} {:?}",
            m.pairs
        );
        let ops = difffold::ted::replay_script(&pa, &pb, &m.pairs).unwrap_or_else(|e| {
            panic!(
                "round {round}: replay failed: {e}: {a:?} vs {b:?} {:?}",
                m.pairs
            )
        });
        assert_eq!(
            ops, want,
            "round {round}: operation count differs from the distance"
        );
    }
}

#[test]
fn the_validator_rejects_illegal_mappings() {
    use difffold::ted::check_mapping;
    // a = f(x, y), b = f(y, x): swapping the two leaves breaks sibling order.
    let a = T(0, vec![T(1, vec![]), T(2, vec![])]);
    let b = T(0, vec![T(2, vec![]), T(1, vec![])]);
    let (pa, pb) = (post(&a), post(&b));
    // Postorder: a = [x=1, y=2, f=3], b = [y=1, x=2, f=3]; map x->x (1->2) and y->y (2->1) crosses.
    assert!(check_mapping(&pa, &pb, &[(1, 2), (2, 1), (3, 3)]).is_err());
    // Ancestor swap: map the root of a to a leaf of b.
    let c = T(0, vec![T(0, vec![T(1, vec![])])]);
    let (pc, pd) = (post(&c), post(&c));
    assert!(check_mapping(&pc, &pd, &[(1, 3), (3, 1)]).is_err());
    assert_eq!(
        check_mapping(&pa, &pb, &[(3, 3), (1, 2)]).unwrap(),
        2,
        "two matched nodes; delete y and insert y"
    );
}

#[test]
fn replay_rejects_a_wrong_mapping() {
    use difffold::ted::replay_script;
    let a = T(0, vec![T(1, vec![]), T(2, vec![])]);
    let b = T(0, vec![T(2, vec![]), T(1, vec![])]);
    let (pa, pb) = (post(&a), post(&b));
    // Crossing the two leaves (x->x, y->y while the order is swapped) must not execute to b.
    let r = replay_script(&pa, &pb, &[(1, 2), (2, 1), (3, 3)]);
    assert!(
        r.is_err(),
        "a sibling-order-breaking mapping must fail to replay, got {r:?}"
    );
    // A legal mapping of the same pair replays with the exact cost 2 (delete one leaf, insert it back).
    assert_eq!(replay_script(&pa, &pb, &[(1, 2), (3, 3)]).unwrap(), 2);
}
