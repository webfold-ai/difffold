//! Exactness of the threshold filter [`difffold::tedfilter`] against an independent forest recursion.
//!
//! The oracle below charges the same cost model as the exact solver: 1 per insert or delete, and a relabel
//! that costs 0 for equal labels, 1 for different labels of one kind, and 2 across kinds. It shares no code
//! with the crate.
use difffold::ted::{ted, PostTree};
use difffold::tedfilter::{
    label_lower_bound, levenshtein_within, postorder_lower_bound, preorder_lower_bound,
    size_lower_bound, within, within_stats,
};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct T {
    label: u32,
    kind: u32,
    kids: Vec<T>,
}

fn node(label: u32, kind: u32, kids: Vec<T>) -> T {
    T { label, kind, kids }
}

fn size(f: &[T]) -> u32 {
    f.iter().map(|t| 1 + size(&t.kids)).sum()
}

fn relabel(v: &T, w: &T) -> u32 {
    if v.label == w.label {
        0
    } else if v.kind == w.kind {
        1
    } else {
        2
    }
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
    let mut f_del = fr.to_vec();
    f_del.extend(v.kids.iter().cloned());
    let mut g_ins = gr.to_vec();
    g_ins.extend(w.kids.iter().cloned());
    let a = fd(&f_del, g, memo) + 1;
    let b = fd(f, &g_ins, memo) + 1;
    let c = fd(fr, gr, memo) + fd(&v.kids, &w.kids, memo) + relabel(v, w);
    let r = a.min(b).min(c);
    memo.insert((f.to_vec(), g.to_vec()), r);
    r
}

fn oracle(a: &T, b: &T, memo: &mut HashMap<(Vec<T>, Vec<T>), u32>) -> u32 {
    fd(std::slice::from_ref(a), std::slice::from_ref(b), memo)
}

fn to_post(t: &T, label: &mut Vec<u32>, kind: &mut Vec<u32>, kids: &mut Vec<Vec<u32>>) -> u32 {
    let ks: Vec<u32> = t
        .kids
        .iter()
        .map(|c| to_post(c, label, kind, kids))
        .collect();
    label.push(t.label);
    kind.push(t.kind);
    kids.push(ks);
    label.len() as u32 - 1
}

fn post(t: &T) -> PostTree {
    let (mut l, mut k, mut kids) = (Vec::new(), Vec::new(), Vec::new());
    to_post(t, &mut l, &mut k, &mut kids);
    PostTree::from_kids(l, &kids).with_kinds(k)
}

/// The empty tree, which the exact solver and the filter both accept.
fn empty_post() -> PostTree {
    PostTree::from_kids(Vec::new(), &[]).with_kinds(Vec::new())
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

fn random_tree(r: &mut Rng, budget: &mut i32, labels: u64, kinds: u64) -> T {
    *budget -= 1;
    let label = r.below(labels) as u32;
    let kind = r.below(kinds) as u32;
    let mut kids = Vec::new();
    while *budget > 0 && r.below(3) != 0 {
        kids.push(random_tree(r, budget, labels, kinds));
    }
    node(label, kind, kids)
}

/// The `idx`-th node in preorder, counting `t` itself as 0.
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

/// Delete the node at preorder position `p >= 1` (the root is never deleted). Its children take its place.
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

/// Apply `ops` random edits: relabel-heavy (label or kind change), structure-heavy (delete or wrap a run of
/// children), so pairs at every distance from 0 to about `ops` appear.
fn mutate(r: &mut Rng, t: &mut T, ops: u32, labels: u64, kinds: u64) {
    for _ in 0..ops {
        let n = size(std::slice::from_ref(t)) as u64;
        match r.below(4) {
            0 | 1 => {
                let mut idx = r.below(n) as usize;
                let x = nth_mut(t, &mut idx).unwrap();
                x.label = r.below(labels) as u32;
                if r.below(3) == 0 {
                    x.kind = r.below(kinds) as u32;
                }
            }
            2 => {
                if n > 1 {
                    let mut idx = (1 + r.below(n - 1)) as usize - 1;
                    delete_rec(t, &mut idx);
                }
            }
            _ => {
                let mut idx = r.below(n) as usize;
                let x = nth_mut(t, &mut idx).unwrap();
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

/// Longest-common-subsequence distance over symbols: the insert/delete-only cost that charges 2 per relabel.
fn indel_distance(x: &[u32], y: &[u32]) -> usize {
    let mut dp = vec![vec![0usize; y.len() + 1]; x.len() + 1];
    for i in 1..=x.len() {
        for j in 1..=y.len() {
            dp[i][j] = if x[i - 1] == y[j - 1] {
                dp[i - 1][j - 1] + 1
            } else {
                dp[i - 1][j].max(dp[i][j - 1])
            };
        }
    }
    x.len() + y.len() - 2 * dp[x.len()][y.len()]
}

/// Naive full Levenshtein, the reference for [`levenshtein_within`].
fn naive_levenshtein(x: &[u32], y: &[u32]) -> usize {
    let mut prev: Vec<usize> = (0..=y.len()).collect();
    for i in 1..=x.len() {
        let mut cur = vec![i; y.len() + 1];
        for j in 1..=y.len() {
            let sub = prev[j - 1] + usize::from(x[i - 1] != y[j - 1]);
            cur[j] = sub.min(prev[j] + 1).min(cur[j - 1] + 1);
        }
        prev = cur;
    }
    prev[y.len()]
}

/// Checks that `within` equals `(Some(d) if d <= tau else None)` for every tau in `0..=d + 2`, and that
/// `within_stats` agrees with `within`. Returns the number of checks.
fn check_pair(a: &T, b: &T, d: u32, pa: &PostTree, pb: &PostTree) -> usize {
    let mut checks = 0;
    for tau in 0..=d + 2 {
        let want = (d <= tau).then_some(d);
        assert_eq!(within(pa, pb, tau), want, "tau {tau}: {a:?} vs {b:?}");
        assert_eq!(
            within_stats(pa, pb, tau).0,
            want,
            "stats path, tau {tau}: {a:?} vs {b:?}"
        );
        checks += 1;
    }
    checks
}

#[test]
fn within_is_exact_on_random_pairs_at_every_threshold() {
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    let mut memo = HashMap::new();
    let mut checks = 0usize;
    let mut within_pairs = 0usize;
    let rounds = 8000;
    for round in 0..rounds {
        let labels = 1 + r.below(4);
        let kinds = 1 + r.below(3);
        let mut budget = 1 + r.below(12) as i32;
        let a = random_tree(&mut r, &mut budget, labels, kinds);
        let b = if r.below(5) == 0 {
            let mut budget = 1 + r.below(12) as i32;
            random_tree(&mut r, &mut budget, labels, kinds)
        } else {
            let mut b = a.clone();
            let ops = r.below(6) as u32;
            mutate(&mut r, &mut b, ops, labels, kinds);
            b
        };
        let d = oracle(&a, &b, &mut memo);
        let (pa, pb) = (post(&a), post(&b));
        assert_eq!(
            ted(&pa, &pb),
            d,
            "round {round}: exact solver disagrees with the oracle: {a:?} vs {b:?}"
        );
        checks += check_pair(&a, &b, d, &pa, &pb);
        within_pairs += usize::from(d <= 3);
    }
    assert!(checks > rounds * 3);
    assert!(
        within_pairs > rounds / 10,
        "too few close pairs to test the accepting path"
    );
    eprintln!("random pairs: {rounds}, threshold checks: {checks}, pairs at distance <= 3: {within_pairs}");
}

#[test]
fn every_stage_lower_bound_is_below_the_exact_distance() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let mut memo = HashMap::new();
    for round in 0..6000 {
        let labels = 1 + r.below(4);
        let kinds = 1 + r.below(3);
        let mut budget = 1 + r.below(12) as i32;
        let a = random_tree(&mut r, &mut budget, labels, kinds);
        let mut b = a.clone();
        let ops = r.below(8) as u32;
        mutate(&mut r, &mut b, ops, labels, kinds);
        let d = oracle(&a, &b, &mut memo);
        let (pa, pb) = (post(&a), post(&b));
        assert!(
            size_lower_bound(&pa, &pb) <= d,
            "round {round} size: {a:?} vs {b:?}"
        );
        assert!(
            label_lower_bound(&pa, &pb) <= d,
            "round {round} labels: {a:?} vs {b:?}"
        );
        assert!(
            preorder_lower_bound(&pa, &pb) <= d,
            "round {round} preorder: {a:?} vs {b:?}"
        );
        assert!(
            postorder_lower_bound(&pa, &pb) <= d,
            "round {round} postorder: {a:?} vs {b:?}"
        );
    }
}

#[test]
fn levenshtein_stage_matches_the_naive_table() {
    let mut r = Rng(0x0123_4567_89ab_cdef);
    for round in 0..20000 {
        let alpha = 1 + r.below(3);
        let x: Vec<u32> = (0..r.below(13)).map(|_| r.below(alpha) as u32).collect();
        let y: Vec<u32> = (0..r.below(13)).map(|_| r.below(alpha) as u32).collect();
        let want = naive_levenshtein(&x, &y);
        for k in 0..=(x.len() + y.len() + 1) {
            let got = levenshtein_within(&x, &y, k);
            assert_eq!(
                got,
                (want <= k).then_some(want),
                "round {round} k {k}: {x:?} vs {y:?}"
            );
        }
    }
}

/// The insert/delete-only distance can exceed the tree distance because a relabel costs 1 in a tree and 2
/// as a delete plus an insert. A filter built on that line distance would wrongly reject this pair. The
/// filter must accept it.
#[test]
fn relabel_is_not_charged_as_delete_plus_insert() {
    let a = node(1, 0, vec![]);
    let b = node(2, 0, vec![]);
    let (pa, pb) = (post(&a), post(&b));
    assert_eq!(ted(&pa, &pb), 1);
    assert_eq!(
        indel_distance(&[1], &[2]),
        2,
        "the insert/delete-only distance overestimates here"
    );
    let (got, st) = within_stats(&pa, &pb, 1);
    assert_eq!(got, Some(1));
    assert_eq!(
        st.preorder.rejected, 0,
        "the preorder Levenshtein stage must not reject it"
    );
    assert_eq!(st.postorder.rejected, 0);
    assert_eq!(preorder_lower_bound(&pa, &pb), 1);

    // A structural pair with one relabel below a shared parent: the indel distance is 4 against a tree
    // distance of 1.
    let a = node(
        9,
        0,
        vec![node(1, 0, vec![node(5, 0, vec![])]), node(2, 0, vec![])],
    );
    let b = node(
        9,
        0,
        vec![node(3, 0, vec![node(5, 0, vec![])]), node(2, 0, vec![])],
    );
    let (pa, pb) = (post(&a), post(&b));
    let d = ted(&pa, &pb);
    assert_eq!(d, 1);
    assert_eq!(
        indel_distance(&pa.label, &pb.label),
        2,
        "indel distance over postorder labels"
    );
    assert_eq!(within(&pa, &pb, 1), Some(1));
    assert_eq!(within(&pa, &pb, 0), None);
}

/// A relabel across kinds costs 2 in the solver, which the substitution cost of 1 must not overshoot.
#[test]
fn cross_kind_relabel_costs_two_and_the_filter_respects_it() {
    let a = node(1, 0, vec![]);
    let b = node(2, 1, vec![]);
    let (pa, pb) = (post(&a), post(&b));
    assert_eq!(ted(&pa, &pb), 2);
    assert_eq!(within(&pa, &pb, 1), None);
    assert_eq!(within(&pa, &pb, 2), Some(2));
    // Same label, different kind: relabel is 0 for equal labels, so the distance is 0.
    let c = node(1, 1, vec![]);
    let pc = post(&c);
    assert_eq!(ted(&pa, &pc), 0);
    assert_eq!(within(&pa, &pc, 0), Some(0));
}

fn chain(n: u32, label: u32) -> T {
    (0..n).fold(node(label, 0, vec![]), |acc, _| node(label, 0, vec![acc]))
}

fn star(n: u32) -> T {
    node(0, 0, (0..n).map(|_| node(1, 0, vec![])).collect())
}

fn comb(n: u32, left: bool) -> T {
    (1..n).fold(node(1, 0, vec![]), |acc, _| {
        let leaf = node(1, 0, vec![]);
        let kids = if left {
            vec![acc, leaf]
        } else {
            vec![leaf, acc]
        };
        node(0, 0, kids)
    })
}

#[test]
fn degenerate_shapes_are_exact() {
    let mut shapes: Vec<T> = vec![node(0, 0, vec![]), node(7, 1, vec![])];
    for n in 1..=7 {
        shapes.push(chain(n, 0));
        shapes.push(chain(n, 3));
        shapes.push(star(n));
        shapes.push(comb(n, true));
        shapes.push(comb(n, false));
    }
    let mut memo = HashMap::new();
    let posts: Vec<PostTree> = shapes.iter().map(post).collect();
    for (i, a) in shapes.iter().enumerate() {
        for (j, b) in shapes.iter().enumerate() {
            let d = oracle(a, b, &mut memo);
            check_pair(a, b, d, &posts[i], &posts[j]);
        }
    }
}

#[test]
fn empty_trees_and_huge_thresholds() {
    let e = empty_post();
    let one = post(&node(1, 0, vec![]));
    assert_eq!(within(&e, &one, 0), None);
    assert_eq!(within(&e, &one, 1), Some(1));
    assert_eq!(within(&one, &e, 1), Some(1));
    assert_eq!(within(&e, &e, 0), Some(0));
    // Thresholds far above n + m must not allocate for them and must still return the exact distance.
    let a = post(&chain(6, 0));
    let b = post(&star(4));
    let d = ted(&a, &b);
    assert_eq!(within(&a, &b, u32::MAX), Some(d));
    assert_eq!(within_stats(&a, &b, u32::MAX).0, Some(d));
}
