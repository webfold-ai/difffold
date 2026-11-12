//! Tests of the cross-level refinement (`difffold::refine`): hand-built moves, reorders, wraps and
//! unwraps, and properties that must hold for any pair of trees (the mapping is a bijection that
//! respects kinds, the result is deterministic, the seed alone is the top-down mapping).

use difffold::mapping::correspondence;
use difffold::refine::{match_trees, refine, Flat, Mapping, Options, NIL};
use difffold::{diff, Arena, Id};

const BLOCK: u32 = 1000;
const STMT: u32 = 1001;
const CALL: u32 = 1002;
const LIST: u32 = 1003;

/// Labels below 1000 are leaves of one kind; labels from 1000 are internal and are their own kind.
fn kind_of(l: u32) -> u32 {
    if l >= 1000 {
        l
    } else {
        1
    }
}

fn leaf(a: &mut Arena, text: u32) -> Id {
    a.mk(text, &[])
}

fn node(a: &mut Arena, kind: u32, kids: &[Id]) -> Id {
    a.mk(kind, kids)
}

/// A statement of six distinct leaves starting at `base`: 7 nodes, at least `anchor_below`, so it
/// may move across parents.
fn stmt(a: &mut Arena, base: u32) -> Id {
    let k: Vec<Id> = (0..6).map(|i| leaf(a, base + i)).collect();
    node(a, STMT, &k)
}

fn run(a: &Arena, x: Id, y: Id, o: &Options) -> (Flat, Flat, Mapping) {
    let (bf, af, m, _) = match_trees(a, x, y, kind_of, o);
    (bf, af, m)
}

/// Every node of the subtree of `bf` rooted at preorder index `b` is paired inside the subtree of
/// `af` rooted at `a`, node for node.
fn subtree_paired(m: &Mapping, bf: &Flat, b: usize, a: usize) -> bool {
    (0..bf.size[b] as usize).all(|k| m.b2a[b + k] == (a + k) as u32)
}

/// Preorder index of the `nth` node of `f` whose subtree id is `id`.
fn at(f: &Flat, id: Id, nth: usize) -> usize {
    (0..f.len())
        .filter(|&v| f.id[v] == id)
        .nth(nth)
        .expect("node present")
}

fn check_invariants(bf: &Flat, af: &Flat, m: &Mapping) {
    for (b, a) in m.pairs() {
        assert_eq!(m.a2b[a as usize], b, "b2a and a2b disagree at ({b}, {a})");
        let (b, a) = (b as usize, a as usize);
        if bf.size[b] > 1 || af.size[a] > 1 {
            assert_eq!(bf.kind[b], af.kind[a], "internal pair with different kinds");
        }
    }
    for (a, &b) in m.a2b.iter().enumerate() {
        if b != NIL {
            assert_eq!(m.b2a[b as usize], a as u32);
        }
    }
    assert_eq!(
        m.b2a.iter().filter(|&&a| a != NIL).count(),
        m.a2b.iter().filter(|&&b| b != NIL).count()
    );
}

#[test]
fn reorder_of_siblings_is_paired_and_counted_as_a_move() {
    let mut a = Arena::new();
    let (s1, s2, s3) = (stmt(&mut a, 1), stmt(&mut a, 10), stmt(&mut a, 20));
    let x = node(&mut a, BLOCK, &[s1, s2, s3]);
    let y = node(&mut a, BLOCK, &[s3, s1, s2]);
    // Top-down alone pairs at most two statements and relabels the rest.
    let (bf, af, seed) = run(&a, x, y, &Options::SEED);
    assert!(seed.len() < bf.len());
    let (bf, af2, m) = run(&a, x, y, &Options::FULL);
    check_invariants(&bf, &af2, &m);
    assert_eq!(
        m.len(),
        bf.len(),
        "every node has a partner after a pure reorder"
    );
    assert!(m.moves(&bf, &af2) >= 1);
    assert!(subtree_paired(&m, &bf, at(&bf, s3, 0), at(&af2, s3, 0)));
    let _ = af;
}

#[test]
fn subtree_moved_to_another_parent_keeps_all_its_nodes() {
    let mut a = Arena::new();
    let moved = stmt(&mut a, 50);
    let other = stmt(&mut a, 60);
    let (l1, l2) = (leaf(&mut a, 7), leaf(&mut a, 8));
    let b1 = node(&mut a, LIST, &[moved, l1]);
    let b2 = node(&mut a, LIST, &[other, l2]);
    let x = node(&mut a, BLOCK, &[b1, b2]);
    let (b1y, b2y) = {
        let b1y = node(&mut a, LIST, &[l1]);
        let b2y = node(&mut a, LIST, &[other, moved, l2]);
        (b1y, b2y)
    };
    let y = node(&mut a, BLOCK, &[b1y, b2y]);
    let (bf, af, m) = run(&a, x, y, &Options::FULL);
    check_invariants(&bf, &af, &m);
    let (pb, pa) = (at(&bf, moved, 0), at(&af, moved, 0));
    assert!(
        subtree_paired(&m, &bf, pb, pa),
        "moved statement must be paired node for node"
    );
    assert!(m.moves(&bf, &af) >= 1);
    // The other statement stays under its parent.
    assert!(subtree_paired(
        &m,
        &bf,
        at(&bf, other, 0),
        at(&af, other, 0)
    ));
    // Without the exact phase the move is lost.
    let (bf, _, plain) = run(&a, x, y, &Options::SEED);
    assert!(!subtree_paired(&plain, &bf, pb, pa));
}

#[test]
fn wrap_pairs_the_wrapped_statement_and_leaves_the_wrapper_unpaired() {
    let mut a = Arena::new();
    let inner = stmt(&mut a, 30);
    let keep = stmt(&mut a, 40);
    let x = node(&mut a, BLOCK, &[keep, inner]);
    let wrapper = node(&mut a, CALL, &[inner]);
    let y = node(&mut a, BLOCK, &[keep, wrapper]);
    let (bf, af, m) = run(&a, x, y, &Options::FULL);
    check_invariants(&bf, &af, &m);
    assert!(subtree_paired(&m, &bf, at(&bf, keep, 0), at(&af, keep, 0)));
    let (pb, pa) = (at(&bf, inner, 0), at(&af, inner, 0));
    assert!(
        subtree_paired(&m, &bf, pb, pa),
        "the wrapped statement keeps its identity"
    );
    assert_eq!(m.a2b[pa - 1], NIL, "the new wrapper has no partner");
    assert_eq!(af.kind[pa - 1], CALL);
    // Top-down alone loses the identity of the wrapped statement.
    let (bf, af, plain) = run(&a, x, y, &Options::SEED);
    assert!(!subtree_paired(
        &plain,
        &bf,
        at(&bf, inner, 0),
        at(&af, inner, 0)
    ));
}

#[test]
fn unwrap_is_the_mirror_of_wrap() {
    let mut a = Arena::new();
    let inner = stmt(&mut a, 30);
    let keep = stmt(&mut a, 40);
    let wrapper = node(&mut a, CALL, &[inner]);
    let x = node(&mut a, BLOCK, &[keep, wrapper]);
    let y = node(&mut a, BLOCK, &[keep, inner]);
    let (bf, af, m) = run(&a, x, y, &Options::FULL);
    check_invariants(&bf, &af, &m);
    let (pb, pa) = (at(&bf, inner, 0), at(&af, inner, 0));
    assert!(
        subtree_paired(&m, &bf, pb, pa),
        "the unwrapped statement keeps its identity"
    );
    assert_eq!(m.b2a[pb - 1], NIL, "the removed wrapper has no partner");
    assert_eq!(bf.kind[pb - 1], CALL);
}

#[test]
fn leaf_moved_into_a_new_wrapper_is_paired_by_label() {
    // `f(x)` becomes `g(f(x))`: the identifier `f` and its argument gain a parent.
    let mut a = Arena::new();
    let (f, xarg, g) = (leaf(&mut a, 3), leaf(&mut a, 4), leaf(&mut a, 5));
    let call = node(&mut a, CALL, &[f, xarg]);
    let before = node(&mut a, STMT, &[call]);
    let outer = node(&mut a, CALL, &[g, call]);
    let after = node(&mut a, STMT, &[outer]);
    let x = node(&mut a, BLOCK, &[before]);
    let y = node(&mut a, BLOCK, &[after]);
    let (bf, af, m) = run(&a, x, y, &Options::FULL);
    check_invariants(&bf, &af, &m);
    // before: block 0, stmt 1, call 2, f 3, x 4.  after: block 0, stmt 1, outer 2, g 3, call 4, f 5, x 6.
    assert_eq!(bf.label[3], af.label[5]);
    assert_eq!(m.b2a[3], 5);
    assert_eq!(m.b2a[4], 6);
}

#[test]
fn seed_is_the_top_down_mapping_minus_kind_changing_pairs() {
    let mut a = Arena::new();
    let (s1, s2) = (stmt(&mut a, 1), stmt(&mut a, 10));
    let s2b = {
        let k = [leaf(&mut a, 10), leaf(&mut a, 11), leaf(&mut a, 99)];
        node(&mut a, STMT, &k)
    };
    let x = node(&mut a, BLOCK, &[s1, s2]);
    let y = node(&mut a, BLOCK, &[s1, s2b]);
    let d = diff(&a, x, y);
    let corr = correspondence(&a, x, y, &d.edit);
    let (bf, af, m) = run(&a, x, y, &Options::SEED);
    let want: Vec<(u32, u32)> = corr
        .pairs
        .iter()
        .filter(|p| {
            let (b, a) = (p.before as usize, p.after as usize);
            bf.kind[b] == af.kind[a] || (bf.size[b] == 1 && af.size[a] == 1)
        })
        .map(|p| (p.before, p.after))
        .collect();
    let got: Vec<(u32, u32)> = m.pairs().collect();
    assert_eq!(got, want);
}

fn next(state: &mut u64, m: u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state % m
}

/// A deterministic pseudo-random tree of about `n` nodes from a seed.
fn random_tree(a: &mut Arena, state: &mut u64, depth: u32) -> Id {
    if depth == 0 || next(state, 4) == 0 {
        let l = next(state, 12) as u32;
        return a.mk(l, &[]);
    }
    let n = 1 + next(state, 4) as usize;
    let kids: Vec<Id> = (0..n).map(|_| random_tree(a, state, depth - 1)).collect();
    let k = BLOCK + next(state, 3) as u32;
    a.mk(k, &kids)
}

#[test]
fn mapping_is_a_kind_respecting_bijection_and_deterministic() {
    for seed in 1..60u64 {
        let mut a = Arena::new();
        let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let x = random_tree(&mut a, &mut s, 5);
        // The after-tree is a different random tree from a nearby seed, so some subtrees coincide.
        let mut s2 = (seed / 2).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        let y = random_tree(&mut a, &mut s2, 5);
        for opts in [Options::SEED, Options::FULL] {
            let (bf, af, m) = run(&a, x, y, &opts);
            check_invariants(&bf, &af, &m);
            let (_, _, m2) = run(&a, x, y, &opts);
            assert_eq!(
                m.b2a, m2.b2a,
                "refinement must be deterministic (seed {seed})"
            );
        }
        // The refine entry point agrees with match_trees.
        let d = diff(&a, x, y);
        let corr = correspondence(&a, x, y, &d.edit);
        let (bf, af) = (
            Flat::from_arena(&a, x, kind_of),
            Flat::from_arena(&a, y, kind_of),
        );
        let (m, _) = refine(&a, &bf, &af, &corr, &Options::FULL);
        let (_, _, m3) = run(&a, x, y, &Options::FULL);
        assert_eq!(m.b2a, m3.b2a);
    }
}

#[test]
fn identical_trees_map_node_for_node() {
    let mut a = Arena::new();
    let mut s = 12345u64;
    let x = random_tree(&mut a, &mut s, 6);
    let (bf, af, m) = run(&a, x, x, &Options::FULL);
    assert_eq!(m.len(), bf.len());
    assert!(m.pairs().all(|(b, a)| b == a));
    assert_eq!(m.moves(&bf, &af), 0);
}

fn opts(spec: &str) -> Options {
    Options::parse(spec).expect("valid phase list")
}

#[test]
fn container_phase_pairs_a_container_that_gained_a_wrapper_by_shared_descendants() {
    // A list of two statements gains a third statement and is wrapped in a new call node. Top-down
    // pairs the list with the wrapper (a kind change, dropped by the seed), so only the statements
    // are paired across levels by the exact phase; the container phase pairs the two lists.
    let mut a = Arena::new();
    let (p, q, r) = (stmt(&mut a, 100), stmt(&mut a, 110), stmt(&mut a, 120));
    let list_b = node(&mut a, LIST, &[p, q]);
    let list_a = node(&mut a, LIST, &[p, q, r]);
    let wrapper = node(&mut a, CALL, &[list_a]);
    let x = node(&mut a, BLOCK, &[list_b]);
    let y = node(&mut a, BLOCK, &[wrapper]);
    let (bf, af, no) = run(&a, x, y, &opts("exact"));
    let (lb, la) = (
        (0..bf.len()).find(|&v| bf.kind[v] == LIST).unwrap(),
        (0..af.len()).find(|&v| af.kind[v] == LIST).unwrap(),
    );
    assert_eq!(
        no.b2a[lb], NIL,
        "without the container phase the lists stay unpaired"
    );
    let (bf, af, yes) = run(&a, x, y, &opts("exact,containers"));
    check_invariants(&bf, &af, &yes);
    assert_eq!(yes.b2a[lb], la as u32);
    assert!(subtree_paired(&yes, &bf, at(&bf, p, 0), at(&af, p, 0)));
    assert!(subtree_paired(&yes, &bf, at(&bf, q, 0), at(&af, q, 0)));
}

#[test]
fn validate_phase_drops_a_tentative_pair_that_shares_almost_nothing() {
    // Same-kind statements at the same position, but only one of six leaves is common.
    let mut a = Arena::new();
    let ls: Vec<Id> = (0..6).map(|i| leaf(&mut a, 200 + i)).collect();
    let s_b = node(&mut a, STMT, &ls);
    let s_a = {
        let k = [leaf(&mut a, 200)];
        node(&mut a, STMT, &k)
    };
    let x = node(&mut a, BLOCK, &[s_b]);
    let y = node(&mut a, BLOCK, &[s_a]);
    let (bf, af, kept) = run(&a, x, y, &opts("exact"));
    check_invariants(&bf, &af, &kept);
    let s_idx = (0..bf.len()).find(|&v| bf.kind[v] == STMT).unwrap();
    assert_ne!(kept.b2a[s_idx], NIL, "top-down pairs the two statements");
    let (bf, af, dropped) = run(&a, x, y, &opts("exact,validate"));
    check_invariants(&bf, &af, &dropped);
    assert_eq!(
        dropped.b2a[s_idx], NIL,
        "validate removes the implausible pair"
    );
    // The block pair stays.
    assert_eq!(dropped.b2a[0], 0);
}

#[test]
fn descend_phase_pairs_a_leaf_that_moved_between_branches_and_retarget_prefers_equal_text() {
    // Leaf 9 moves from one statement to the other (small subtrees, so the exact phase does not move them).
    let mut a = Arena::new();
    let (l1, l2, l3, l9) = (
        leaf(&mut a, 1),
        leaf(&mut a, 2),
        leaf(&mut a, 3),
        leaf(&mut a, 9),
    );
    let (s1b, s2b) = (node(&mut a, CALL, &[l1, l9]), node(&mut a, CALL, &[l2]));
    let (s1a, s2a) = (node(&mut a, CALL, &[l1]), node(&mut a, CALL, &[l2, l9]));
    let (x, y) = (
        node(&mut a, BLOCK, &[s1b, s2b, l3]),
        node(&mut a, BLOCK, &[s1a, s2a, l3]),
    );
    let (bf, af, without) = run(&a, x, y, &opts("exact,validate,containers,recover"));
    let nine_b = (0..bf.len()).find(|&v| bf.label[v] == 9).unwrap();
    let nine_a = (0..af.len()).find(|&v| af.label[v] == 9).unwrap();
    assert_ne!(
        without.b2a[nine_b], nine_a as u32,
        "the top-down skeleton cannot move a leaf"
    );
    let (bf, af, with) = run(&a, x, y, &opts("exact,validate,containers,recover,descend"));
    check_invariants(&bf, &af, &with);
    assert_eq!(with.b2a[nine_b], nine_a as u32);
}
