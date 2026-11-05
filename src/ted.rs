//! Exact ordered tree edit distance (Zhang-Shasha objective, unit insert, delete and relabel costs).
//!
//! Deleting a node promotes its children, so this is the classical general objective that RTED and
//! APTED compute, not the top-down (Selkow) objective of [`crate::diff`].
//!
//! The speed comes from asking "is the distance at most `tau`?" with a doubling `tau`, and from two
//! pruning facts that are exact (they discard only mappings that cost more than `tau`):
//!
//! 1. A tree edit mapping preserves "before in postorder", so the nodes before `i` that are mapped
//!    correspond to the mapped nodes before `j`. Every unmapped node shifts a pair by one, hence a pair
//!    `(i, j)` in a mapping of cost at most `tau` has `|i - j| <= tau`. Subtree distances are only
//!    needed for such pairs.
//! 2. In a forest distance table, a cell whose two forests differ in size by more than `tau` costs more
//!    than `tau`, so only a diagonal band of width `2 tau + 1` is computed. A row whose band is all
//!    above `tau` ends the table, because values never fall below the row minimum.
//!
//! This module is a loop-based first version. The recursion-only discipline of [`crate::lines`] has not
//! been applied here yet.

use crate::intern::{Arena, Id};

/// A tree in postorder with 1-based indices: node `i` has label `label[i - 1]` and leftmost leaf `lml[i - 1]`.
pub struct PostTree {
    /// Label id per node, in postorder.
    pub label: Vec<u32>,
    /// 1-based postorder index of the leftmost leaf of each node's subtree.
    pub lml: Vec<u32>,
    /// Keyroots (1-based), ascending: the nodes that are the root or have a left sibling.
    pub keyroots: Vec<u32>,
    /// Child lists (0-based indices), kept so the mirror image can be built.
    kids: Vec<Vec<u32>>,
    /// Node kind per node. Relabelling within a kind costs 1, across kinds 2 (the same as deleting and inserting).
    /// All zero by default, which makes every relabel cost 1: the classical unit-cost model.
    pub kind: Vec<u32>,
}

impl PostTree {
    /// Build from labels and child lists in postorder (children have smaller indices).
    #[must_use]
    pub fn from_kids(label: Vec<u32>, kids: &[Vec<u32>]) -> Self {
        let n = label.len();
        let mut lml = vec![0u32; n];
        let mut i = 0;
        while i < n {
            #[allow(clippy::len_zero)]
            let v = if kids[i].len() == 0 {
                i as u32 + 1
            } else {
                lml[kids[i][0] as usize]
            };
            lml[i] = v;
            i += 1;
        }
        let mut seen = vec![false; n + 2];
        let mut keyroots = Vec::new();
        i = n;
        while i > 0 {
            i -= 1;
            let l = lml[i] as usize;
            if !seen[l] {
                seen[l] = true;
                keyroots.push(i as u32 + 1);
            }
        }
        keyroots.reverse();
        let kind = vec![0u32; n];
        PostTree {
            label,
            lml,
            keyroots,
            kids: kids.to_vec(),
            kind,
        }
    }

    /// Attach node kinds (one per node, in postorder). With kinds, relabelling across kinds costs 2.
    #[must_use]
    pub fn with_kinds(mut self, kind: Vec<u32>) -> Self {
        assert_eq!(kind.len(), self.label.len(), "one kind per node");
        self.kind = kind;
        self
    }

    /// The mirror image (children in reverse order). Mirroring both trees leaves the distance unchanged.
    ///
    /// The postorder of the mirror image is the reverse of the preorder of `self`, and the preorder index of a node
    /// (1-based) is its leftmost leaf plus its depth, so node `x` moves to `n - lml[x] - depth[x]` (0-based).
    #[must_use]
    pub fn mirror(&self) -> PostTree {
        let n = self.label.len();
        if n == 0 {
            return PostTree::from_kids(Vec::new(), &[]);
        }
        let depth = depths(self);
        let mut pos = vec![0usize; n];
        let mut x = 0;
        while x < n {
            let l = self.lml[x] as usize;
            let d = depth[x];
            let q = n - l;
            let v = q - d;
            pos[x] = v;
            x += 1;
        }
        let mut label = vec![0u32; n];
        let mut kind = vec![0u32; n];
        let mut kids: Vec<Vec<u32>> = vec![Vec::new(); n];
        x = 0;
        while x < n {
            let y = pos[x];
            label[y] = self.label[x];
            kind[y] = self.kind[x];
            let mut ks = Vec::new();
            let mut j = self.kids[x].len();
            while j > 0 {
                j -= 1;
                ks.push(pos[self.kids[x][j] as usize] as u32);
            }
            kids[y] = ks;
            x += 1;
        }
        PostTree::from_kids(label, &kids).with_kinds(kind)
    }

    /// Work estimate of the left-path decomposition against `other`: the product of the keyroot subtree sizes.
    fn cost_against(&self, other: &PostTree) -> u128 {
        keyroot_work(self) * keyroot_work(other)
    }

    /// Expand an arena tree (a DAG when subtrees repeat) into its postorder tree.
    #[must_use]
    pub fn from_arena(arena: &Arena, root: Id) -> Self {
        let (mut label, mut kids) = (Vec::new(), Vec::new());
        expand(arena, root, &mut label, &mut kids);
        Self::from_kids(label, &kids)
    }

    /// Node count.
    #[must_use]
    pub fn len(&self) -> usize {
        self.label.len()
    }

    /// Whether the tree is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        #[allow(clippy::len_zero)]
        let e = self.label.len() == 0;
        e
    }
}

fn expand(arena: &Arena, x: Id, label: &mut Vec<u32>, kids: &mut Vec<Vec<u32>>) -> u32 {
    let ks: Vec<u32> = arena
        .kids(x)
        .iter()
        .map(|&k| expand(arena, k, label, kids))
        .collect();
    label.push(arena.label(x));
    kids.push(ks);
    label.len() as u32 - 1
}

/// The depth of every node (the root has depth 0). Parents have larger indices than their children, so the
/// nodes are visited from the root down.
fn depths(t: &PostTree) -> Vec<usize> {
    let n = t.label.len();
    let mut depth = vec![0usize; n];
    let mut p = n;
    while p > 0 {
        p -= 1;
        let d = depth[p] + 1;
        let mut j = 0;
        while j < t.kids[p].len() {
            depth[t.kids[p][j] as usize] = d;
            j += 1;
        }
    }
    depth
}

/// The 1-based preorder index of every node: its leftmost leaf plus its depth.
fn preorder(t: &PostTree) -> Vec<usize> {
    let n = t.label.len();
    let depth = depths(t);
    let mut pre = vec![0usize; n];
    let mut x = 0;
    while x < n {
        let l = t.lml[x] as usize;
        let d = depth[x];
        let v = l + d;
        pre[x] = v;
        x += 1;
    }
    pre
}

/// The sum of the keyroot subtree sizes.
fn keyroot_work(t: &PostTree) -> u128 {
    let mut s = 0u128;
    let mut i = 0;
    while i < t.keyroots.len() {
        let k = t.keyroots[i];
        s += (k - t.lml[k as usize - 1] + 1) as u128;
        i += 1;
    }
    s
}

/// Work counters of one [`ted_stats`] run.
#[derive(Debug, Default, Clone, Copy)]
pub struct Stats {
    /// Forest-distance cells evaluated, summed over all threshold attempts.
    pub cells: u64,
    /// Keyroot-pair windows run.
    pub windows: u64,
    /// Keyroot-pair windows skipped by the position filter.
    pub skipped: u64,
    /// Threshold values tried.
    pub attempts: u32,
    /// Whether the mirrored (right-path) orientation was chosen.
    pub mirrored: bool,
}

/// The exact distance, by doubling the threshold.
#[must_use]
pub fn ted(a: &PostTree, b: &PostTree) -> u32 {
    ted_stats(a, b).0
}

/// The exact distance with work counters.
#[must_use]
pub fn ted_stats(a: &PostTree, b: &PostTree) -> (u32, Stats) {
    let mut st = Stats::default();
    if a.is_empty() || b.is_empty() {
        return (umax(a.len(), b.len()) as u32, st);
    }
    // Left paths or right paths, whichever the keyroot sizes say is cheaper.
    let ma = a.mirror();
    let mb = b.mirror();
    if ma.cost_against(&mb) < a.cost_against(b) {
        st.mirrored = true;
        let d = ted_oriented(&ma, &mb, &mut st);
        (d, st)
    } else {
        let d = ted_oriented(a, b, &mut st);
        (d, st)
    }
}

/// Plain Zhang-Shasha: left paths, the threshold set to its maximum so no band or early exit applies.
/// The objective-matched unpruned baseline for measuring what the pruning contributes.
#[must_use]
pub fn ted_unpruned(a: &PostTree, b: &PostTree) -> u32 {
    let mut st = Stats::default();
    within(a, b, (a.len() + b.len()) as u32, &mut st).expect("the distance never exceeds n + m")
}

/// The relabel cost of node `x` of `a` to node `y` of `b` (1-based): 0 for equal labels, 1 within a kind, 2 across kinds.
fn relabel_cost(a: &PostTree, b: &PostTree, x: usize, y: usize) -> u32 {
    if a.label[x - 1] == b.label[y - 1] {
        0
    } else if a.kind[x - 1] == b.kind[y - 1] {
        1
    } else {
        2
    }
}

/// A lower bound on the distance: `max(n, m)` minus the size of the label multiset overlap. A mapping
/// of `k` pairs costs `n + m - k` plus its relabels, and at most `overlap` pairs can have equal labels.
fn label_lower_bound(a: &PostTree, b: &PostTree) -> u32 {
    // Counting instead of sorting: label ids are dense interner ids, so a count table over the labels of
    // `a` is small, and each label of `b` consumes one count of the same label.
    let mut top = 0usize;
    let mut i = 0;
    while i < a.label.len() {
        let l = a.label[i] as usize;
        if l >= top {
            top = l + 1;
        }
        i += 1;
    }
    let mut cnt = vec![0u32; top];
    i = 0;
    while i < a.label.len() {
        let l = a.label[i] as usize;
        cnt[l] += 1;
        i += 1;
    }
    let mut common = 0u32;
    i = 0;
    while i < b.label.len() {
        let l = b.label[i] as usize;
        if l < top && cnt[l] > 0 {
            cnt[l] -= 1;
            common += 1;
        }
        i += 1;
    }
    umax(a.len(), b.len()) as u32 - common
}

fn ted_oriented(a: &PostTree, b: &PostTree, st: &mut Stats) -> u32 {
    let n = a.len();
    let m = b.len();
    let cap = (n + m) as u32;
    let mut tau = max32(adiff(n, m) as u32, label_lower_bound(a, b));
    tau = max32(tau, 1);
    loop {
        // Once the band would cover a third of the table, skip the remaining doubling steps.
        if (tau as u64) * 3 >= umax(n, m) as u64 {
            tau = cap;
        }
        st.attempts = st.attempts.wrapping_add(1);
        let r = within_td(a, b, min32(tau, cap), st);
        if let Some(d) = r.0 {
            return d;
        }
        tau = dbl32(tau);
    }
}

/// The larger of two `u32`.
#[inline]
fn max32(x: u32, y: u32) -> u32 {
    if x >= y {
        x
    } else {
        y
    }
}

/// `x.saturating_mul(2)`.
#[inline]
fn dbl32(x: u32) -> u32 {
    if x >= 2_147_483_648 {
        u32::MAX
    } else {
        2 * x
    }
}

/// `Some(d)` with the exact distance when it is at most `tau`, else `None`.
#[must_use]
pub fn ted_within(a: &PostTree, b: &PostTree, tau: u32) -> Option<u32> {
    within(a, b, tau, &mut Stats::default())
}

fn within(a: &PostTree, b: &PostTree, tau: u32, st: &mut Stats) -> Option<u32> {
    within_td(a, b, tau, st).0
}

/// The larger of two `usize`.
#[inline]
fn umax(x: usize, y: usize) -> usize {
    if x >= y {
        x
    } else {
        y
    }
}

/// The smaller of two `usize`.
#[inline]
fn umin(x: usize, y: usize) -> usize {
    if x <= y {
        x
    } else {
        y
    }
}

/// `|x - y|`.
#[inline]
fn adiff(x: usize, y: usize) -> usize {
    if x >= y {
        x - y
    } else {
        y - x
    }
}

/// The smaller of two `u32`.
#[inline]
fn eq32(x: u32, y: u32) -> bool {
    if x == y {
        true
    } else {
        false
    }
}

fn min32(x: u32, y: u32) -> u32 {
    if x <= y {
        x
    } else {
        y
    }
}

/// The band index `x * w + (y + t - x)` of a cell `(x, y)` with `|x - y| <= t` in a table of row width `w`.
#[inline]
fn bidx(w: usize, t: usize, x: usize, y: usize) -> usize {
    x * w + (y + t - x)
}

/// The cell `(pp, qq)` of a band table, or `inf` outside the band.
#[inline]
fn get_cell(fd: &[u32], w: usize, t: usize, inf: u32, pp: usize, qq: usize) -> u32 {
    if adiff(pp, qq) <= t {
        fd[bidx(w, t, pp, qq)]
    } else {
        inf
    }
}

/// [`within`] that also returns the subtree-distance table, banded by `|x - y| <= tau`.
fn within_td(a: &PostTree, b: &PostTree, tau: u32, st: &mut Stats) -> (Option<u32>, Vec<u32>) {
    let n = a.len();
    let m = b.len();
    if adiff(n, m) as u32 > tau {
        return (None, Vec::new());
    }
    if n == 0 || m == 0 {
        let d = umax(n, m) as u32;
        if d <= tau {
            return (Some(d), Vec::new());
        }
        return (None, Vec::new());
    }
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    // td[x][y], banded by |x - y| <= t; index x * w + (y + t - x).
    let mut td = vec![inf; (n + 1) * w];
    let rows = umax(n, m) + 1;
    let mut fd = vec![inf; rows * w];
    let mut ia = 0;
    while ia < a.keyroots.len() {
        let i0 = a.keyroots[ia] as usize;
        let li = a.lml[i0 - 1] as usize;
        let mut ib = 0;
        while ib < b.keyroots.len() {
            let j0 = b.keyroots[ib] as usize;
            let lj = b.lml[j0 - 1] as usize;
            if adiff(li, lj) > 2 * t {
                st.skipped = st.skipped.wrapping_add(1);
            } else {
                st.windows = st.windows.wrapping_add(1);
                fill_window(a, b, &mut td, &mut fd, (i0, j0), tau, true, st);
            }
            ib += 1;
        }
        ia += 1;
    }
    let d = if adiff(n, m) <= t {
        td[bidx(w, t, n, m)]
    } else {
        inf
    };
    if d <= tau {
        (Some(d), td)
    } else {
        (None, td)
    }
}

/// Fill the forest-distance table of the window `(i0, j0)` and record the subtree distances of its
/// left-path pairs in `td`.
fn fill_window(
    a: &PostTree,
    b: &PostTree,
    td: &mut [u32],
    fd: &mut [u32],
    (i0, j0): (usize, usize),
    tau: u32,
    stop: bool,
    st: &mut Stats,
) {
    let t = tau as usize;
    let inf = tau + 1;
    let w = 2 * t + 1;
    let li = a.lml[i0 - 1] as usize;
    let lj = b.lml[j0 - 1] as usize;
    let si = i0 - li + 1;
    let sj = j0 - lj + 1;
    fd[bidx(w, t, 0, 0)] = 0;
    let lim_q = umin(sj, t);
    let mut q = 1;
    while q <= lim_q {
        fd[bidx(w, t, 0, q)] = q as u32;
        q += 1;
    }
    let lim_p = umin(si, t);
    let mut p = 1;
    while p <= lim_p {
        fd[bidx(w, t, p, 0)] = p as u32;
        p += 1;
    }
    p = 1;
    while p <= si {
        let qlo = umax(p.saturating_sub(t), 1);
        let qhi = umin(sj, p + t);
        let x = li + p - 1;
        let lx = a.lml[x - 1] as usize;
        let mut row_min = if p <= t { fd[bidx(w, t, p, 0)] } else { inf };
        q = qlo;
        while q <= qhi {
            st.cells = st.cells.wrapping_add(1);
            let y = lj + q - 1;
            let ly = b.lml[y - 1] as usize;
            let del = get_cell(fd, w, t, inf, p - 1, q) + 1;
            let ins = get_cell(fd, w, t, inf, p, q - 1) + 1;
            let v = if lx == li && ly == lj {
                let ren = relabel_cost(a, b, x, y);
                let diag = get_cell(fd, w, t, inf, p - 1, q - 1) + ren;
                let v = min32(min32(min32(del, ins), diag), inf);
                if adiff(x, y) <= t {
                    td[bidx(w, t, x, y)] = v;
                }
                v
            } else {
                let tdv = if adiff(x, y) <= t {
                    td[bidx(w, t, x, y)]
                } else {
                    inf
                };
                let sub = get_cell(fd, w, t, inf, lx - li, ly - lj) + tdv;
                min32(min32(min32(del, ins), sub), inf)
            };
            fd[bidx(w, t, p, q)] = v;
            row_min = min32(row_min, v);
            q += 1;
        }
        if qlo > qhi || (stop && row_min > tau) {
            break;
        }
        p += 1;
    }
}

/// An optimal edit mapping: `pairs` holds 1-based postorder indices `(node of a, node of b)`.
#[derive(Debug, Clone)]
pub struct Mapping {
    /// The exact distance.
    pub cost: u32,
    /// Matched node pairs, ascending in the first component.
    pub pairs: Vec<(u32, u32)>,
}

/// An optimal mapping, recovered by tracing back through the forest tables at the exact distance.
#[must_use]
pub fn ted_mapping(a: &PostTree, b: &PostTree) -> Mapping {
    ted_mapping_with(a, b, true)
}

/// [`ted_mapping`] with the tie-break made explicit. Among equal-cost optimal mappings, `prefer_match`
/// picks the one that matches a pair over deleting and inserting it; `false` prefers delete, then insert.
#[must_use]
pub fn ted_mapping_with(a: &PostTree, b: &PostTree, prefer_match: bool) -> Mapping {
    let cost = ted(a, b);
    if a.is_empty() || b.is_empty() {
        return Mapping {
            cost,
            pairs: Vec::new(),
        };
    }
    let to_b = traceback(a, b, cost, prefer_match);
    let n = a.len();
    let mut pairs = Vec::new();
    let mut x = 1;
    while x <= n {
        let y = to_b[x];
        if y != 0 {
            pairs.push((x as u32, y as u32));
        }
        x += 1;
    }
    Mapping { cost, pairs }
}

/// The window cell `(p, q)` is a pair of nodes on the left paths of both windows.
fn is_leaf_case(p: usize, q: usize, lx: usize, ly: usize, li: usize, lj: usize) -> bool {
    if p > 0 && q > 0 && lx == li {
        ly == lj
    } else {
        false
    }
}

/// Whether the table value `v` at `(p, q)` is explained by matching the last tree of both forests.
#[allow(clippy::too_many_arguments)]
fn diag_test(
    a: &PostTree,
    b: &PostTree,
    fd: &[u32],
    td: &[u32],
    w: usize,
    t: usize,
    inf: u32,
    (li, lj): (usize, usize),
    (p, q): (usize, usize),
    (x, y): (usize, usize),
    (lx, ly): (usize, usize),
    leaf_case: bool,
    v: u32,
) -> bool {
    if p > 0 && q > 0 {
        if leaf_case {
            let rc = relabel_cost(a, b, x, y);
            rc < 2 && eq32(get_cell(fd, w, t, inf, p - 1, q - 1) + rc, v)
        } else {
            let tdv = get_cell(td, w, t, inf, x, y);
            eq32(get_cell(fd, w, t, inf, lx - li, ly - lj) + tdv, v)
        }
    } else {
        false
    }
}

/// Whether the table value `v` at `(p, q)` is explained by deleting the last node of the first forest.
fn del_test(fd: &[u32], w: usize, t: usize, inf: u32, (p, q): (usize, usize), v: u32) -> bool {
    if p > 0 {
        eq32(get_cell(fd, w, t, inf, p - 1, q) + 1, v)
    } else {
        false
    }
}

/// Whether the table value `v` at `(p, q)` is explained by inserting the last node of the second forest.
fn ins_test(fd: &[u32], w: usize, t: usize, inf: u32, (p, q): (usize, usize), v: u32) -> bool {
    if q > 0 {
        eq32(get_cell(fd, w, t, inf, p, q - 1) + 1, v)
    } else {
        false
    }
}

/// The step the traceback takes: matching the last trees, unless deleting or inserting explains the cell and
/// matching is not preferred or not possible.
fn choose_diag(prefer_match: bool, diag_ok: bool, del_ok: bool, ins_ok: bool) -> bool {
    if prefer_match && diag_ok {
        true
    } else if del_ok {
        false
    } else {
        !ins_ok
    }
}

/// Put `(x, y)` in slot `top` of the stack, which has `top` live entries.
fn push_slot(stack_i: &mut Vec<usize>, stack_j: &mut Vec<usize>, top: usize, x: usize, y: usize) {
    if top == stack_i.len() {
        stack_i.push(x);
        stack_j.push(y);
    } else {
        stack_i[top] = x;
        stack_j[top] = y;
    }
}

/// The image in `b` of every node of `a` (both 1-based, 0 for a node without image) under an optimal mapping,
/// recovered by tracing back through the forest tables at the exact distance `cost`.
///
/// The stack holds the pairs of subtrees whose forest tables still have to be traced; `top` entries are live.
fn traceback(a: &PostTree, b: &PostTree, cost: u32, prefer_match: bool) -> Vec<usize> {
    let n = a.label.len();
    let m = b.label.len();
    let mut st = Stats::default();
    let (_d, mut td) = within_td(a, b, cost, &mut st);
    let t = cost as usize;
    let inf = cost + 1;
    let w = 2 * t + 1;
    let mut to_b = vec![0usize; n + 1];
    let mut stack_i = Vec::new();
    let mut stack_j = Vec::new();
    stack_i.push(n);
    stack_j.push(m);
    let mut top = 1;
    while top > 0 {
        top -= 1;
        let i = stack_i[top];
        let j = stack_j[top];
        let li = a.lml[i - 1] as usize;
        let lj = b.lml[j - 1] as usize;
        let si = i - li + 1;
        let sj = j - lj + 1;
        let mut fd = vec![inf; (si + 1) * w];
        fill_window(a, b, &mut td, &mut fd, (i, j), cost, false, &mut st);
        let mut p = si;
        let mut q = sj;
        while p + q > 0 {
            let v = get_cell(&fd, w, t, inf, p, q);
            let x = li + umax(p, 1) - 1;
            let y = lj + umax(q, 1) - 1;
            let lx = a.lml[x - 1] as usize;
            let ly = b.lml[y - 1] as usize;
            let leaf_case = is_leaf_case(p, q, lx, ly, li, lj);
            let diag_ok = diag_test(a, b, &fd, &td, w, t, inf, (li, lj), (p, q), (x, y), (lx, ly), leaf_case, v);
            let del_ok = del_test(&fd, w, t, inf, (p, q), v);
            let ins_ok = ins_test(&fd, w, t, inf, (p, q), v);
            let go_diag = choose_diag(prefer_match, diag_ok, del_ok, ins_ok);
            if go_diag {
                if leaf_case {
                    to_b[x] = y;
                    p -= 1;
                    q -= 1;
                } else {
                    push_slot(&mut stack_i, &mut stack_j, top, x, y);
                    top += 1;
                    p = lx - li;
                    q = ly - lj;
                }
            } else if del_ok {
                p -= 1;
            } else {
                q -= 1;
            }
        }
    }
    to_b
}

/// The verdict of [`check_core`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Check {
    /// A legal tree edit mapping; the payload is the cost of its edit script.
    Cost(u32),
    /// The pair `(x, y)` names a node outside the trees.
    Range(usize, usize),
    /// The pair `(x, y)` reuses a node already mapped.
    Dup(usize, usize),
    /// The pair `(x, y)` reverses the postorder of an earlier pair.
    Post(usize, usize),
    /// The pair `(x, y)` reverses the preorder of an earlier pair.
    Pre(usize, usize),
}

/// The checker behind [`check_mapping`].
///
/// A mapping is a legal tree edit mapping exactly when it is one to one and preserves both the postorder and
/// the preorder (equivalently, the postorder and the ancestor relation). The postorder is checked by walking the
/// nodes of `a` in postorder and the preorder by walking them in preorder, each time requiring the images in `b`
/// to increase.
pub fn check_core(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Check {
    let n = a.label.len();
    let m = b.label.len();
    let mut to_b = vec![0usize; n + 1];
    let mut to_a = vec![0usize; m + 1];
    let mut verdict = Check::Cost(0);
    let mut ok = true;
    let mut i = 0;
    while ok && i < pairs.len() {
        let x = pairs[i].0 as usize;
        let y = pairs[i].1 as usize;
        if x == 0 || x > n || y == 0 || y > m {
            verdict = Check::Range(x, y);
            ok = false;
        } else if to_b[x] != 0 || to_a[y] != 0 {
            verdict = Check::Dup(x, y);
            ok = false;
        } else {
            to_b[x] = y;
            to_a[y] = x;
            i += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let mut prev = 0;
    let mut x = 1;
    while ok && x <= n {
        let y = to_b[x];
        if y != 0 && y <= prev {
            verdict = Check::Post(x, y);
            ok = false;
        } else {
            if y != 0 {
                prev = y;
            }
            x += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let pa = preorder(a);
    let pb = preorder(b);
    let mut at = vec![0usize; n + 1];
    x = 1;
    while x <= n {
        at[pa[x - 1]] = x;
        x += 1;
    }
    let mut prev_pre = 0;
    let mut k = 1;
    while ok && k <= n {
        let x = at[k];
        let y = to_b[x];
        if y != 0 && pb[y - 1] <= prev_pre {
            verdict = Check::Pre(x, y);
            ok = false;
        } else {
            if y != 0 {
                prev_pre = pb[y - 1];
            }
            k += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let mut relabels = 0u32;
    x = 1;
    while x <= n {
        let y = to_b[x];
        if y != 0 {
            relabels += relabel_cost(a, b, x, y);
        }
        x += 1;
    }
    let cnt = pairs.len() as u32;
    Check::Cost((n as u32 - cnt) + (m as u32 - cnt) + relabels)
}

/// Independent validity check of a mapping. Returns the edit script cost it implies
/// (unmapped nodes of `a` deleted with their children promoted, unmapped nodes of `b` inserted, mapped
/// pairs with different labels relabelled) when the mapping is a legal tree edit mapping, else the reason.
///
/// Legal means: one to one; ancestor relations are preserved in both directions; sibling order is
/// preserved. Equivalently, deleting the unmapped nodes of `a` and of `b` (promoting children) leaves
/// two ordered forests that coincide under the mapping, so the replay produces `b`.
pub fn check_mapping(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Result<u32, String> {
    match check_core(a, b, pairs) {
        Check::Cost(c) => Ok(c),
        Check::Range(x, y) => Err(format!("pair ({x}, {y}) out of range")),
        Check::Dup(x, y) => Err(format!("not one to one at ({x}, {y})")),
        Check::Post(x, y) => Err(format!("postorder broken at ({x}, {y})")),
        Check::Pre(x, y) => Err(format!(
            "ancestor relation or sibling order broken at ({x}, {y})"
        )),
    }
}

/// The verdict of [`replay_core`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Replay {
    /// The script turns `a` into `b`; the payload is its number of unit operations.
    Ops(u32),
    /// The pair `(x, y)` names a node outside the trees.
    Range(usize, usize),
    /// The pair `(x, y)` reuses a node already mapped.
    Dup(usize, usize),
    /// The nodes of `a` do not keep their order: the image `y` of `x` is not above the earlier images.
    Order(usize, usize),
    /// After the deletions the subtree of `x` holds a different number of surviving nodes than the subtree
    /// of its image `y` will hold before the insertions.
    Shape(usize, usize),
}

/// The checker behind [`replay_script`].
///
/// An ordered tree in postorder is determined by its node sequence and, for each node, the number of nodes in
/// its subtree (equivalently its leftmost leaf). Deleting a node with promotion of its children removes it
/// from the sequence and shrinks the subtrees that contained it, so after the deletions of all unmapped nodes
/// of `a` the surviving nodes are the mapped ones and the subtree of a survivor `x` holds the mapped nodes of
/// its old subtree. The insertions of the unmapped nodes of `b` then produce `b` exactly when the survivors,
/// taken in order, are the images in order, each with the subtree size it will have in `b` among the images.
/// Relabels cost their relabel cost, deletions and insertions one each.
pub fn replay_core(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Replay {
    let n = a.label.len();
    let m = b.label.len();
    let mut to_b = vec![0usize; n + 1];
    let mut to_a = vec![0usize; m + 1];
    let mut verdict = Replay::Ops(0);
    let mut ok = true;
    let mut i = 0;
    while ok && i < pairs.len() {
        let x = pairs[i].0 as usize;
        let y = pairs[i].1 as usize;
        if x == 0 || x > n || y == 0 || y > m {
            verdict = Replay::Range(x, y);
            ok = false;
        } else if to_b[x] != 0 || to_a[y] != 0 {
            verdict = Replay::Dup(x, y);
            ok = false;
        } else {
            to_b[x] = y;
            to_a[y] = x;
            i += 1;
        }
    }
    if !ok {
        return verdict;
    }
    let mut cnt_a = vec![0usize; n + 1];
    let mut x = 1;
    while x <= n {
        let c = cnt_a[x - 1];
        cnt_a[x] = if to_b[x] != 0 { c + 1 } else { c };
        x += 1;
    }
    let mut cnt_b = vec![0usize; m + 1];
    let mut y = 1;
    while y <= m {
        let c = cnt_b[y - 1];
        cnt_b[y] = if to_a[y] != 0 { c + 1 } else { c };
        y += 1;
    }
    let mut ops = 0u32;
    let mut prev = 0;
    x = 1;
    while ok && x <= n {
        let y = to_b[x];
        if y == 0 {
            ops += 1;
            x += 1;
        } else if y <= prev {
            verdict = Replay::Order(x, y);
            ok = false;
        } else {
            prev = y;
            let sa = cnt_a[x] - cnt_a[a.lml[x - 1] as usize - 1];
            let sb = cnt_b[y] - cnt_b[b.lml[y - 1] as usize - 1];
            if sa != sb {
                verdict = Replay::Shape(x, y);
                ok = false;
            } else {
                ops += relabel_cost(a, b, x, y);
                x += 1;
            }
        }
    }
    if !ok {
        return verdict;
    }
    let k = pairs.len() as u32;
    Replay::Ops(ops + (m as u32 - k))
}

/// Execute the edit script implied by a mapping and check that it turns `a` into `b`.
///
/// The script is: relabel the mapped pairs whose labels differ; delete every unmapped node of `a`, its
/// children taking its place among its parent's children; insert every unmapped node of `b`. After the last
/// operation the working tree must equal `b` exactly: labels, shape and sibling order. Returns the number of
/// operations, which equals the mapping's cost (a relabel across node kinds counts as the deletion and
/// insertion it stands for). See [`replay_core`] for the representation of the working tree.
pub fn replay_script(a: &PostTree, b: &PostTree, pairs: &[(u32, u32)]) -> Result<u32, String> {
    match replay_core(a, b, pairs) {
        Replay::Ops(c) => Ok(c),
        Replay::Range(x, y) => Err(format!("bad pair ({x}, {y})")),
        Replay::Dup(x, y) => Err(format!("bad pair ({x}, {y})")),
        Replay::Order(x, y) => Err(format!(
            "children of a node differ: node {x} of a is not mapped above the earlier nodes (image {y})"
        )),
        Replay::Shape(x, y) => Err(format!(
            "the subtree of node {x} of a does not become the subtree of node {y} of b"
        )),
    }
}
