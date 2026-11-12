//! Cross-level refinement of the top-down mapping: exact moves, container matching, recovery.
//!
//! The top-down engine ([`crate::diff`]) pairs a node only when its parent is paired, so a subtree
//! that moves, a container that is added around existing code (wrap) or removed from around it
//! (unwrap), and a reordered child are all reported as delete plus insert. This module starts from
//! the top-down mapping and repairs it in four phases, each of which only touches nodes that are
//! still unmapped (phase 1 may re-pair the interior of a subtree it proves identical):
//!
//! 1. **seed**: the top-down pairs, minus pairs of internal nodes with different kinds (a leaf may be
//!    updated to a leaf of another kind). A kind change
//!    on an internal node is how the top-down objective expresses a wrap (the wrapper is "relabelled"
//!    to the wrapped node); it is dropped so phases 2 and 3 can place both nodes properly.
//! 2. **exact** (`Options::exact`): an unmapped before-subtree and an unmapped after-subtree with the
//!    same arena id are structurally identical (I1), so they are paired node for node, largest first,
//!    wherever they sit. This is move and reorder detection for unchanged code, in O(1) per
//!    candidate because equality is an id comparison.
//! 3. **containers** (`Options::containers`): bottom-up, an unmapped internal before-node is paired
//!    with the unmapped after-node of the same kind that shares the most already-mapped descendants,
//!    when the Dice coefficient `2 |common| / (|desc b| + |desc a|)` reaches `Options::dice`.
//! 4. **recover** (`Options::recover`): for every container pair created in phase 3, the certified
//!    top-down aligner runs on the two subtrees and its pairs fill in the still-unmapped nodes
//!    beneath them. Then unmapped leaves with an equal label under a mapped parent pair up.
//!
//! The result is a mapping, not a top-down edit script: pairs may cross levels and order. It is not
//! an optimum of any edit-distance objective. [`Mapping::moves`] counts the pairs whose parents are
//! not paired with each other or that cross a sibling.

use crate::diff::diff;
use crate::intern::{Arena, Id};
use crate::mapping::{correspondence, Correspondence, PairKind};

/// "No partner".
pub const NIL: u32 = u32::MAX;

/// A tree flattened to preorder arrays. Node `v`'s children are `v + 1`, then each next sibling at
/// `c + size[c]`, until `v + size[v]`.
#[derive(Clone, Debug, Default)]
pub struct Flat {
    /// Node label (leaf labels carry text, internal labels are the kind).
    pub label: Vec<u32>,
    /// Node kind, from the caller's `kind_of`.
    pub kind: Vec<u32>,
    /// Parent index, [`NIL`] for the root.
    pub parent: Vec<u32>,
    /// Subtree size.
    pub size: Vec<u32>,
    /// Arena id of the subtree rooted here.
    pub id: Vec<Id>,
}

impl Flat {
    /// Flattens the subtree `root` of `arena` in preorder. `kind_of` maps a label to its kind.
    #[must_use]
    pub fn from_arena(arena: &Arena, root: Id, kind_of: impl Fn(u32) -> u32) -> Self {
        let n = arena.size(root) as usize;
        let mut f = Flat {
            label: Vec::with_capacity(n),
            kind: Vec::with_capacity(n),
            parent: Vec::with_capacity(n),
            size: Vec::with_capacity(n),
            id: Vec::with_capacity(n),
        };
        let mut stack: Vec<(Id, u32)> = vec![(root, NIL)];
        while let Some((x, p)) = stack.pop() {
            let v = f.label.len() as u32;
            let l = arena.label(x);
            f.label.push(l);
            f.kind.push(kind_of(l));
            f.parent.push(p);
            f.size.push(arena.size(x));
            f.id.push(x);
            for &k in arena.kids(x).iter().rev() {
                stack.push((k, v));
            }
        }
        f
    }

    /// Number of nodes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.label.len()
    }

    /// True for the empty tree.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.label.is_empty()
    }

    fn is_leaf(&self, v: usize) -> bool {
        self.size[v] == 1
    }

    /// Children of `v`, in order.
    fn kids(&self, v: usize) -> impl Iterator<Item = usize> + '_ {
        let end = v + self.size[v] as usize;
        let mut c = v + 1;
        std::iter::from_fn(move || {
            if c >= end {
                return None;
            }
            let out = c;
            c += self.size[c] as usize;
            Some(out)
        })
    }
}

/// A node mapping between two flattened trees.
#[derive(Clone, Debug)]
pub struct Mapping {
    /// `b2a[b]` is the after-index paired with before-node `b`, or [`NIL`].
    pub b2a: Vec<u32>,
    /// `a2b[a]` is the before-index paired with after-node `a`, or [`NIL`].
    pub a2b: Vec<u32>,
    /// The phase that last paired each before-node: 1 seed, 2 exact, 3 containers, 4 recovery by
    /// alignment, 5 recovery of leaves. For diagnostics.
    pub phase: Vec<u8>,
    cur: u8,
}

impl Mapping {
    /// An empty mapping.
    #[must_use]
    pub fn new(nb: usize, na: usize) -> Self {
        Self {
            b2a: vec![NIL; nb],
            a2b: vec![NIL; na],
            phase: vec![0; nb],
            cur: 1,
        }
    }

    fn link(&mut self, b: usize, a: usize) {
        self.unlink_b(b);
        self.unlink_a(a);
        self.b2a[b] = a as u32;
        self.a2b[a] = b as u32;
        self.phase[b] = self.cur;
    }

    fn unlink_b(&mut self, b: usize) {
        let a = self.b2a[b];
        if a != NIL {
            self.a2b[a as usize] = NIL;
            self.b2a[b] = NIL;
        }
    }

    fn unlink_a(&mut self, a: usize) {
        let b = self.a2b[a];
        if b != NIL {
            self.b2a[b as usize] = NIL;
            self.a2b[a] = NIL;
        }
    }

    /// Number of pairs.
    #[must_use]
    pub fn len(&self) -> usize {
        self.b2a.iter().filter(|&&a| a != NIL).count()
    }

    /// True when nothing is paired.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The pairs `(before, after)`, increasing in `before`.
    pub fn pairs(&self) -> impl Iterator<Item = (u32, u32)> + '_ {
        self.b2a
            .iter()
            .enumerate()
            .filter(|(_, &a)| a != NIL)
            .map(|(b, &a)| (b as u32, a))
    }

    /// Pairs that no top-down ordered mapping can contain: the parents are not paired with each
    /// other, or the pair crosses a sibling (its after-index is smaller than an earlier sibling's).
    #[must_use]
    pub fn moves(&self, bf: &Flat, af: &Flat) -> usize {
        let mut out = 0;
        for (b, a) in self.pairs() {
            let (pb, pa) = (bf.parent[b as usize], af.parent[a as usize]);
            if pb == NIL || pa == NIL {
                continue;
            }
            if self.b2a[pb as usize] != pa {
                out += 1;
            }
        }
        for v in 0..bf.len() {
            let mut last = 0u32;
            let pv = self.b2a[v];
            if pv == NIL {
                continue;
            }
            for c in bf.kids(v) {
                let a = self.b2a[c];
                if a == NIL || af.parent[a as usize] != pv {
                    continue;
                }
                if a < last {
                    out += 1;
                } else {
                    last = a;
                }
            }
        }
        out
    }
}

/// Which phases run.
#[derive(Clone, Copy, Debug)]
pub struct Options {
    /// Phase 2: pair identical unmapped subtrees wherever they are.
    pub exact: bool,
    /// Phase 3: pair unmapped containers by Dice similarity of mapped descendants.
    pub containers: bool,
    /// Phase 4: align the interior of phase-3 pairs, then pair equal leaves under mapped parents.
    pub recover: bool,
    /// Between phases 2 and 3: drop a tentative top-down pair of internal nodes whose Dice
    /// similarity (mapped descendants shared) is below `keep`.
    pub validate: bool,
    /// Dice threshold of `validate`.
    pub keep: f64,
    /// Phase 3 threshold.
    pub dice: f64,
    /// Smallest subtree (in nodes) phase 2 pairs. Leaves are left to phase 4.
    pub min_exact: u32,
    /// Subtrees smaller than this move only between paired parents (reorder), not across them.
    pub anchor_below: u32,
}

impl Options {
    /// The seed only: the top-down mapping with kind-changing pairs removed.
    pub const SEED: Options = Options {
        exact: false,
        validate: false,
        keep: 0.3,
        containers: false,
        recover: false,
        dice: 0.5,
        min_exact: 2,
        anchor_below: 6,
    };
    /// All phases.
    pub const FULL: Options = Options {
        exact: true,
        validate: true,
        keep: 0.3,
        containers: true,
        recover: true,
        dice: 0.5,
        min_exact: 2,
        anchor_below: 6,
    };
}

impl Options {
    /// Parses a comma-separated phase list: `seed`, `exact`, `containers`, `recover`, or `full`
    /// (all). Used by the benchmark and scoring binaries for ablations.
    ///
    /// # Errors
    /// Returns the unrecognised word.
    pub fn parse(spec: &str) -> Result<Self, String> {
        let mut o = Self::SEED;
        for w in spec.split(',').map(str::trim).filter(|w| !w.is_empty()) {
            match w {
                "seed" => {}
                "exact" => o.exact = true,
                "validate" => o.validate = true,
                "containers" => o.containers = true,
                "recover" => o.recover = true,
                "full" => o = Self::FULL,
                other => return Err(format!("unknown phase {other:?}")),
            }
        }
        Ok(o)
    }
}

impl Default for Options {
    fn default() -> Self {
        Self::FULL
    }
}

/// Pairs added by each phase (the seed count is after dropping kind-changing pairs).
#[derive(Clone, Copy, Debug, Default)]
pub struct RefineStats {
    /// Top-down pairs kept.
    pub seed: usize,
    /// Top-down pairs dropped for changing kind.
    pub dropped: usize,
    /// Nodes paired by phase 2.
    pub exact: usize,
    /// Tentative pairs dropped by the validation step.
    pub invalid: usize,
    /// Nodes paired by phase 3.
    pub containers: usize,
    /// Nodes paired by phase 4.
    pub recovered: usize,
    /// Leaf pairs dropped because their parents are not paired.
    pub orphans: usize,
}

/// Top-down diff of `x` and `y`, then [`refine`]. Returns both flattened trees and the mapping.
#[must_use]
pub fn match_trees(
    arena: &Arena,
    x: Id,
    y: Id,
    kind_of: impl Fn(u32) -> u32 + Copy,
    opts: &Options,
) -> (Flat, Flat, Mapping, RefineStats) {
    let d = diff(arena, x, y);
    let corr = correspondence(arena, x, y, &d.edit);
    let (bf, af) = (
        Flat::from_arena(arena, x, kind_of),
        Flat::from_arena(arena, y, kind_of),
    );
    let (m, st) = refine(arena, &bf, &af, &corr, opts);
    (bf, af, m, st)
}

/// Refines the top-down correspondence `seed` of `bf` and `af` (see the module docs).
#[must_use]
pub fn refine(
    arena: &Arena,
    bf: &Flat,
    af: &Flat,
    seed: &Correspondence,
    opts: &Options,
) -> (Mapping, RefineStats) {
    let mut m = Mapping::new(bf.len(), af.len());
    let mut st = RefineStats::default();
    // A pair inside an identical top-down subtree is firm; a pair of nodes whose subtrees differ is
    // tentative and phase 2 may replace it by an identical subtree found elsewhere.
    let mut firm = (vec![false; bf.len()], vec![false; af.len()]);
    for p in &seed.pairs {
        let (b, a) = (p.before as usize, p.after as usize);
        if bf.kind[b] == af.kind[a] || (bf.is_leaf(b) && af.is_leaf(a)) {
            m.link(b, a);
            st.seed += 1;
            if p.kind == PairKind::Identical {
                firm.0[b] = true;
                firm.1[a] = true;
            }
        } else {
            st.dropped += 1;
        }
    }
    if opts.exact {
        m.cur = 2;
        st.exact = exact_phase(bf, af, &mut m, &mut firm, opts.min_exact, opts.anchor_below);
    }
    if opts.validate {
        st.invalid = validate_phase(bf, af, &mut m, &firm, opts.keep);
    }
    let mut created: Vec<(usize, usize)> = Vec::new();
    if opts.containers {
        m.cur = 3;
        st.containers = container_phase(bf, af, &mut m, opts.dice, &mut created);
    }
    if opts.recover {
        m.cur = 4;
        st.recovered = recover_phase(arena, bf, af, &mut m, &created);
        if opts.validate {
            st.invalid += validate_phase(bf, af, &mut m, &firm, opts.keep);
        }
        m.cur = 5;
        st.recovered += leaf_phase(bf, af, &mut m);
    }
    st.orphans = drop_orphans(bf, af, &mut m, &firm);
    (m, st)
}

/// A leaf pair outside an identical subtree stands only when the parents of the two leaves are paired
/// with each other. Otherwise the pair is an accident of position inside a context (a top-down
/// pairing, or a recovered one) that a later phase has dismantled.
fn drop_orphans(bf: &Flat, af: &Flat, m: &mut Mapping, firm: &(Vec<bool>, Vec<bool>)) -> usize {
    let mut dropped = 0;
    for b in 0..bf.len() {
        let a = m.b2a[b];
        if a == NIL || !bf.is_leaf(b) || firm.0[b] {
            continue;
        }
        let (pb, pa) = (bf.parent[b], af.parent[a as usize]);
        if pb == NIL || pa == NIL || m.b2a[pb as usize] != pa {
            m.unlink_b(b);
            dropped += 1;
        }
    }
    dropped
}

/// Pairs `b` and `a` and, because their ids are equal, every node of the two subtrees.
fn link_subtrees(bf: &Flat, af: &Flat, m: &mut Mapping, b: usize, a: usize) -> usize {
    let n = bf.size[b] as usize;
    for k in 0..n {
        m.link(b + k, a + k);
    }
    debug_assert_eq!(n, af.size[a] as usize);
    n
}

fn exact_phase(
    bf: &Flat,
    af: &Flat,
    m: &mut Mapping,
    firm: &mut (Vec<bool>, Vec<bool>),
    min: u32,
    anchor_below: u32,
) -> usize {
    // Candidate after-nodes by id, in preorder.
    let mut by_id: std::collections::HashMap<u32, Vec<u32>> = std::collections::HashMap::new();
    let mut cand_b: Vec<u32> = Vec::new();
    for a in 0..af.len() {
        if !firm.1[a] && af.size[a] >= min {
            by_id.entry(af.id[a].0).or_default().push(a as u32);
        }
    }
    for b in 0..bf.len() {
        if !firm.0[b] && bf.size[b] >= min && by_id.contains_key(&bf.id[b].0) {
            cand_b.push(b as u32);
        }
    }
    // Largest first; stable in preorder, so earlier nodes win ties.
    cand_b.sort_by_key(|&b| std::cmp::Reverse(bf.size[b as usize]));
    let mut locked = (vec![false; bf.len()], vec![false; af.len()]);
    let mut paired = 0;
    for b in cand_b {
        let b = b as usize;
        if locked.0[b] {
            continue;
        }
        let list = by_id.get(&bf.id[b].0).expect("checked above");
        let want = if bf.parent[b] == NIL {
            NIL
        } else {
            m.b2a[bf.parent[b] as usize]
        };
        // Prefer a candidate under the partner of b's parent, else the nearest in preorder.
        let mut best: Option<((bool, std::cmp::Reverse<u32>), u32)> = None;
        for &a in list {
            if locked.1[a as usize] {
                continue;
            }
            let under = want != NIL && af.parent[a as usize] == want;
            if !under && bf.size[b] < anchor_below {
                continue;
            }
            let dist = (i64::from(a) - b as i64).unsigned_abs() as u32;
            let key = (under, std::cmp::Reverse(dist));
            if best.is_none_or(|(k, _)| key > k) {
                best = Some((key, a));
            }
        }
        if let Some((_, a)) = best {
            let a = a as usize;
            for k in 0..bf.size[b] as usize {
                locked.0[b + k] = true;
                locked.1[a + k] = true;
                firm.0[b + k] = true;
                firm.1[a + k] = true;
            }
            paired += link_subtrees(bf, af, m, b, a);
        }
    }
    paired
}

/// Drops tentative internal pairs that share too little: the top-down objective pairs two same-kind
/// siblings whenever relabelling is cheaper than deleting one and inserting the other, however
/// different their contents. Bottom-up, so an inner pair is judged before the pair around it.
fn validate_phase(
    bf: &Flat,
    af: &Flat,
    m: &mut Mapping,
    firm: &(Vec<bool>, Vec<bool>),
    keep: f64,
) -> usize {
    let mut dropped = 0;
    for b in (1..bf.len()).rev() {
        let a = m.b2a[b];
        if a == NIL || firm.0[b] || bf.is_leaf(b) || af.is_leaf(a as usize) {
            continue;
        }
        let a = a as usize;
        let (b_end, a_end) = (b + bf.size[b] as usize, a + af.size[a] as usize);
        let common = (b + 1..b_end)
            .filter(|&d| {
                let p = m.b2a[d] as usize;
                m.b2a[d] != NIL && p > a && p < a_end
            })
            .count();
        let denom = f64::from(bf.size[b] - 1) + f64::from(af.size[a] - 1);
        if 2.0 * common as f64 / denom < keep {
            m.unlink_b(b);
            dropped += 1;
        }
    }
    dropped
}

fn container_phase(
    bf: &Flat,
    af: &Flat,
    m: &mut Mapping,
    dice: f64,
    created: &mut Vec<(usize, usize)>,
) -> usize {
    let mut paired = 0;
    let mut common: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
    // Children have larger preorder indices than their parents, so a reverse sweep is a post-order.
    for b in (0..bf.len()).rev() {
        if m.b2a[b] != NIL || bf.is_leaf(b) {
            continue;
        }
        common.clear();
        let end = b + bf.size[b] as usize;
        for d in b + 1..end {
            let pd = m.b2a[d];
            if pd == NIL {
                continue;
            }
            let mut anc = af.parent[pd as usize];
            while anc != NIL {
                if m.a2b[anc as usize] == NIL && af.kind[anc as usize] == bf.kind[b] {
                    *common.entry(anc).or_insert(0) += 1;
                }
                anc = af.parent[anc as usize];
            }
        }
        let mut best: Option<(f64, u32, u32)> = None;
        for (&a, &c) in &common {
            let denom = f64::from(bf.size[b] - 1) + f64::from(af.size[a as usize] - 1);
            if denom == 0.0 {
                continue;
            }
            let s = 2.0 * f64::from(c) / denom;
            if s < dice {
                continue;
            }
            let dist = (i64::from(a) - b as i64).unsigned_abs() as u32;
            let better = match best {
                None => true,
                Some((bs, bd, ba)) => {
                    s > bs + 1e-12 || ((s - bs).abs() <= 1e-12 && (dist, a) < (bd, ba))
                }
            };
            if better {
                best = Some((s, dist, a));
            }
        }
        if let Some((_, _, a)) = best {
            m.link(b, a as usize);
            created.push((b, a as usize));
            paired += 1;
        }
    }
    paired
}

fn recover_phase(
    arena: &Arena,
    bf: &Flat,
    af: &Flat,
    m: &mut Mapping,
    created: &[(usize, usize)],
) -> usize {
    let mut added = 0;
    // Outer pairs first, so the aligner sees the largest context.
    let mut order: Vec<(usize, usize)> = created.to_vec();
    order.sort_unstable();
    for (b, a) in order {
        if m.b2a[b] != a as u32 {
            continue;
        }
        let d = diff(arena, bf.id[b], af.id[a]);
        let c = correspondence(arena, bf.id[b], af.id[a], &d.edit);
        for p in &c.pairs {
            let (pb, pa) = (b + p.before as usize, a + p.after as usize);
            if m.b2a[pb] == NIL && m.a2b[pa] == NIL && bf.kind[pb] == af.kind[pa] {
                m.link(pb, pa);
                added += 1;
            }
        }
    }
    added
}

/// Unmapped leaves with an equal label whose parents are paired with each other, in order.
fn leaf_phase(bf: &Flat, af: &Flat, m: &mut Mapping) -> usize {
    let mut added = 0;
    for pb in 0..bf.len() {
        let pa = m.b2a[pb];
        if pa == NIL || bf.is_leaf(pb) {
            continue;
        }
        let pa = pa as usize;
        let mut free_a: Vec<usize> = af
            .kids(pa)
            .filter(|&c| m.a2b[c] == NIL && af.is_leaf(c))
            .collect();
        if free_a.is_empty() {
            continue;
        }
        for c in bf.kids(pb) {
            if m.b2a[c] != NIL || !bf.is_leaf(c) {
                continue;
            }
            if let Some(i) = free_a.iter().position(|&x| af.label[x] == bf.label[c]) {
                let a = free_a.remove(i);
                m.link(c, a);
                added += 1;
            }
        }
    }
    added
}
