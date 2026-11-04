//! Top-down ordered-tree distance with a certified banded aligner.
//!
//! The objective is the top-down (Selkow) edit distance, unit cost per node:
//!
//! ```text
//! dist(x, y) = 0                                   if x == y        (O(1) by I1)
//!            = [label x != label y] + align(kids x, kids y)  otherwise (roots always pair)
//! align      = min-cost ordered alignment; delete a child = its size,
//!              insert a child = its size, pair children x', y' = dist(x', y')
//! ```
//!
//! Contracts (`SPEC.md` has the statements):
//!
//! * `C1` strip: equal first or last children pair at cost 0 without loss of optimality.
//! * `C2` threshold certificate: the DP keeps a cell `(i, j)` only if `F(i,j) + h(i,j) <= tau`,
//!   where `F` is the cost accumulated forward from the start and `h(i,j) = |R_a(i) - R_b(j)|` is
//!   the reversed accumulation of subtree sizes, an admissible bound on the remaining cost. A
//!   pruned cell lies on no path of total cost `<= tau`, so a result of cost `<= tau` is optimal.
//!   `tau` starts at `h(0,0)` and doubles until a result fits. No width is guessed.
//! * `C3` replay: `apply(before, script) == after` and `cost(script) == dist`.
//! * `C4` equals the naive full DP (the oracle in `tests/`).
//! * `C5..C8` symmetry, identity, size lower bound `dist >= |size x - size y|`, triangle inequality.

use crate::intern::{Arena, Id};
use crate::kernel::{self, bound, suffix_sums, Counters, Oracle, Row, INF};
use apeiron::freq::Table;

/// One step of a child alignment, as indices into the two child lists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Step {
    Pair(usize, usize),
    Del(usize),
    Ins(usize),
}

/// An edit script over canonical nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Edit {
    /// An identical subtree, carried over.
    Keep(Id),
    /// A subtree present only before.
    Del(Id),
    /// A subtree present only after.
    Ins(Id),
    /// A node kept with children edited; relabelled to `to_label`.
    Upd {
        /// The before-node.
        from: Id,
        /// The label after the edit.
        to_label: u32,
        /// Child edits in order.
        kids: Vec<Edit>,
    },
}

/// Where the first threshold of an align comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tau0 {
    /// `h(0, 0)`, the size-difference bound.
    Bound,
    /// The constant 1.
    One,
}

/// Switches for the same-objective ablation ladder. Every setting computes the same distance.
#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// Compare subtrees by recursion instead of by id.
    pub deep_eq: bool,
    /// Memoise `dist` on the (id, id) pair.
    pub memo: bool,
    /// Prune by `F + h <= tau`; off keeps every cell (full DP).
    pub threshold: bool,
    /// First threshold.
    pub tau0: Tau0,
    /// Threshold growth factor per round (at least 2).
    pub growth: u32,
}

impl Config {
    /// Full DP, structural comparison, no memo.
    pub const FULL_STRUCTURAL: Config = Config {
        deep_eq: true,
        memo: false,
        threshold: false,
        tau0: Tau0::Bound,
        growth: 2,
    };
    /// Full DP with exact interning (id equality).
    pub const FULL_INTERNED: Config = Config {
        deep_eq: false,
        memo: false,
        threshold: false,
        tau0: Tau0::Bound,
        growth: 2,
    };
    /// Full DP with interning and memoisation.
    pub const FULL_MEMO: Config = Config {
        deep_eq: false,
        memo: true,
        threshold: false,
        tau0: Tau0::Bound,
        growth: 2,
    };
    /// The production configuration: interning, memo, threshold pruning, doubling from `h(0,0)`.
    pub const PRODUCTION: Config = Config {
        deep_eq: false,
        memo: true,
        threshold: true,
        tau0: Tau0::Bound,
        growth: 2,
    };
}

impl Default for Config {
    fn default() -> Self {
        Self::PRODUCTION
    }
}

/// Counters for one differ.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// Non-trivial aligns run (both middle lists non-empty).
    pub aligns: u64,
    /// Threshold rounds over all aligns (each fill is one round).
    pub rounds: u64,
    /// Largest number of rounds any single align needed.
    pub max_rounds: u64,
    /// Memo lookups that hit.
    pub memo_hits: u64,
    /// Memo lookups that missed.
    pub memo_misses: u64,
    /// Cells whose value was kept (not pruned).
    pub kept: u64,
    /// Distinct unequal pairs whose distance was computed.
    pub pairs: u64,
    /// DP cells filled.
    pub cells: u64,
    /// Aligns accepted on the first threshold.
    pub first_round: u64,
    /// Extra threshold rounds beyond the first.
    pub widenings: u64,
    /// Recursive distances skipped because the cell could not fit under the threshold.
    pub pruned: u64,
}

/// Result of [`diff`].
#[derive(Debug)]
pub struct Diff {
    /// The top-down edit distance.
    pub cost: u32,
    /// An edit script of exactly that cost.
    pub edit: Edit,
    /// Work counters.
    pub stats: Stats,
}

struct Aligned {
    cost: u32,
    steps: Vec<Step>,
}

struct Differ<'a> {
    arena: &'a Arena,
    cfg: Config,
    memo: Table<u64, u32>,
    stats: Stats,
}

fn pair_key(x: Id, y: Id) -> u64 {
    (u64::from(x.0) << 32) | u64::from(y.0)
}

impl<'a> Differ<'a> {
    fn new(arena: &'a Arena, cfg: Config) -> Self {
        Self {
            arena,
            cfg,
            memo: Table::new(),
            stats: Stats::default(),
        }
    }

    fn eq(&self, x: Id, y: Id) -> bool {
        if self.cfg.deep_eq {
            self.arena.deep_eq(x, y)
        } else {
            x == y
        }
    }

    fn dist(&mut self, x: Id, y: Id) -> u32 {
        if self.eq(x, y) {
            return 0;
        }
        let key = pair_key(x, y);
        if self.cfg.memo {
            if let Some(&d) = self.memo.get(&key) {
                self.stats.memo_hits += 1;
                return d;
            }
            self.stats.memo_misses += 1;
        }
        self.stats.pairs += 1;
        let rel = u32::from(self.arena.label(x) != self.arena.label(y));
        let a = self.align(self.arena.kids(x), self.arena.kids(y)).cost;
        let d = rel + a;
        if self.cfg.memo {
            self.memo.insert_merge_last_write(key, d);
        }
        d
    }

    fn align(&mut self, a: &'a [Id], b: &'a [Id]) -> Aligned {
        let (n, m) = (a.len(), b.len());
        let mut p = 0;
        while p < n.min(m) && self.eq(a[p], b[p]) {
            p += 1;
        }
        let mut s = 0;
        while s < n.min(m) - p && self.eq(a[n - 1 - s], b[m - 1 - s]) {
            s += 1;
        }
        let mut steps: Vec<Step> = (0..p).map(|i| Step::Pair(i, i)).collect();
        let (ma, mb) = (&a[p..n - s], &b[p..m - s]);
        let mid = self.align_mid(ma, mb);
        for st in mid.steps {
            steps.push(match st {
                Step::Pair(i, j) => Step::Pair(i + p, j + p),
                Step::Del(i) => Step::Del(i + p),
                Step::Ins(j) => Step::Ins(j + p),
            });
        }
        for k in 0..s {
            steps.push(Step::Pair(n - s + k, m - s + k));
        }
        Aligned {
            cost: mid.cost,
            steps,
        }
    }

    fn align_mid(&mut self, a: &'a [Id], b: &'a [Id]) -> Aligned {
        let (n, m) = (a.len(), b.len());
        let sa: Vec<u32> = a.iter().map(|&x| self.arena.size(x)).collect();
        let sb: Vec<u32> = b.iter().map(|&x| self.arena.size(x)).collect();
        if n == 0 || m == 0 {
            let mut steps = Vec::with_capacity(n + m);
            steps.extend((0..n).map(Step::Del));
            steps.extend((0..m).map(Step::Ins));
            return Aligned {
                cost: sa.iter().sum::<u32>() + sb.iter().sum::<u32>(),
                steps,
            };
        }
        // Reversed accumulation: ra[i] is the total size of a[i..], rb[j] likewise.
        let ra = suffix_sums(&sa);
        let rb = suffix_sums(&sb);
        self.stats.aligns += 1;
        let mut tau = if self.cfg.threshold {
            match self.cfg.tau0 {
                Tau0::Bound => bound(&ra, &rb, 0, 0),
                Tau0::One => 1,
            }
        } else {
            INF / 2
        };
        let mut rounds = 0u64;
        loop {
            rounds += 1;
            self.stats.rounds += 1;
            if let Some(rows) = self.fill(a, b, &sa, &sb, &ra, &rb, tau) {
                let cost = rows[n].at(m);
                assert!(cost < INF, "final cell kept");
                debug_assert!(cost <= tau);
                if rounds == 1 {
                    self.stats.first_round += 1;
                }
                self.stats.max_rounds = self.stats.max_rounds.max(rounds);
                let steps = self.trace(a, b, &sa, &sb, &rows);
                return Aligned { cost, steps };
            }
            self.stats.widenings += 1;
            tau = (tau.saturating_mul(self.cfg.growth.max(2))).max(tau + 1);
        }
    }

    /// Threshold DP. Returns `None` when no path of cost `<= tau` exists. The DP itself is
    /// `kernel::fill`; this supplies the recursive pair cost and collects the counters.
    #[allow(clippy::too_many_arguments)]
    fn fill(
        &mut self,
        a: &'a [Id],
        b: &'a [Id],
        sa: &[u32],
        sb: &[u32],
        ra: &[u32],
        rb: &[u32],
        tau: u32,
    ) -> Option<Vec<Row>> {
        let on = self.cfg.threshold;
        let mut c = Counters::default();
        let rows = {
            let mut o = Pairs { d: self, a, b };
            kernel::fill(&mut o, sa, sb, ra, rb, tau, on, &mut c)
        };
        self.stats.cells += c.cells;
        self.stats.kept += c.kept;
        self.stats.pruned += c.pruned;
        rows
    }

    fn trace(
        &mut self,
        a: &'a [Id],
        b: &'a [Id],
        sa: &[u32],
        sb: &[u32],
        rows: &[Row],
    ) -> Vec<Step> {
        let (mut i, mut j) = (a.len(), b.len());
        let mut out = Vec::with_capacity(i + j);
        let get = |i: usize, j: usize| rows[i].at(j);
        while i > 0 || j > 0 {
            let here = get(i, j);
            if i > 0 && j > 0 {
                let diag = get(i - 1, j - 1);
                if diag < INF {
                    if self.eq(a[i - 1], b[j - 1]) && diag == here {
                        out.push(Step::Pair(i - 1, j - 1));
                        i -= 1;
                        j -= 1;
                        continue;
                    }
                    let lbound = if self.cfg.threshold {
                        diag + sa[i - 1].abs_diff(sb[j - 1])
                    } else {
                        diag
                    };
                    if lbound <= here && diag + self.dist(a[i - 1], b[j - 1]) == here {
                        out.push(Step::Pair(i - 1, j - 1));
                        i -= 1;
                        j -= 1;
                        continue;
                    }
                }
            }
            if i > 0 && get(i - 1, j).saturating_add(sa[i - 1]) == here {
                out.push(Step::Del(i - 1));
                i -= 1;
            } else {
                assert!(
                    j > 0 && get(i, j - 1).saturating_add(sb[j - 1]) == here,
                    "trace invariant"
                );
                out.push(Step::Ins(j - 1));
                j -= 1;
            }
        }
        out.reverse();
        out
    }

    fn edit(&mut self, x: Id, y: Id) -> Edit {
        if self.eq(x, y) {
            return Edit::Keep(x);
        }
        let (ka, kb) = (self.arena.kids(x), self.arena.kids(y));
        let al = self.align(ka, kb);
        let kids = al
            .steps
            .iter()
            .map(|st| match *st {
                Step::Pair(i, j) => self.edit(ka[i], kb[j]),
                Step::Del(i) => Edit::Del(ka[i]),
                Step::Ins(j) => Edit::Ins(kb[j]),
            })
            .collect();
        Edit::Upd {
            from: x,
            to_label: self.arena.label(y),
            kids,
        }
    }
}

/// The recursive pair cost for `kernel::fill`.
struct Pairs<'d, 'a> {
    d: &'d mut Differ<'a>,
    a: &'a [Id],
    b: &'a [Id],
}

impl Oracle for Pairs<'_, '_> {
    fn pair_cost(&mut self, i: usize, j: usize) -> u32 {
        self.d.dist(self.a[i], self.b[j])
    }

    fn same(&self, i: usize, j: usize) -> bool {
        self.d.eq(self.a[i], self.b[j])
    }
}

/// Cost of a script: nodes deleted, nodes inserted, labels changed.
#[must_use]
pub fn cost(arena: &Arena, e: &Edit) -> u32 {
    match e {
        Edit::Keep(_) => 0,
        Edit::Del(x) | Edit::Ins(x) => arena.size(*x),
        Edit::Upd {
            from,
            to_label,
            kids,
        } => {
            u32::from(arena.label(*from) != *to_label)
                + kids.iter().map(|k| cost(arena, k)).sum::<u32>()
        }
    }
}

/// Replay `edit` against `before`, rebuilding the after-tree.
///
/// # Errors
/// Returns a description when the script does not apply to `before`.
pub fn apply(arena: &mut Arena, before: Id, edit: &Edit) -> Result<Id, String> {
    match edit {
        Edit::Keep(x) => {
            if *x == before {
                Ok(before)
            } else {
                Err("keep does not match the before-node".into())
            }
        }
        Edit::Del(_) | Edit::Ins(_) => Err("delete or insert at a position with no parent".into()),
        Edit::Upd {
            from,
            to_label,
            kids,
        } => {
            if *from != before {
                return Err("update does not match the before-node".into());
            }
            let old: Vec<Id> = arena.kids(before).to_vec();
            let mut cur = 0;
            let mut out: Vec<Id> = Vec::new();
            for k in kids {
                match k {
                    Edit::Ins(y) => out.push(*y),
                    Edit::Keep(x) | Edit::Del(x) => {
                        if old.get(cur) != Some(x) {
                            return Err("child does not match the before-child".into());
                        }
                        cur += 1;
                        if matches!(k, Edit::Keep(_)) {
                            out.push(*x);
                        }
                    }
                    Edit::Upd { from, .. } => {
                        let Some(&c) = old.get(cur) else {
                            return Err("child missing".into());
                        };
                        if c != *from {
                            return Err("update child does not match the before-child".into());
                        }
                        cur += 1;
                        out.push(apply(arena, c, k)?);
                    }
                }
            }
            if cur != old.len() {
                return Err("script leaves before-children unconsumed".into());
            }
            Ok(arena.mk(*to_label, &out))
        }
    }
}

/// Distance and script between two canonical trees, with the production configuration.
#[must_use]
pub fn diff(arena: &Arena, before: Id, after: Id) -> Diff {
    diff_with(arena, Config::PRODUCTION, before, after)
}

/// [`diff`] under an explicit [`Config`]. Every config computes the same distance.
#[must_use]
pub fn diff_with(arena: &Arena, cfg: Config, before: Id, after: Id) -> Diff {
    let mut d = Differ::new(arena, cfg);
    let cost_ = d.dist(before, after);
    let edit = d.edit(before, after);
    Diff {
        cost: cost_,
        edit,
        stats: d.stats,
    }
}

/// Distance only, no script. For timing the matcher without script construction.
#[must_use]
pub fn distance_with(arena: &Arena, cfg: Config, before: Id, after: Id) -> (u32, Stats) {
    let mut d = Differ::new(arena, cfg);
    let c = d.dist(before, after);
    (c, d.stats)
}

/// The admissible remaining-cost bound at `(i, j)` for two child lists, as the solver computes it.
#[must_use]
pub fn remaining_bound(arena: &Arena, a: &[Id], b: &[Id], i: usize, j: usize) -> u32 {
    let sa: Vec<u32> = a.iter().map(|&x| arena.size(x)).collect();
    let sb: Vec<u32> = b.iter().map(|&x| arena.size(x)).collect();
    bound(&suffix_sums(&sa), &suffix_sums(&sb), i, j)
}

/// Align two child lists with an explicit threshold. Returns `None` when no alignment of cost
/// `<= tau` exists, and otherwise the exact minimum cost (which is `<= tau`).
#[must_use]
pub fn align_within(arena: &Arena, a: &[Id], b: &[Id], tau: u32) -> Option<u32> {
    let mut d = Differ::new(arena, Config::PRODUCTION);
    let (n, m) = (a.len(), b.len());
    let mut p = 0;
    while p < n.min(m) && a[p] == b[p] {
        p += 1;
    }
    let mut s = 0;
    while s < n.min(m) - p && a[n - 1 - s] == b[m - 1 - s] {
        s += 1;
    }
    let (ma, mb) = (&a[p..n - s], &b[p..m - s]);
    let sa: Vec<u32> = ma.iter().map(|&x| arena.size(x)).collect();
    let sb: Vec<u32> = mb.iter().map(|&x| arena.size(x)).collect();
    if ma.is_empty() || mb.is_empty() {
        let c = sa.iter().sum::<u32>() + sb.iter().sum::<u32>();
        return (c <= tau).then_some(c);
    }
    let (ra, rb) = (suffix_sums(&sa), suffix_sums(&sb));
    let rows = d.fill(ma, mb, &sa, &sb, &ra, &rb, tau)?;
    Some(rows[ma.len()].at(mb.len()))
}

/// Distance and script if the distance is at most `tau`, else `None`.
#[must_use]
pub fn diff_within(arena: &Arena, before: Id, after: Id, tau: u32) -> Option<Diff> {
    let r = diff(arena, before, after);
    (r.cost <= tau).then_some(r)
}

/// [`diff`], then enforce `C3`: the script replays to the after-tree and costs exactly the distance.
///
/// # Panics
/// Panics if either contract is violated.
pub fn diff_checked(arena: &mut Arena, before: Id, after: Id) -> Diff {
    let r = diff(arena, before, after);
    assert_eq!(
        cost(arena, &r.edit),
        r.cost,
        "C3: script cost differs from distance"
    );
    let rebuilt = apply(arena, before, &r.edit).expect("C3: script does not apply");
    assert_eq!(rebuilt, after, "C3: script does not rebuild the after-tree");
    r
}
