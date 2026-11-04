//! The pure alignment kernel.
//!
//! This is the code that the proofs are about. It is the *only* implementation of the threshold DP:
//! `diff.rs` calls it, and `proof/extract/` includes this very file by `#[path]` for Charon, the
//! way apeiron's `proof/extract/lib.rs` includes the real source. Nothing here is a copy.
//!
//! The style is dictated by what Aeneas can translate: safe Rust, `while` loops with explicit
//! indices, no closures, no iterator adaptors, no `?`, no `min`/`abs_diff` methods. The recursive
//! pair cost is the only unknown, and it is a trait method, so a theorem about [`fill`] quantifies
//! over every oracle that satisfies the size bound.
//!
//! Preconditions the proofs must carry (they are not checked at run time in release builds): the
//! total size of both lists is below `2^28`, and `tau < INF`.

/// "Pruned or absent". Also an upper bound on every real cost.
pub const INF: u32 = 1_073_741_823;

/// The source of recursive pair costs. Indices are 0-based positions in the two child lists.
pub trait Oracle {
    /// The cost of pairing `a[i]` with `b[j]`: `dist(a[i], b[j])`.
    fn pair_cost(&mut self, i: usize, j: usize) -> u32;
    /// Whether `a[i]` and `b[j]` are the same subtree.
    fn same(&self, i: usize, j: usize) -> bool;
}

/// Work counters, copied into `Stats` by the caller. They are diagnostics: increments wrap, so no
/// proof about the kernel has to bound them.
#[derive(Clone, Copy, Debug, Default)]
pub struct Counters {
    /// Cells whose value was computed.
    pub cells: u64,
    /// Cells that were kept.
    pub kept: u64,
    /// Pair costs skipped by the size bound.
    pub pruned: u64,
}

/// One DP row: the kept cells `lo .. lo + v.len()`; everything else is pruned.
pub struct Row {
    /// First column held.
    pub lo: usize,
    /// Values; `INF` marks a pruned cell inside the span.
    pub v: Vec<u32>,
}

impl Row {
    /// The value at column `j`, or `INF` when the cell is pruned or outside the span.
    #[must_use]
    pub fn at(&self, j: usize) -> u32 {
        if j < self.lo {
            INF
        } else {
            let k = j - self.lo;
            if k < self.v.len() {
                self.v[k]
            } else {
                INF
            }
        }
    }
}

/// `|x - y|`.
#[must_use]
pub fn adiff(x: u32, y: u32) -> u32 {
    x.abs_diff(y)
}

/// The smaller of two values.
#[must_use]
pub fn umin(x: u32, y: u32) -> u32 {
    if x <= y {
        x
    } else {
        y
    }
}

/// `out[i]` is the sum of `x[i..]`, and `out[x.len()]` is 0: the reversed accumulation.
#[must_use]
pub fn suffix_sums(x: &[u32]) -> Vec<u32> {
    let n = x.len();
    let mut out: Vec<u32> = Vec::new();
    let mut k = 0;
    while k <= n {
        out.push(0);
        k += 1;
    }
    let mut i = n;
    while i > 0 {
        i -= 1;
        let s = out[i + 1] + x[i];
        out[i] = s;
    }
    out
}

/// The admissible remaining-cost bound `h(i, j) = |R_a(i) - R_b(j)|`.
#[must_use]
pub fn bound(ra: &[u32], rb: &[u32], i: usize, j: usize) -> u32 {
    adiff(ra[i], rb[j])
}

fn hh(ra: &[u32], rb: &[u32], on: bool, i: usize, j: usize) -> u32 {
    if on {
        bound(ra, rb, i, j)
    } else {
        0
    }
}

/// Row 0 of the DP: the cells `(0, j)` that fit under `tau`.
#[must_use]
pub fn first_row(sb: &[u32], ra: &[u32], rb: &[u32], on: bool, tau: u32) -> Row {
    let m = sb.len();
    let mut v0: Vec<u32> = Vec::new();
    v0.push(0);
    let mut j0 = 1;
    while j0 <= m {
        let f = v0[j0 - 1] + sb[j0 - 1];
        if f + hh(ra, rb, on, 0, j0) > tau {
            break;
        }
        v0.push(f);
        j0 += 1;
    }
    Row { lo: 0, v: v0 }
}

/// The delete candidate of cell `(i, j)`: the cell above plus the deleted child's size, or `INF`.
#[must_use]
pub fn del_cand(prev: &Row, j: usize, sa: &[u32], i: usize) -> u32 {
    let above = prev.at(j);
    if above < INF {
        above + sa[i - 1]
    } else {
        INF
    }
}

/// The insert candidate of cell `(i, j)`: the cell to the left plus the inserted child's size, or
/// `INF` for the first cell of the row. A pruned left neighbour yields a word `>= INF`.
#[must_use]
pub fn ins_cand(v: &[u32], j: usize, plo: usize, sb: &[u32]) -> u32 {
    if j > plo {
        v[v.len() - 1] + sb[j - 1]
    } else {
        INF
    }
}

/// The lower bound on the pair candidate: the diagonal predecessor plus the size difference when
/// pruning is on, and the predecessor alone otherwise.
#[must_use]
pub fn lower_bound(on: bool, diag: u32, sa_i: u32, sb_j: u32) -> u32 {
    if on {
        diag + adiff(sa_i, sb_j)
    } else {
        diag
    }
}

/// The diagonal stage of cell `(i, j)`: consider the pair candidate only when its lower bound can
/// win and can fit under `tau`. Skipping the recursive pair cost is invisible after the keep test
/// because the pair cost is at least the size difference.
#[allow(clippy::too_many_arguments)]
pub fn diag_stage<O: Oracle>(
    o: &mut O,
    prev: &Row,
    i: usize,
    j: usize,
    sa: &[u32],
    sb: &[u32],
    ra: &[u32],
    rb: &[u32],
    tau: u32,
    on: bool,
    best0: u32,
    c: &mut Counters,
) -> u32 {
    let mut best = best0;
    if j > 0 {
        let diag = prev.at(j - 1);
        if diag < INF {
            let lbound = lower_bound(on, diag, sa[i - 1], sb[j - 1]);
            if lbound < best {
                if lbound + hh(ra, rb, on, i, j) <= tau {
                    let sub = diag + o.pair_cost(i - 1, j - 1);
                    best = umin(best, sub);
                } else if !o.same(i - 1, j - 1) {
                    c.pruned = c.pruned.wrapping_add(1);
                }
            }
        }
    }
    best
}

/// The candidate value of cell `(i, j)` before the keep test: the least of delete, insert and pair.
/// `v` holds the cells of this row computed so far; `plo` is the first column of the row.
#[allow(clippy::too_many_arguments)]
pub fn cell_value<O: Oracle>(
    o: &mut O,
    prev: &Row,
    v: &[u32],
    i: usize,
    j: usize,
    plo: usize,
    sa: &[u32],
    sb: &[u32],
    ra: &[u32],
    rb: &[u32],
    tau: u32,
    on: bool,
    c: &mut Counters,
) -> u32 {
    let del = del_cand(prev, j, sa, i);
    let ins = ins_cand(v, j, plo, sb);
    let best0 = umin(del, ins);
    diag_stage(o, prev, i, j, sa, sb, ra, rb, tau, on, best0, c)
}

/// The word stored for a cell: its value when it is kept, `INF` when it is pruned.
#[must_use]
pub fn pick(kept: bool, best: u32) -> u32 {
    if kept {
        best
    } else {
        INF
    }
}

/// Count one computed cell, and one kept cell when `kept`. Counters are diagnostics and wrap.
#[must_use]
pub fn count_cell(c: Counters, kept: bool) -> Counters {
    let cells = c.cells.wrapping_add(1);
    let kept_n = if kept { c.kept.wrapping_add(1) } else { c.kept };
    Counters {
        cells,
        kept: kept_n,
        pruned: c.pruned,
    }
}

/// The raw cells of row `i`, starting at the previous row's first column. Pruned cells hold `INF`.
/// A cell is `min(delete, insert, pair)`, kept iff its value plus the bound fits under `tau`.
#[allow(clippy::too_many_arguments)]
pub fn row_cells<O: Oracle>(
    o: &mut O,
    prev: &Row,
    i: usize,
    sa: &[u32],
    sb: &[u32],
    ra: &[u32],
    rb: &[u32],
    tau: u32,
    on: bool,
    c: &mut Counters,
) -> Vec<u32> {
    let m = sb.len();
    let plo = prev.lo;
    let phi = plo + prev.v.len() - 1;
    let mut v: Vec<u32> = Vec::new();
    let mut j = plo;
    loop {
        let best = cell_value(o, prev, &v, i, j, plo, sa, sb, ra, rb, tau, on, c);
        let kept = best + hh(ra, rb, on, i, j) <= tau;
        *c = count_cell(*c, kept);
        let word = pick(kept, best);
        v.push(word);
        j += 1;
        let more_diag = j <= phi + 1;
        let more_ins = word < INF;
        if j > m || !(more_diag || more_ins) {
            break;
        }
    }
    v
}

/// Drop the pruned cells at both ends of a raw row, or `None` if every cell is pruned.
#[must_use]
pub fn trim_row(v: &[u32], plo: usize) -> Option<Row> {
    let mut first = 0;
    while first < v.len() && v[first] >= INF {
        first += 1;
    }
    if first == v.len() {
        None
    } else {
        let mut last = v.len() - 1;
        while v[last] >= INF {
            last -= 1;
        }
        let mut kept_row: Vec<u32> = Vec::new();
        let mut k = first;
        while k <= last {
            kept_row.push(v[k]);
            k += 1;
        }
        Some(Row {
            lo: plo + first,
            v: kept_row,
        })
    }
}

/// The threshold DP of `Differ::fill`. Returns `None` when no alignment of cost `<= tau` exists,
/// and otherwise every row, whose last cell holds the optimum. `on = false` keeps every cell.
///
/// `sa`, `sb` are the subtree sizes of the two lists; `ra`, `rb` their [`suffix_sums`].
#[allow(clippy::too_many_arguments)]
pub fn fill<O: Oracle>(
    o: &mut O,
    sa: &[u32],
    sb: &[u32],
    ra: &[u32],
    rb: &[u32],
    tau: u32,
    on: bool,
    c: &mut Counters,
) -> Option<Vec<Row>> {
    let n = sa.len();
    let m = sb.len();
    let mut rows: Vec<Row> = Vec::new();
    rows.push(first_row(sb, ra, rb, on, tau));
    let mut i = 1;
    let mut ok = true;
    while i <= n && ok {
        let plo = rows[i - 1].lo;
        let v = row_cells(o, &rows[i - 1], i, sa, sb, ra, rb, tau, on, c);
        match trim_row(&v, plo) {
            Some(r) => rows.push(r),
            None => ok = false,
        }
        i += 1;
    }
    if ok && rows[n].at(m) < INF {
        Some(rows)
    } else {
        None
    }
}
