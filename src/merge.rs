//! Three-way line merge on the exact line differ (diff3 semantics).
//!
//! Output layer: ordinary code, loops allowed. The alignment comes from [`crate::lines`].
//! A base line kept by both sides is a *stable* line. The text between two consecutive stable lines is
//! a chunk with a base version `B`, a left version `L` and a right version `R`:
//! if `L == B` take `R`; if `R == B` take `L`; if `L == R` take `L`; otherwise it is a conflict.

use crate::lines::{diff_text_with, split_lines, Algo};

/// The result of a three-way merge.
pub struct Merged {
    /// Merged text, with conflict markers where the sides disagree.
    pub text: Vec<u8>,
    /// Number of conflicting chunks.
    pub conflicts: usize,
}

/// For each base line, its line index on the other side if it is kept, else `None`.
fn kept_map(base: &[u8], other: &[u8], algo: Algo) -> Vec<Option<usize>> {
    let d = diff_text_with(base, other, algo);
    let mut out = Vec::with_capacity(d.deleted.len());
    let mut j = 0;
    for &del in &d.deleted {
        if del {
            out.push(None);
        } else {
            while j < d.inserted.len() && d.inserted[j] {
                j += 1;
            }
            out.push(Some(j));
            j += 1;
        }
    }
    out
}

fn push_lines(out: &mut Vec<u8>, lines: &[&[u8]]) {
    for l in lines {
        out.extend_from_slice(l);
    }
}

fn ensure_newline(out: &mut Vec<u8>) {
    if !out.is_empty() && out[out.len() - 1] != b'\n' {
        out.push(b'\n');
    }
}

/// Merge `left` and `right`, both edits of `base`.
#[must_use]
pub fn merge3(base: &[u8], left: &[u8], right: &[u8], algo: Algo) -> Merged {
    let (bl, ll, rl) = (split_lines(base), split_lines(left), split_lines(right));
    let (ml, mr) = (kept_map(base, left, algo), kept_map(base, right, algo));
    let mut out = Vec::new();
    let mut conflicts = 0;
    // (base, left, right) index of the previous stable line; usize::MAX stands for "before the start".
    let (mut pb, mut pl, mut pr) = (usize::MAX, usize::MAX, usize::MAX);
    let next = |x: usize| x.wrapping_add(1);
    let chunk = |out: &mut Vec<u8>,
                 b0: usize,
                 b1: usize,
                 l0: usize,
                 l1: usize,
                 r0: usize,
                 r1: usize,
                 conflicts: &mut usize| {
        let (b, l, r) = (&bl[b0..b1], &ll[l0..l1], &rl[r0..r1]);
        if l == b {
            push_lines(out, r);
        } else if r == b || l == r {
            push_lines(out, l);
        } else {
            *conflicts += 1;
            ensure_newline(out);
            out.extend_from_slice(b"<<<<<<< left\n");
            push_lines(out, l);
            ensure_newline(out);
            out.extend_from_slice(b"=======\n");
            push_lines(out, r);
            ensure_newline(out);
            out.extend_from_slice(b">>>>>>> right\n");
        }
    };
    for i in 0..bl.len() {
        if let (Some(l), Some(r)) = (ml[i], mr[i]) {
            chunk(
                &mut out,
                next(pb),
                i,
                next(pl),
                l,
                next(pr),
                r,
                &mut conflicts,
            );
            out.extend_from_slice(bl[i]);
            (pb, pl, pr) = (i, l, r);
        }
    }
    chunk(
        &mut out,
        next(pb),
        bl.len(),
        next(pl),
        ll.len(),
        next(pr),
        rl.len(),
        &mut conflicts,
    );
    Merged {
        text: out,
        conflicts,
    }
}
