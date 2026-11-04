//! Unified-diff output for the line differ.
//!
//! This module is output formatting. It is deliberately ordinary code (loops allowed); the
//! recursion-only discipline applies to the algorithm in [`crate::lines`]. The contract is
//! `git apply(old, unified(old, new)) == new` and `git apply --reverse(new, patch) == old`, not
//! byte equality with Git's own hunk placement.

use crate::lines::{diff_text_with, split_lines, Algo};

enum Op {
    Eq(usize, usize),
    Del(usize),
    Ins(usize),
}

/// Whether the file is modified, created or deleted.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// The file exists on both sides.
    Modify,
    /// The file is absent on the old side.
    Create,
    /// The file is absent on the new side.
    Delete,
}

/// `prefix` + `name`, quoted the way Git quotes paths with control characters, quotes, backslashes or
/// non-ASCII bytes: in double quotes, with C escapes and octal for the rest.
fn quote_path(prefix: &str, name: &str) -> String {
    let full = format!("{prefix}{name}");
    if !full.bytes().any(|b| b < 0x20 || b == 0x7f || b >= 0x80 || b == b'"' || b == b'\\') {
        return full;
    }
    let mut q = String::from("\"");
    for b in full.bytes() {
        match b {
            b'"' => q.push_str("\\\""),
            b'\\' => q.push_str("\\\\"),
            b'\t' => q.push_str("\\t"),
            b'\n' => q.push_str("\\n"),
            b'\r' => q.push_str("\\r"),
            0x20..=0x7e => q.push(b as char),
            _ => q.push_str(&format!("\\{b:03o}")),
        }
    }
    q.push('"');
    q
}

/// A `git apply`-able unified diff of `old` into `new` for a file called `name`, with `ctx` lines of
/// context. Returns an empty vector when the texts are equal.
#[must_use]
pub fn unified(old: &[u8], new: &[u8], name: &str, ctx: usize, algo: Algo) -> Vec<u8> {
    unified_with(old, new, name, ctx, algo, Kind::Modify, "100644")
}

/// Like [`unified`], for a file that may be created or deleted. `mode` is the file mode written on a
/// creation or deletion header, for example `100644`.
#[must_use]
pub fn unified_with(old: &[u8], new: &[u8], name: &str, ctx: usize, algo: Algo, kind: Kind, mode: &str) -> Vec<u8> {
    let d = diff_text_with(old, new, algo);
    let (la, lb) = (split_lines(old), split_lines(new));
    let mut ops = Vec::with_capacity(la.len().max(lb.len()));
    let (mut i, mut j) = (0, 0);
    while i < la.len() || j < lb.len() {
        if i < la.len() && d.deleted[i] {
            ops.push(Op::Del(i));
            i += 1;
        } else if j < lb.len() && d.inserted[j] {
            ops.push(Op::Ins(j));
            j += 1;
        } else {
            ops.push(Op::Eq(i, j));
            i += 1;
            j += 1;
        }
    }
    let changed: Vec<usize> = ops.iter().enumerate().filter(|(_, o)| !matches!(o, Op::Eq(..))).map(|(k, _)| k).collect();
    let mut w: Vec<u8> = Vec::new();
    if changed.is_empty() && kind == Kind::Modify {
        return w;
    }
    let (qa, qb) = (quote_path("a/", name), quote_path("b/", name));
    w.extend_from_slice(format!("diff --git {qa} {qb}\n").as_bytes());
    match kind {
        Kind::Modify => w.extend_from_slice(format!("--- {qa}\n+++ {qb}\n").as_bytes()),
        Kind::Create => {
            w.extend_from_slice(format!("new file mode {mode}\n").as_bytes());
            if !changed.is_empty() {
                w.extend_from_slice(format!("--- /dev/null\n+++ {qb}\n").as_bytes());
            }
        }
        Kind::Delete => {
            w.extend_from_slice(format!("deleted file mode {mode}\n").as_bytes());
            if !changed.is_empty() {
                w.extend_from_slice(format!("--- {qa}\n+++ /dev/null\n").as_bytes());
            }
        }
    }
    let mut s = 0;
    while s < changed.len() {
        let mut e = s;
        while e + 1 < changed.len() && changed[e + 1] - changed[e] - 1 <= 2 * ctx {
            e += 1;
        }
        let lo = changed[s].saturating_sub(ctx);
        let hi = (changed[e] + ctx + 1).min(ops.len());
        let (mut a0, mut b0, mut ac, mut bc) = (None, None, 0usize, 0usize);
        for op in &ops[lo..hi] {
            match op {
                Op::Eq(x, y) => {
                    a0.get_or_insert(*x);
                    b0.get_or_insert(*y);
                    ac += 1;
                    bc += 1;
                }
                Op::Del(x) => {
                    a0.get_or_insert(*x);
                    ac += 1;
                }
                Op::Ins(y) => {
                    b0.get_or_insert(*y);
                    bc += 1;
                }
            }
        }
        let first_a = a0.unwrap_or_else(|| ops[..lo].iter().filter(|o| !matches!(o, Op::Ins(_))).count());
        let first_b = b0.unwrap_or_else(|| ops[..lo].iter().filter(|o| !matches!(o, Op::Del(_))).count());
        let fa = if ac == 0 { first_a } else { first_a + 1 };
        let fb = if bc == 0 { first_b } else { first_b + 1 };
        w.extend_from_slice(format!("@@ -{fa},{ac} +{fb},{bc} @@\n").as_bytes());
        for op in &ops[lo..hi] {
            let (tag, line) = match op {
                Op::Eq(x, _) => (b' ', la[*x]),
                Op::Del(x) => (b'-', la[*x]),
                Op::Ins(y) => (b'+', lb[*y]),
            };
            w.push(tag);
            w.extend_from_slice(line);
            if line.last() != Some(&b'\n') {
                w.extend_from_slice(b"\n\\ No newline at end of file\n");
            }
        }
        s = e + 1;
    }
    w
}
