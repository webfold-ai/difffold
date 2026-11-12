//! The API both front ends wrap.

use std::collections::HashMap;
use std::fmt;

use difffold::diff::diff;
use difffold::intern::{Arena, Id};
use difffold::lines::{diff_text_with, replay_ok, split_lines, Algo};
use difffold::merge::merge3 as merge3_lines;
use difffold::ted::{ted, PostTree};
use difffold::unified::unified;

/// The most nodes a tree may have. The tree engines are polynomial in the node count, so an
/// unbounded tree from an untrusted caller is a way to burn unbounded time and memory.
pub const MAX_TREE_NODES: usize = 20_000;

/// The deepest a tree may be. The tree engines recurse over the tree, so depth is stack depth, and
/// a WebAssembly stack is small (1 MiB by default). Measured on a 1 MiB stack, the deepest chain
/// that completed was about 207 levels for `top-down` and 860 for `general` in an unoptimised build,
/// and about 1,030 and 4,090 optimised. 128 keeps a margin under the worst of those.
pub const MAX_TREE_DEPTH: usize = 128;

/// Why a call failed. The text is meant for a person.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiError(String);

impl ApiError {
    fn new(msg: impl Into<String>) -> Self {
        Self(msg.into())
    }
}

impl fmt::Display for ApiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ApiError {}

/// The crate version.
#[must_use]
pub fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

/// What an edit does to a line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EditKind {
    /// The line is in both texts.
    Equal,
    /// The line is only in the old text.
    Delete,
    /// The line is only in the new text.
    Insert,
}

impl EditKind {
    /// The name the front ends use: `equal`, `delete` or `insert`.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Equal => "equal",
            Self::Delete => "delete",
            Self::Insert => "insert",
        }
    }

    /// The inverse of [`name`](Self::name).
    ///
    /// # Errors
    /// Any other string.
    pub fn parse(s: &str) -> Result<Self, ApiError> {
        match s {
            "equal" => Ok(Self::Equal),
            "delete" => Ok(Self::Delete),
            "insert" => Ok(Self::Insert),
            other => Err(ApiError::new(format!(
                "unknown edit {other:?}; expected equal, delete or insert"
            ))),
        }
    }
}

/// One step of an edit script: a line, with its terminator, and what happens to it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edit {
    /// What the edit does.
    pub kind: EditKind,
    /// The line's bytes, including its `\n` unless it is the last line of a text without one.
    pub line: Vec<u8>,
}

fn algo(name: &str) -> Result<Algo, ApiError> {
    match name.trim().to_ascii_lowercase().as_str() {
        "minimal" | "myers" => Ok(Algo::Minimal),
        "histogram" => Ok(Algo::Histogram),
        other => Err(ApiError::new(format!(
            "unknown algorithm {other:?}; expected minimal or histogram"
        ))),
    }
}

/// An ordered edit script from `old` to `new`. Deletions come before the insertions that replace
/// them. `minimal` returns the fewest deleted plus inserted lines; `histogram` is faster on some
/// inputs and valid, but not minimal.
///
/// The result is replayed before it is returned: keeping the `equal` and `delete` lines gives
/// `old`, keeping the `equal` and `insert` lines gives `new`.
///
/// # Errors
/// An unknown algorithm name, or (a bug) a script that does not replay.
pub fn diff_lines(old: &[u8], new: &[u8], algorithm: &str) -> Result<Vec<Edit>, ApiError> {
    let d = diff_text_with(old, new, algo(algorithm)?);
    if !replay_ok(old, new, &d) {
        return Err(ApiError::new(
            "internal error: the line diff does not replay",
        ));
    }
    let (la, lb) = (split_lines(old), split_lines(new));
    let mut out = Vec::with_capacity(la.len().max(lb.len()));
    let (mut i, mut j) = (0, 0);
    while i < la.len() || j < lb.len() {
        if i < la.len() && d.deleted[i] {
            out.push(Edit {
                kind: EditKind::Delete,
                line: la[i].to_vec(),
            });
            i += 1;
        } else if j < lb.len() && d.inserted[j] {
            out.push(Edit {
                kind: EditKind::Insert,
                line: lb[j].to_vec(),
            });
            j += 1;
        } else {
            out.push(Edit {
                kind: EditKind::Equal,
                line: la[i].to_vec(),
            });
            i += 1;
            j += 1;
        }
    }
    Ok(out)
}

/// Replay `edits` on `old` and return the new text.
///
/// # Errors
/// The script does not fit `old`: an `equal` or `delete` line differs from the next line of `old`,
/// or the script ends before `old` does.
pub fn apply_edits(old: &[u8], edits: &[Edit]) -> Result<Vec<u8>, ApiError> {
    let lines = split_lines(old);
    let mut at = 0;
    let mut out = Vec::with_capacity(old.len());
    for (n, e) in edits.iter().enumerate() {
        match e.kind {
            EditKind::Insert => out.extend_from_slice(&e.line),
            EditKind::Equal | EditKind::Delete => {
                match lines.get(at) {
                    Some(l) if *l == e.line.as_slice() => {}
                    Some(_) => {
                        return Err(ApiError::new(format!(
                            "edit {n} ({}) does not match line {} of the old text",
                            e.kind.name(),
                            at + 1
                        )))
                    }
                    None => {
                        return Err(ApiError::new(format!(
                            "edit {n} ({}) is past the end of the old text",
                            e.kind.name()
                        )))
                    }
                }
                at += 1;
                if e.kind == EditKind::Equal {
                    out.extend_from_slice(&e.line);
                }
            }
        }
    }
    if at != lines.len() {
        return Err(ApiError::new(format!(
            "the script stops after {at} of {} old lines",
            lines.len()
        )));
    }
    Ok(out)
}

/// A unified diff of `old` into `new` for a file called `name`, with `context` lines of context,
/// that `git apply` accepts (and `git apply --reverse` undoes). Empty when the texts are equal.
///
/// # Errors
/// An unknown algorithm name.
pub fn unified_patch(
    old: &[u8],
    new: &[u8],
    name: &str,
    context: usize,
    algorithm: &str,
) -> Result<Vec<u8>, ApiError> {
    Ok(unified(old, new, name, context, algo(algorithm)?))
}

/// The result of [`merge3`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Merge {
    /// The merged text, with conflict markers where the sides disagree.
    pub text: Vec<u8>,
    /// How many conflicting chunks there are.
    pub conflicts: usize,
}

/// Merge `left` and `right`, both edits of `base`, line by line.
///
/// # Errors
/// An unknown algorithm name.
pub fn merge3(base: &[u8], left: &[u8], right: &[u8], algorithm: &str) -> Result<Merge, ApiError> {
    let m = merge3_lines(base, left, right, algo(algorithm)?);
    Ok(Merge {
        text: m.text,
        conflicts: m.conflicts,
    })
}

/// Which tree distance to compute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Objective {
    /// Top-down (Selkow): a node can match only if its parent does; deleting or inserting a subtree
    /// costs its size; relabelling costs 1; the roots always pair.
    TopDown,
    /// General ordered-tree edit distance (Zhang-Shasha): deleting a node promotes its children, so
    /// matches can cross levels. With unit costs it is never larger than the top-down distance.
    General,
}

fn objective(name: &str) -> Result<Objective, ApiError> {
    match name.trim().to_ascii_lowercase().as_str() {
        "top-down" | "topdown" | "selkow" => Ok(Objective::TopDown),
        "general" | "zhang-shasha" | "ted" => Ok(Objective::General),
        other => Err(ApiError::new(format!(
            "unknown objective {other:?}; expected top-down or general"
        ))),
    }
}

/// Build one tree in `arena` from preorder `labels` and `parents` (`parents[0]` is `-1`; every other
/// parent is an earlier node). Labels are interned through `ids`, which both trees share so equal
/// labels get equal ids.
fn build(
    arena: &mut Arena,
    ids: &mut HashMap<String, u32>,
    labels: &[String],
    parents: &[i32],
    which: &str,
) -> Result<Id, ApiError> {
    let n = labels.len();
    if n == 0 {
        return Err(ApiError::new(format!("tree {which} has no nodes")));
    }
    if n != parents.len() {
        return Err(ApiError::new(format!(
            "tree {which}: {n} labels but {} parents",
            parents.len()
        )));
    }
    if n > MAX_TREE_NODES {
        return Err(ApiError::new(format!(
            "tree {which} has {n} nodes; the limit is {MAX_TREE_NODES}"
        )));
    }
    if parents[0] != -1 {
        return Err(ApiError::new(format!(
            "tree {which}: node 0 must be the root (parent -1)"
        )));
    }
    let mut depth = vec![0usize; n];
    let mut kids: Vec<Vec<usize>> = vec![Vec::new(); n];
    for i in 1..n {
        let p = usize::try_from(parents[i])
            .ok()
            .filter(|p| *p < i)
            .ok_or_else(|| {
                ApiError::new(format!(
                    "tree {which}: node {i} has parent {}, but a parent must be an earlier node",
                    parents[i]
                ))
            })?;
        depth[i] = depth[p] + 1;
        if depth[i] > MAX_TREE_DEPTH {
            return Err(ApiError::new(format!(
                "tree {which} is deeper than {MAX_TREE_DEPTH} levels"
            )));
        }
        kids[p].push(i);
    }
    // Children have larger preorder indices than their parent, so walking backwards builds every
    // child before the node that needs it.
    let mut made: Vec<Option<Id>> = vec![None; n];
    for i in (0..n).rev() {
        let next =
            u32::try_from(ids.len()).map_err(|_| ApiError::new("too many distinct labels"))?;
        let label = *ids.entry(labels[i].clone()).or_insert(next);
        let child_ids: Vec<Id> = kids[i].iter().filter_map(|k| made[*k]).collect();
        made[i] = Some(arena.mk(label, &child_ids));
    }
    made[0].ok_or_else(|| ApiError::new("internal error: no root"))
}

/// The edit distance between two ordered, labelled trees, each given as preorder `labels` and
/// `parents` (the index of each node's parent; `-1` for the root at index 0). Children keep the
/// order of their indices.
///
/// # Errors
/// An unknown objective; a tree that is empty, malformed, larger than [`MAX_TREE_NODES`] or deeper
/// than [`MAX_TREE_DEPTH`].
pub fn tree_distance(
    labels_a: &[String],
    parents_a: &[i32],
    labels_b: &[String],
    parents_b: &[i32],
    objective_name: &str,
) -> Result<u32, ApiError> {
    let obj = objective(objective_name)?;
    let mut arena = Arena::new();
    let mut ids = HashMap::new();
    let a = build(&mut arena, &mut ids, labels_a, parents_a, "a")?;
    let b = build(&mut arena, &mut ids, labels_b, parents_b, "b")?;
    Ok(match obj {
        Objective::TopDown => diff(&arena, a, b).cost,
        Objective::General => ted(
            &PostTree::from_arena(&arena, a),
            &PostTree::from_arena(&arena, b),
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small deterministic generator: no dependency, and a failing seed can be replayed.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn text(rng: &mut Rng, lines: u64, alphabet: u64, final_newline: bool) -> Vec<u8> {
        let mut t = Vec::new();
        for i in 0..lines {
            t.extend_from_slice(format!("line {}", rng.below(alphabet)).as_bytes());
            if i + 1 < lines || final_newline {
                t.push(b'\n');
            }
        }
        t
    }

    /// The fewest deleted plus inserted lines, by the textbook LCS table.
    fn minimal_cost(a: &[u8], b: &[u8]) -> usize {
        let (la, lb) = (split_lines(a), split_lines(b));
        let mut dp = vec![vec![0usize; lb.len() + 1]; la.len() + 1];
        for i in 1..=la.len() {
            for j in 1..=lb.len() {
                dp[i][j] = if la[i - 1] == lb[j - 1] {
                    dp[i - 1][j - 1] + 1
                } else {
                    dp[i - 1][j].max(dp[i][j - 1])
                };
            }
        }
        la.len() + lb.len() - 2 * dp[la.len()][lb.len()]
    }

    fn cost(edits: &[Edit]) -> usize {
        edits.iter().filter(|e| e.kind != EditKind::Equal).count()
    }

    #[test]
    fn scripts_replay_and_the_minimal_one_is_minimal() {
        let mut rng = Rng(7);
        for round in 0..400 {
            let (na, nb) = (rng.below(25), rng.below(25));
            let a = text(&mut rng, na, 6, round % 3 != 0);
            let b = text(&mut rng, nb, 6, round % 4 != 0);
            for name in ["minimal", "histogram"] {
                let e = diff_lines(&a, &b, name).expect("diff");
                assert_eq!(
                    apply_edits(&a, &e).expect("replay"),
                    b,
                    "{name} round {round}"
                );
                // The same script read the other way gives the old text back.
                let old: Vec<u8> = e
                    .iter()
                    .filter(|x| x.kind != EditKind::Insert)
                    .flat_map(|x| x.line.clone())
                    .collect();
                assert_eq!(old, a);
            }
            let m = diff_lines(&a, &b, "minimal").expect("diff");
            assert_eq!(cost(&m), minimal_cost(&a, &b), "round {round}");
            assert!(cost(&diff_lines(&a, &b, "histogram").expect("diff")) >= cost(&m));
        }
    }

    #[test]
    fn deletions_come_before_the_insertions_that_replace_them() {
        let e = diff_lines(b"a\nb\nc\n", b"a\nX\nc\n", "minimal").expect("diff");
        let kinds: Vec<_> = e.iter().map(|x| x.kind.name()).collect();
        assert_eq!(kinds, ["equal", "delete", "insert", "equal"]);
        assert_eq!(e[1].line, b"b\n");
        assert_eq!(e[2].line, b"X\n");
    }

    #[test]
    fn a_missing_final_newline_is_kept_exactly() {
        let e = diff_lines(b"a\nb", b"a\nb\n", "minimal").expect("diff");
        assert_eq!(apply_edits(b"a\nb", &e).expect("replay"), b"a\nb\n");
        assert_eq!(cost(&e), 2, "b and b\\n are different lines");
    }

    #[test]
    fn empty_and_equal_inputs() {
        assert!(diff_lines(b"", b"", "minimal").expect("diff").is_empty());
        let e = diff_lines(b"", b"x\ny\n", "minimal").expect("diff");
        assert_eq!(cost(&e), 2);
        assert_eq!(apply_edits(b"", &e).expect("replay"), b"x\ny\n");
        let e = diff_lines(b"x\ny\n", b"", "histogram").expect("diff");
        assert_eq!(apply_edits(b"x\ny\n", &e).expect("replay"), b"");
        let same = diff_lines(b"p\nq\n", b"p\nq\n", "minimal").expect("diff");
        assert_eq!(cost(&same), 0);
        assert!(unified_patch(b"p\n", b"p\n", "f", 3, "minimal")
            .expect("patch")
            .is_empty());
    }

    #[test]
    fn binary_and_non_utf8_bytes_survive() {
        let a: &[u8] = b"\xff\xfe\n\x00\x01\nplain\n";
        let b: &[u8] = b"\xff\xfe\n\x00\x02\nplain\n";
        let e = diff_lines(a, b, "minimal").expect("diff");
        assert_eq!(apply_edits(a, &e).expect("replay"), b);
    }

    #[test]
    fn apply_edits_rejects_a_script_that_does_not_fit() {
        let e = diff_lines(b"a\nb\n", b"a\nc\n", "minimal").expect("diff");
        assert!(apply_edits(b"a\nZ\n", &e)
            .unwrap_err()
            .to_string()
            .contains("does not match line 2"));
        assert!(apply_edits(b"a\n", &e)
            .unwrap_err()
            .to_string()
            .contains("past the end"));
        assert!(apply_edits(b"a\nb\nextra\n", &e)
            .unwrap_err()
            .to_string()
            .contains("stops after 2 of 3"));
    }

    #[test]
    fn a_large_input_is_handled() {
        let mut rng = Rng(99);
        let a = text(&mut rng, 60_000, 5_000, true);
        let mut b = a.clone();
        b.extend_from_slice(b"tail\n");
        let e = diff_lines(&a, &b, "minimal").expect("diff");
        assert_eq!(apply_edits(&a, &e).expect("replay"), b);
        assert_eq!(cost(&e), 1);
        let unrelated = text(&mut rng, 20_000, 3_000, true);
        let e = diff_lines(&a, &unrelated, "histogram").expect("diff");
        assert_eq!(apply_edits(&a, &e).expect("replay"), unrelated);
    }

    #[test]
    fn merge_takes_non_overlapping_edits_and_marks_conflicts() {
        let m = merge3(b"a\nb\nc\n", b"A\nb\nc\n", b"a\nb\nC\n", "minimal").expect("merge");
        assert_eq!(
            (m.text.as_slice(), m.conflicts),
            (b"A\nb\nC\n".as_slice(), 0)
        );
        let c = merge3(b"a\n", b"left\n", b"right\n", "minimal").expect("merge");
        assert_eq!(c.conflicts, 1);
        let s = String::from_utf8(c.text).expect("utf8");
        assert!(
            s.contains("left") && s.contains("right") && s.contains("<<<<<<<"),
            "{s}"
        );
    }

    #[test]
    fn unknown_names_say_what_is_valid() {
        assert!(diff_lines(b"", b"", "fast")
            .unwrap_err()
            .to_string()
            .contains("minimal or histogram"));
        assert!(EditKind::parse("move")
            .unwrap_err()
            .to_string()
            .contains("equal, delete or insert"));
        let t = vec!["a".to_owned()];
        assert!(tree_distance(&t, &[-1], &t, &[-1], "fast")
            .unwrap_err()
            .to_string()
            .contains("top-down or general"));
    }

    fn t(labels: &[&str], parents: &[i32]) -> (Vec<String>, Vec<i32>) {
        (
            labels.iter().map(|s| (*s).to_owned()).collect(),
            parents.to_vec(),
        )
    }

    fn dist(a: &(Vec<String>, Vec<i32>), b: &(Vec<String>, Vec<i32>), o: &str) -> u32 {
        tree_distance(&a.0, &a.1, &b.0, &b.1, o).expect("distance")
    }

    #[test]
    fn tree_distances_match_hand_computed_values() {
        let leaf = t(&["a"], &[-1]);
        assert_eq!(dist(&leaf, &leaf, "top-down"), 0);
        // a(b) against a(c): one relabel.
        let (ab, ac) = (t(&["a", "b"], &[-1, 0]), t(&["a", "c"], &[-1, 0]));
        assert_eq!(dist(&ab, &ac, "top-down"), 1);
        assert_eq!(dist(&ab, &ac, "general"), 1);
        // Wrapping: a(b) against a(c(b)). General inserts c once; top-down cannot match b under a
        // new parent, so it relabels b to c and inserts the b below it.
        let wrapped = t(&["a", "c", "b"], &[-1, 0, 1]);
        assert_eq!(dist(&ab, &wrapped, "general"), 1);
        assert_eq!(dist(&ab, &wrapped, "top-down"), 2);
        // Child order matters.
        let (xy, yx) = (
            t(&["r", "x", "y"], &[-1, 0, 0]),
            t(&["r", "y", "x"], &[-1, 0, 0]),
        );
        assert_eq!(dist(&xy, &yx, "general"), 2);
    }

    #[test]
    fn tree_distance_is_a_metric_on_random_trees_and_general_never_exceeds_top_down() {
        fn tree(rng: &mut Rng, n: usize) -> (Vec<String>, Vec<i32>) {
            let labels: Vec<String> = (0..n).map(|_| format!("l{}", rng.below(3))).collect();
            let mut parents = vec![-1];
            for i in 1..n {
                parents.push(rng.below(i as u64) as i32);
            }
            // A random parent array is not in preorder; renumber into preorder.
            let mut kids = vec![Vec::new(); n];
            for (i, p) in parents.iter().enumerate().skip(1) {
                kids[*p as usize].push(i);
            }
            let mut order = Vec::new();
            let mut stack = vec![0usize];
            while let Some(x) = stack.pop() {
                order.push(x);
                for k in kids[x].iter().rev() {
                    stack.push(*k);
                }
            }
            let pos: Vec<usize> = {
                let mut p = vec![0; n];
                for (i, x) in order.iter().enumerate() {
                    p[*x] = i;
                }
                p
            };
            let l = order.iter().map(|x| labels[*x].clone()).collect();
            let pr = order
                .iter()
                .map(|x| {
                    if *x == 0 {
                        -1
                    } else {
                        pos[parents[*x] as usize] as i32
                    }
                })
                .collect();
            (l, pr)
        }
        let mut rng = Rng(3);
        for _ in 0..150 {
            let (na, nb, nc) = (
                1 + rng.below(9) as usize,
                1 + rng.below(9) as usize,
                1 + rng.below(9) as usize,
            );
            let (a, b, c) = (tree(&mut rng, na), tree(&mut rng, nb), tree(&mut rng, nc));
            for o in ["top-down", "general"] {
                assert_eq!(dist(&a, &a, o), 0);
                assert_eq!(dist(&a, &b, o), dist(&b, &a, o), "{o} symmetric");
                assert!(
                    dist(&a, &c, o) <= dist(&a, &b, o) + dist(&b, &c, o),
                    "{o} triangle"
                );
            }
            assert!(dist(&a, &b, "general") <= dist(&a, &b, "top-down"));
            // Size bound: never more than deleting one tree and inserting the other.
            assert!(dist(&a, &b, "top-down") as usize <= a.0.len() + b.0.len());
        }
    }

    #[test]
    fn malformed_trees_are_errors_not_panics() {
        let ok = t(&["a", "b"], &[-1, 0]);
        let bad = |labels: &[&str], parents: &[i32]| {
            let x = t(labels, parents);
            tree_distance(&x.0, &x.1, &ok.0, &ok.1, "general")
                .unwrap_err()
                .to_string()
        };
        assert!(bad(&[], &[]).contains("no nodes"));
        assert!(bad(&["a"], &[-1, 0]).contains("1 labels but 2 parents"));
        assert!(bad(&["a", "b"], &[0, 0]).contains("must be the root"));
        assert!(bad(&["a", "b"], &[-1, 1]).contains("an earlier node"));
        assert!(bad(&["a", "b"], &[-1, -1]).contains("an earlier node"));
        assert!(bad(&["a", "b"], &[-1, 7]).contains("an earlier node"));
        assert!(bad(&["a", "b", "c"], &[-1, 0, i32::MIN]).contains("an earlier node"));
    }

    #[test]
    fn size_and_depth_limits_are_enforced_before_any_work() {
        let n = MAX_TREE_NODES + 1;
        let labels = vec!["x".to_owned(); n];
        let mut parents = vec![-1];
        parents.extend(std::iter::repeat_n(0, n - 1));
        let ok = t(&["a"], &[-1]);
        let e = tree_distance(&labels, &parents, &ok.0, &ok.1, "top-down")
            .unwrap_err()
            .to_string();
        assert!(e.contains("the limit is"), "{e}");
        // One level too deep.
        let d = MAX_TREE_DEPTH + 2;
        let labels = vec!["x".to_owned(); d];
        let parents: Vec<i32> = (0..d as i32).map(|i| i - 1).collect();
        let e = tree_distance(&labels, &parents, &ok.0, &ok.1, "top-down")
            .unwrap_err()
            .to_string();
        assert!(e.contains("deeper than"), "{e}");
    }

    #[test]
    fn the_deepest_allowed_tree_fits_a_one_mebibyte_stack() {
        // WebAssembly's default stack is 1 MiB; run on a thread with that much to prove the depth
        // limit leaves room.
        let h = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let d = MAX_TREE_DEPTH + 1;
                let labels: Vec<String> = (0..d).map(|i| format!("n{}", i % 3)).collect();
                let parents: Vec<i32> = (0..d as i32).map(|i| i - 1).collect();
                let other: Vec<String> = (0..d).map(|i| format!("n{}", (i + 1) % 3)).collect();
                for o in ["top-down", "general"] {
                    let v =
                        tree_distance(&labels, &parents, &other, &parents, o).expect("distance");
                    assert!(v > 0, "{o}");
                }
            })
            .expect("spawn");
        h.join().expect("no stack overflow");
    }
}
