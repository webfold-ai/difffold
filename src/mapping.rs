//! Node-level correspondence recovered from an edit script.
//!
//! Hash-consed ids carry no position: two identical subtrees share one [`Id`]. Positions are
//! recovered the way [`crate::apply`] walks, by replaying the script against the two trees with
//! one preorder counter per side. Nothing is read from the arena except subtree sizes.
//!
//! Representation: a node is identified by its **preorder index** in its own tree (root is 0,
//! children in order, every node counted). For a tree built by converting a tree-sitter tree
//! with all children (named and anonymous), this is the preorder of the tree-sitter walk.
//!
//! * `Keep(x)` pairs the two subtrees node for node in preorder (identical shapes), kind
//!   [`PairKind::Identical`].
//! * `Upd` pairs its before-node with its after-node ([`PairKind::Relabel`] when the label
//!   changed, [`PairKind::Changed`] when only descendants changed) and recurses into the kids.
//! * `Del` / `Ins` advance one counter by the subtree size and produce no pair.
//!
//! Pairs come out in increasing order on both sides, since the objective is ordered and top-down:
//! a node is paired only when its parent is. Moves, wraps and unwraps cannot appear.

use crate::diff::Edit;
use crate::intern::Arena;

/// How a pair was produced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairKind {
    /// Inside a kept identical subtree.
    Identical,
    /// An updated node whose label changed.
    Relabel,
    /// An updated node with the same label whose descendants changed.
    Changed,
}

/// One before/after node pair, as preorder indices.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pair {
    /// Preorder index in the before-tree.
    pub before: u32,
    /// Preorder index in the after-tree.
    pub after: u32,
    /// Why the pair exists.
    pub kind: PairKind,
}

/// The correspondence implied by a script.
#[derive(Clone, Debug, Default)]
pub struct Correspondence {
    /// Pairs, increasing in both coordinates.
    pub pairs: Vec<Pair>,
    /// Nodes in the before-tree.
    pub before_len: u32,
    /// Nodes in the after-tree.
    pub after_len: u32,
}

impl Correspondence {
    /// `out[b]` is the after-index paired with before-node `b`, if any.
    #[must_use]
    pub fn before_to_after(&self) -> Vec<Option<u32>> {
        let mut out = vec![None; self.before_len as usize];
        for p in &self.pairs {
            out[p.before as usize] = Some(p.after);
        }
        out
    }
}

fn walk(arena: &Arena, e: &Edit, b: &mut u32, a: &mut u32, out: &mut Vec<Pair>) {
    match e {
        Edit::Keep(x) => {
            let s = arena.size(*x);
            out.extend((0..s).map(|k| Pair {
                before: *b + k,
                after: *a + k,
                kind: PairKind::Identical,
            }));
            *b += s;
            *a += s;
        }
        Edit::Del(x) => *b += arena.size(*x),
        Edit::Ins(y) => *a += arena.size(*y),
        Edit::Upd {
            from,
            to_label,
            kids,
        } => {
            let kind = if arena.label(*from) == *to_label {
                PairKind::Changed
            } else {
                PairKind::Relabel
            };
            out.push(Pair {
                before: *b,
                after: *a,
                kind,
            });
            *b += 1;
            *a += 1;
            for k in kids {
                walk(arena, k, b, a, out);
            }
        }
    }
}

/// The correspondence of `edit`, a script from `before` to `after` in `arena`.
#[must_use]
pub fn correspondence(
    arena: &Arena,
    before: crate::Id,
    after: crate::Id,
    edit: &Edit,
) -> Correspondence {
    let (mut b, mut a) = (0, 0);
    let mut pairs = Vec::new();
    walk(arena, edit, &mut b, &mut a, &mut pairs);
    debug_assert_eq!(b, arena.size(before));
    debug_assert_eq!(a, arena.size(after));
    Correspondence {
        pairs,
        before_len: arena.size(before),
        after_len: arena.size(after),
    }
}
