//! Exact hash-consing arena.
//!
//! Invariant `I1` (structural identity): for any two nodes `x`, `y` built by one [`Arena`],
//! `x == y` as [`Id`]s **iff** their labels are equal and their child id lists are equal. This
//! holds unconditionally. The 64-bit fold only chooses a bucket; every candidate in the bucket is
//! confirmed against the stored label and children before an id is reused, so a fold collision
//! costs one extra compare and can never alias two different nodes. There is no 2^-64 term.
//!
//! By induction on children, `I1` makes id equality equal to deep structural equality, which is
//! what lets every later stage compare subtrees in O(1) and key memo tables by id pair.

use apeiron::map::table::{Table, WordHome};

/// A canonical node. Equal ids mean structurally equal subtrees (`I1`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Id(pub u32);

const NIL: u32 = u32::MAX;
const PHI: u64 = 0x9E37_79B9_7F4A_7C15;

/// The hash-consed forest.
pub struct Arena {
    fold_fn: fn(u32, &[Id]) -> u64,
    label: Vec<u32>,
    span: Vec<(u32, u32)>,
    kids: Vec<Id>,
    size: Vec<u32>,
    chain: Vec<u32>,
    /// Bucket to chain head. Total-default: an absent bucket reads as `NIL` (apeiron's certified
    /// `Table`, whose canonical object is `Apeiron.Table.HMap`).
    head: Table<i64, i64, WordHome>,
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

fn fold(label: u32, kids: &[Id]) -> u64 {
    let mut h = u64::from(label).wrapping_mul(PHI) ^ (kids.len() as u64);
    for k in kids {
        h = (h.rotate_left(23) ^ u64::from(k.0)).wrapping_mul(PHI);
    }
    h ^ (h >> 29)
}

impl Arena {
    /// An empty arena.
    #[must_use]
    pub fn new() -> Self {
        Self::with_fold(fold)
    }

    /// An empty arena with a caller-chosen bucket function. Identity (I1) must hold for **any**
    /// function, including a constant one; tests inject one to force every node into one chain.
    #[must_use]
    pub fn with_fold(fold_fn: fn(u32, &[Id]) -> u64) -> Self {
        Self {
            fold_fn,
            label: Vec::new(),
            span: Vec::new(),
            kids: Vec::new(),
            size: Vec::new(),
            chain: Vec::new(),
            head: Table::new(i64::from(NIL), WordHome),
        }
    }

    /// Number of distinct nodes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.label.len()
    }

    /// True when no node has been built.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.label.is_empty()
    }

    /// The canonical node with this label and these children.
    ///
    /// # Panics
    /// Panics if the arena would exceed `u32::MAX - 1` nodes.
    pub fn mk(&mut self, label: u32, kids: &[Id]) -> Id {
        let h = (self.fold_fn)(label, kids);
        let key = h as i64;
        let mut cur = u32::try_from(*self.head.get(&key)).expect("chain head is a node id");
        while cur != NIL {
            let i = cur as usize;
            if self.label[i] == label && self.kids_of(i) == kids {
                return Id(cur);
            }
            cur = self.chain[i];
        }
        let id = u32::try_from(self.label.len()).expect("arena overflow");
        assert!(id != NIL, "arena overflow");
        let start = u32::try_from(self.kids.len()).expect("arena overflow");
        self.kids.extend_from_slice(kids);
        let size = 1 + kids.iter().map(|k| self.size[k.0 as usize]).sum::<u32>();
        let prev = u32::try_from(*self.head.get(&key)).expect("chain head is a node id");
        self.label.push(label);
        self.span.push((start, u32::try_from(kids.len()).expect("arena overflow")));
        self.size.push(size);
        self.chain.push(prev);
        // Last write wins: the new node becomes the chain head. The merge is new-first, so
        // `|new, _old| new`. A storage refusal leaves the table unchanged; panicking keeps I1 true
        // of every id that is returned, because the new node is then never returned.
        self.head.insert_with(&|new: i64, _old: i64| new, key, i64::from(id)).expect("head table refused an insert");
        Id(id)
    }

    fn kids_of(&self, i: usize) -> &[Id] {
        let (s, n) = self.span[i];
        &self.kids[s as usize..(s + n) as usize]
    }

    /// Deep structural equality by recursion over labels and children, never consulting ids.
    /// Under I1 this agrees with `x == y`; it exists so the id shortcut can be switched off in
    /// ablations and checked against the shortcut.
    #[must_use]
    pub fn deep_eq(&self, x: Id, y: Id) -> bool {
        self.label(x) == self.label(y)
            && self.kids(x).len() == self.kids(y).len()
            && self.kids(x).iter().zip(self.kids(y)).all(|(&p, &q)| self.deep_eq(p, q))
    }

    /// Label of a node.
    #[must_use]
    pub fn label(&self, id: Id) -> u32 {
        self.label[id.0 as usize]
    }

    /// Children of a node, in order.
    #[must_use]
    pub fn kids(&self, id: Id) -> &[Id] {
        self.kids_of(id.0 as usize)
    }

    /// Number of nodes in the subtree, counting the root.
    #[must_use]
    pub fn size(&self, id: Id) -> u32 {
        self.size[id.0 as usize]
    }
}
