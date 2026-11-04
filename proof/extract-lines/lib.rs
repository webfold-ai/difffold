//! Extraction root for Charon and Aeneas: the pure helper core of `src/lines.rs` and `src/ted.rs`.
//! The real files are included by `#[path]`; `lines_core` is the one verbatim-with-two-rewrites copy
//! (see its header). `ted` needs a shim for `crate::intern`, which is outside the extracted core.
#[path = "../../src/lines.rs"]
pub mod lines;
#[path = "../extract/lines_core.rs"]
pub mod lines_core;

/// Stand-in for `crate::intern`, which pulls in apeiron and is not part of the extracted core.
/// `ted.rs` uses only `Arena::{kids, label}` and `Id`, in `PostTree::from_arena` and `expand`, which are
/// not extraction roots.
pub mod intern {
    #[derive(Clone, Copy)]
    pub struct Id(pub u32);
    pub struct Arena;
    impl Arena {
        pub fn label(&self, _id: Id) -> u32 {
            0
        }
        pub fn kids(&self, _id: Id) -> &[Id] {
            &[]
        }
    }
}
#[path = "ted_nomax.rs"]
pub mod ted;

/// Stand-in for `.max(1)` on `usize`, see `extract-lines.sh`.
pub trait MaxOne {
    fn max_one(self) -> Self;
}
impl MaxOne for usize {
    fn max_one(self) -> usize {
        if self > 1 { self } else { 1 }
    }
}

/// Extraction root for the inherent method `PostTree::from_kids` (`--start-from` cannot name inherent
/// impl items).
pub fn root_from_kids(label: Vec<u32>, kids: &[Vec<u32>]) -> ted::PostTree {
    ted::PostTree::from_kids(label, kids)
}
