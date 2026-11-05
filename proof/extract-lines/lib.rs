//! Extraction root for Charon and Aeneas: the pure helper core of `src/lines.rs` and the real `src/ted.rs`.
//! The real files are included by `#[path]`; `lines_core` is the one verbatim-with-two-rewrites copy
//! (see its header). `src/ted.rs` is included unchanged.
#[path = "../../src/lines.rs"]
pub mod lines;
#[path = "../extract/lines_core.rs"]
pub mod lines_core;


/// Stand-in for `crate::intern`, which pulls in apeiron and is not part of the extracted core. `ted.rs` uses
/// only `Arena::{kids, label}` and `Id`, in `from_arena` and `expand`, which are not extraction roots.
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
/// The real `src/ted.rs`, included by `#[path]`.
#[path = "../../src/ted.rs"]
pub mod ted;

/// Extraction root for the inherent method `PostTree::from_kids` (`--start-from` cannot name inherent
/// impl items). A wrapper that only calls the real body.
pub fn root_from_kids(label: Vec<u32>, kids: &[Vec<u32>]) -> ted::PostTree {
    ted::PostTree::from_kids(label, kids)
}
