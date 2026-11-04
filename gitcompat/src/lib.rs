//! Git diff and patch compatibility for difffold.
//!
//! Two strictly separate things live here:
//!
//! * **Byte certificate** ([`patch`]): a standard unified patch such that applying it to the
//!   before-bytes yields the after-bytes exactly. Produced by an in-crate Myers line diff. This is
//!   what `git apply` consumes. It never depends on a parser.
//! * **Structural certificate** ([`structural`]): difffold's tree edit script replayed on the
//!   before-tree rebuilds the after-tree. This is for review only and implies nothing about bytes.
//!
//! This crate is diff and patch compatibility. It does not read or write Git objects, packs, refs
//! or the index, and it is not a Git server or client.

pub mod edge;
pub mod extdiff;
pub mod gitcheck;
pub mod myers;
pub mod patch;
pub mod structural;
