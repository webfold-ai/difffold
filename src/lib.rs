//! `difffold`: ordered-tree diff on an exact hash-consed arena.
//!
//! The caveats of an anchor-and-window differ (hash collisions, anchors that are only a heuristic,
//! scripts that are only probably valid) are removed structurally, not mitigated:
//!
//! * [`intern`]: node identity is exact (`I1`). Equal ids if and only if equal subtrees.
//! * [`diff`]: the aligner is a banded DP whose result is accepted only when a lower bound on every
//!   path outside the band meets the band's cost (`C2`). Otherwise the band widens, up to the full
//!   DP. Heuristics choose the band, never the answer.
//! * [`diff::apply`]: every script is replayed against the before-tree and must rebuild the
//!   after-tree id for id, and its summed cost must equal the reported distance (`C3`).
//!
//! The contracts are stated in `SPEC.md` and exercised against an independent oracle in `tests/`.

#![forbid(unsafe_code)]

pub mod diff;
pub mod frontier;
pub mod intern;
pub mod kernel;
pub mod lines;
pub mod mapping;
pub mod merge;
pub mod ted;
pub mod unified;

pub use diff::{
    apply, diff, diff_checked, diff_with, distance_with, Config, Diff, Edit, Stats, Tau0,
};
pub use intern::{Arena, Id};
