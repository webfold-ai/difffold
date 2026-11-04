//! Extraction root for Charon and Aeneas: the pure helper core of `src/lines.rs` and the copies of `src/ted.rs` in `extract/ted_core.rs`.
//! The real files are included by `#[path]`; `lines_core` is the one verbatim-with-two-rewrites copy
//! (see its header). `ted_core` holds faithful copies of four functions of `src/ted.rs` (see its header).
#[path = "../../src/lines.rs"]
pub mod lines;
#[path = "../extract/lines_core.rs"]
pub mod lines_core;

#[path = "../extract/ted_core.rs"]
pub mod ted_core;
