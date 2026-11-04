//! Extraction root for Charon and Aeneas: the pure pieces of the line search. The real `src/lines.rs` is
//! included by `#[path]`; `mcore` holds the closure-free copies (`extract/lines_core.rs` for the newline
//! helpers, `extract/myers_core.rs` for the search helpers), kept in one flat module so the files can also
//! be `include!`d by `tests/myers_core.rs`.
#[path = "../../src/lines.rs"]
pub mod lines;
pub mod mcore {
    include!("../extract/lines_core.rs");
    include!("../extract/myers_core.rs");
}
