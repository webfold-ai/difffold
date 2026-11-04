//! Extraction root for Charon and Aeneas.
//!
//! A development-only translation unit, not a crate of the library. It includes the real
//! `src/kernel.rs` by `#[path]`, so what is extracted is the source the library builds, not a
//! copy. Nothing is restated here.

#[path = "../../src/kernel.rs"]
pub mod kernel;
