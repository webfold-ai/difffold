//! Python and WebAssembly bindings for difffold.
//!
//! One small API, written once in [`api`] in plain Rust, with two thin front ends: a Python module
//! (PyO3, feature `python`) and a WebAssembly module (wasm-bindgen, feature `wasm`, which gives
//! TypeScript declarations). The surface is deliberately narrow and explicit: text, bytes, lists
//! and integers go in and out, never difffold's internal types.
//!
//! | Function | What it does |
//! |---|---|
//! | `diff_lines(old, new, algorithm)` | an ordered edit script: `equal`, `delete` and `insert` lines |
//! | `apply_edits(old, edits)` | replay a script on `old`, checking that it fits, and return the new text |
//! | `unified_patch(old, new, name, context, algorithm)` | a `git apply`-able unified diff |
//! | `merge3(base, left, right, algorithm)` | three-way line merge with conflict markers |
//! | `tree_distance(labels_a, parents_a, labels_b, parents_b, objective)` | ordered-tree edit distance, top-down or general |
//!
//! Not exposed: tree edit scripts and mappings (the `ted` engine reports postorder indices, and
//! translating them is a design decision rather than a binding), cost models, and the experimental
//! aligners.

#![warn(missing_docs)]

pub mod api;

#[cfg(feature = "python")]
mod python;

#[cfg(feature = "wasm")]
mod wasm;
