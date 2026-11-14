//! The `difffold` Python module (PyO3).
//!
//! Text arguments are `str` or `bytes`, and every text argument of one call must be the same type;
//! text comes back as that type. `str` is UTF-8, and lines are split at `\n`, which never falls
//! inside a UTF-8 sequence, so a `str` input always gives `str` output.

use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyString};

use crate::api::{self, Edit, EditKind};

fn value_err(e: api::ApiError) -> PyErr {
    PyValueError::new_err(e.to_string())
}

/// Whether text came in as `str` (and so goes out as `str`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Str,
    Bytes,
}

fn text(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<(Vec<u8>, Kind)> {
    if let Ok(s) = obj.extract::<String>() {
        return Ok((s.into_bytes(), Kind::Str));
    }
    if obj.is_instance_of::<PyBytes>() {
        return Ok((obj.extract::<Vec<u8>>()?, Kind::Bytes));
    }
    Err(PyTypeError::new_err(format!("{what} must be str or bytes")))
}

fn same(a: Kind, b: Kind) -> PyResult<Kind> {
    if a == b {
        Ok(a)
    } else {
        Err(PyTypeError::new_err(
            "text arguments must all be str or all be bytes",
        ))
    }
}

fn out<'py>(py: Python<'py>, bytes: Vec<u8>, kind: Kind) -> PyResult<Bound<'py, PyAny>> {
    match kind {
        Kind::Bytes => Ok(PyBytes::new(py, &bytes).into_any()),
        Kind::Str => {
            let s = String::from_utf8(bytes)
                .map_err(|_| PyValueError::new_err("internal error: the result is not UTF-8"))?;
            Ok(PyString::new(py, &s).into_any())
        }
    }
}

/// An ordered edit script from `old` to `new`: a list of `(kind, line)` where `kind` is `"equal"`,
/// `"delete"` or `"insert"` and `line` includes its newline. `algorithm` is `"minimal"` (fewest
/// changed lines) or `"histogram"` (valid, not necessarily minimal).
#[pyfunction]
#[pyo3(signature = (old, new, algorithm = "minimal"))]
fn diff_lines<'py>(
    py: Python<'py>,
    old: &Bound<'py, PyAny>,
    new: &Bound<'py, PyAny>,
    algorithm: &str,
) -> PyResult<Vec<(&'static str, Bound<'py, PyAny>)>> {
    let ((o, ko), (n, kn)) = (text(old, "old")?, text(new, "new")?);
    let kind = same(ko, kn)?;
    let edits = api::diff_lines(&o, &n, algorithm).map_err(value_err)?;
    edits
        .into_iter()
        .map(|e| Ok((e.kind.name(), out(py, e.line, kind)?)))
        .collect()
}

/// Replay `edits` (as returned by `diff_lines`) on `old` and return the new text. Raises
/// `ValueError` if the script does not fit `old`.
#[pyfunction]
fn apply_edits<'py>(
    py: Python<'py>,
    old: &Bound<'py, PyAny>,
    edits: Vec<(String, Bound<'py, PyAny>)>,
) -> PyResult<Bound<'py, PyAny>> {
    let (o, ko) = text(old, "old")?;
    let mut script = Vec::with_capacity(edits.len());
    for (name, line) in &edits {
        let (bytes, kl) = text(line, "an edit line")?;
        same(ko, kl)?;
        script.push(Edit {
            kind: EditKind::parse(name).map_err(value_err)?,
            line: bytes,
        });
    }
    out(py, api::apply_edits(&o, &script).map_err(value_err)?, ko)
}

/// A unified diff of `old` into `new` for a file called `name`, with `context` lines of context,
/// that `git apply` accepts. Empty when the texts are equal. A patch with `context=0` needs
/// `git apply --unidiff-zero`.
#[pyfunction]
#[pyo3(signature = (old, new, name = "file", context = 3, algorithm = "minimal"))]
fn unified_patch<'py>(
    py: Python<'py>,
    old: &Bound<'py, PyAny>,
    new: &Bound<'py, PyAny>,
    name: &str,
    context: usize,
    algorithm: &str,
) -> PyResult<Bound<'py, PyAny>> {
    let ((o, ko), (n, kn)) = (text(old, "old")?, text(new, "new")?);
    let kind = same(ko, kn)?;
    out(
        py,
        api::unified_patch(&o, &n, name, context, algorithm).map_err(value_err)?,
        kind,
    )
}

/// Three-way line merge of `left` and `right`, both edits of `base`: `(text, conflicts)`.
#[pyfunction]
#[pyo3(signature = (base, left, right, algorithm = "minimal"))]
fn merge3<'py>(
    py: Python<'py>,
    base: &Bound<'py, PyAny>,
    left: &Bound<'py, PyAny>,
    right: &Bound<'py, PyAny>,
    algorithm: &str,
) -> PyResult<(Bound<'py, PyAny>, usize)> {
    let ((b, kb), (l, kl), (r, kr)) = (
        text(base, "base")?,
        text(left, "left")?,
        text(right, "right")?,
    );
    let kind = same(same(kb, kl)?, kr)?;
    let m = api::merge3(&b, &l, &r, algorithm).map_err(value_err)?;
    Ok((out(py, m.text, kind)?, m.conflicts))
}

/// The edit distance between two ordered labelled trees, each given as preorder `labels` and
/// `parents` (the index of each node's parent, `-1` for the root at index 0). `objective` is
/// `"top-down"` or `"general"`. Raises `ValueError` for an empty or malformed tree, one with more
/// than 20,000 nodes, or one deeper than 8,192 levels (128 on WebAssembly, which has a 1 MiB stack).
/// A tree deeper than 32 levels is compared on a thread with a 64 MiB stack, so the limit does not
/// depend on the calling thread's stack.
#[pyfunction]
#[pyo3(signature = (labels_a, parents_a, labels_b, parents_b, objective = "top-down"))]
fn tree_distance(
    labels_a: Vec<String>,
    parents_a: Vec<i32>,
    labels_b: Vec<String>,
    parents_b: Vec<i32>,
    objective: &str,
) -> PyResult<u32> {
    api::tree_distance(&labels_a, &parents_a, &labels_b, &parents_b, objective).map_err(value_err)
}

/// The version of the bindings.
#[pyfunction]
fn version() -> &'static str {
    api::version()
}

#[pymodule]
#[pyo3(name = "difffold")]
fn difffold_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(diff_lines, m)?)?;
    m.add_function(wrap_pyfunction!(apply_edits, m)?)?;
    m.add_function(wrap_pyfunction!(unified_patch, m)?)?;
    m.add_function(wrap_pyfunction!(merge3, m)?)?;
    m.add_function(wrap_pyfunction!(tree_distance, m)?)?;
    m.add_function(wrap_pyfunction!(version, m)?)?;
    Ok(())
}
