//! The WebAssembly module (wasm-bindgen). `wasm-bindgen` turns this into JavaScript and TypeScript
//! declarations.
//!
//! Every text function has a byte form (`Uint8Array`) and a `...Text` form (`string`). The text
//! form is UTF-8; lines are split at `\n`, which never falls inside a UTF-8 sequence.

use js_sys::{Array, Uint8Array};
use wasm_bindgen::prelude::*;

use crate::api::{self, Edit, EditKind};

#[wasm_bindgen(typescript_custom_section)]
const TYPES: &str = r#"
/** What an edit does to a line. */
export type EditKind = "equal" | "delete" | "insert";
"#;

fn err(e: api::ApiError) -> JsError {
    JsError::new(&e.to_string())
}

fn utf8(bytes: Vec<u8>) -> Result<String, JsError> {
    String::from_utf8(bytes).map_err(|_| JsError::new("internal error: the result is not UTF-8"))
}

fn pair(kind: EditKind, line: JsValue) -> JsValue {
    Array::of2(&JsValue::from_str(kind.name()), &line).into()
}

fn edits_from(
    edits: &Array,
    line: impl Fn(JsValue) -> Result<Vec<u8>, JsError>,
) -> Result<Vec<Edit>, JsError> {
    let mut out = Vec::with_capacity(edits.length() as usize);
    for (i, item) in edits.iter().enumerate() {
        let item = item
            .dyn_into::<Array>()
            .map_err(|_| JsError::new(&format!("edit {i} must be a [kind, line] pair")))?;
        let kind = item
            .get(0)
            .as_string()
            .ok_or_else(|| JsError::new(&format!("edit {i}: the kind must be a string")))?;
        out.push(Edit {
            kind: EditKind::parse(&kind).map_err(err)?,
            line: line(item.get(1))?,
        });
    }
    Ok(out)
}

fn bytes_line(v: JsValue) -> Result<Vec<u8>, JsError> {
    v.dyn_into::<Uint8Array>()
        .map(|a| a.to_vec())
        .map_err(|_| JsError::new("an edit line must be a Uint8Array"))
}

fn text_line(v: JsValue) -> Result<Vec<u8>, JsError> {
    v.as_string()
        .map(String::into_bytes)
        .ok_or_else(|| JsError::new("an edit line must be a string"))
}

/// An ordered edit script from `old` to `new`.
#[wasm_bindgen(js_name = diffLines, unchecked_return_type = "Array<[EditKind, Uint8Array]>")]
pub fn diff_lines(old: &[u8], new: &[u8], algorithm: &str) -> Result<Array, JsError> {
    let edits = api::diff_lines(old, new, algorithm).map_err(err)?;
    Ok(edits
        .into_iter()
        .map(|e| pair(e.kind, Uint8Array::from(e.line.as_slice()).into()))
        .collect())
}

/// An ordered edit script from `old` to `new`, as strings.
#[wasm_bindgen(js_name = diffLinesText, unchecked_return_type = "Array<[EditKind, string]>")]
pub fn diff_lines_text(old: &str, new: &str, algorithm: &str) -> Result<Array, JsError> {
    let edits = api::diff_lines(old.as_bytes(), new.as_bytes(), algorithm).map_err(err)?;
    let mut out = Array::new();
    for e in edits {
        out.push(&pair(e.kind, JsValue::from_str(&utf8(e.line)?)));
    }
    Ok(std::mem::take(&mut out))
}

/// Replay `edits` on `old` and return the new text.
#[wasm_bindgen(js_name = applyEdits)]
pub fn apply_edits(
    old: &[u8],
    #[wasm_bindgen(unchecked_param_type = "Array<[EditKind, Uint8Array]>")] edits: &Array,
) -> Result<Vec<u8>, JsError> {
    api::apply_edits(old, &edits_from(edits, bytes_line)?).map_err(err)
}

/// Replay `edits` on `old` and return the new text, as strings.
#[wasm_bindgen(js_name = applyEditsText)]
pub fn apply_edits_text(
    old: &str,
    #[wasm_bindgen(unchecked_param_type = "Array<[EditKind, string]>")] edits: &Array,
) -> Result<String, JsError> {
    utf8(api::apply_edits(old.as_bytes(), &edits_from(edits, text_line)?).map_err(err)?)
}

/// A `git apply`-able unified diff. A patch with `context` 0 needs `git apply --unidiff-zero`.
#[wasm_bindgen(js_name = unifiedPatch)]
pub fn unified_patch(
    old: &[u8],
    new: &[u8],
    name: &str,
    context: u32,
    algorithm: &str,
) -> Result<Vec<u8>, JsError> {
    api::unified_patch(old, new, name, context as usize, algorithm).map_err(err)
}

/// A `git apply`-able unified diff, as strings.
#[wasm_bindgen(js_name = unifiedPatchText)]
pub fn unified_patch_text(
    old: &str,
    new: &str,
    name: &str,
    context: u32,
    algorithm: &str,
) -> Result<String, JsError> {
    utf8(
        api::unified_patch(
            old.as_bytes(),
            new.as_bytes(),
            name,
            context as usize,
            algorithm,
        )
        .map_err(err)?,
    )
}

/// Three-way line merge: `[text, conflicts]`.
#[wasm_bindgen(js_name = merge3, unchecked_return_type = "[Uint8Array, number]")]
pub fn merge3(base: &[u8], left: &[u8], right: &[u8], algorithm: &str) -> Result<Array, JsError> {
    let m = api::merge3(base, left, right, algorithm).map_err(err)?;
    Ok(Array::of2(
        &Uint8Array::from(m.text.as_slice()),
        &JsValue::from_f64(m.conflicts as f64),
    ))
}

/// Three-way line merge, as strings: `[text, conflicts]`.
#[wasm_bindgen(js_name = merge3Text, unchecked_return_type = "[string, number]")]
pub fn merge3_text(base: &str, left: &str, right: &str, algorithm: &str) -> Result<Array, JsError> {
    let m = api::merge3(
        base.as_bytes(),
        left.as_bytes(),
        right.as_bytes(),
        algorithm,
    )
    .map_err(err)?;
    Ok(Array::of2(
        &JsValue::from_str(&utf8(m.text)?),
        &JsValue::from_f64(m.conflicts as f64),
    ))
}

/// The edit distance between two ordered labelled trees, each as preorder `labels` and `parents`
/// (`-1` for the root). `objective` is `"top-down"` or `"general"`.
#[wasm_bindgen(js_name = treeDistance)]
pub fn tree_distance(
    labels_a: Vec<String>,
    parents_a: &[i32],
    labels_b: Vec<String>,
    parents_b: &[i32],
    objective: &str,
) -> Result<u32, JsError> {
    api::tree_distance(&labels_a, parents_a, &labels_b, parents_b, objective).map_err(err)
}

/// The version of the bindings.
#[wasm_bindgen]
#[must_use]
pub fn version() -> String {
    api::version().to_owned()
}
