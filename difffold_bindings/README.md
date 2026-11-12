# difffold_bindings

Python and TypeScript (WebAssembly) bindings for [difffold](../README.md), through one small API. Text
is `str`/`bytes` in Python and `string`/`Uint8Array` in JavaScript (functions ending in `Text` take
strings); everything else is lists and integers, never difffold's internal types.

| Function (Python / JavaScript) | What it does |
|---|---|
| `diff_lines(old, new, algorithm="minimal")` / `diffLines`, `diffLinesText` | an ordered edit script: `(kind, line)` pairs, `kind` one of `equal`, `delete`, `insert`; each line keeps its newline. `minimal` is the fewest changed lines (the `git diff --minimal` objective); `histogram` is valid but not necessarily minimal |
| `apply_edits(old, edits)` / `applyEdits`, `applyEditsText` | replay a script on `old` and return the new text; raises if the script does not fit `old` |
| `unified_patch(old, new, name="file", context=3, algorithm="minimal")` / `unifiedPatch`, `unifiedPatchText` | a unified diff that `git apply` accepts forwards and `--reverse`. With `context=0`, Git needs `--unidiff-zero` |
| `merge3(base, left, right, algorithm="minimal")` / `merge3`, `merge3Text` | three-way line merge: `(text, conflicts)`, with conflict markers |
| `tree_distance(labels_a, parents_a, labels_b, parents_b, objective="top-down")` / `treeDistance` | ordered-tree edit distance, `top-down` (the `diff` engine) or `general` (the `ted` engine); see below |
| `version()` | the version |

A tree is its nodes in preorder: `labels[i]` is node `i`'s label and `parents[i]` its parent's index
(`-1` for the root at index 0, and every other parent comes earlier). Children keep index order. For
example `a(b)` is `["a", "b"], [-1, 0]`, and wrapping `b` in `c`, `a(c(b))`, is
`["a", "c", "b"], [-1, 0, 1]`: the `general` distance between them is 1, the `top-down` distance is 2
(README "Choose an engine": the two objectives are not interchangeable).

Limits, because the tree engines are polynomial and recurse over the tree, checked before any work:

| | Python and other native builds | WebAssembly (TypeScript) |
|---|---|---|
| Nodes per tree | 20,000 | 20,000 |
| Levels (depth) per tree | **8,192** | **128** |

Depth is stack depth, so the depth limit is the stack divided by a per-level budget of 8 KiB. The
worst measured use is about 5 KiB per level (`top-down`, unoptimised: on a 1 MiB stack the deepest
chain that completed was about 207 levels, and `general` managed 860; optimised builds manage about
1,030 and 4,090), so 8 KiB leaves a margin under the worst of them.

- **WebAssembly** has no threads and a 1 MiB stack by default, so it uses what it has: 1 MiB / 8 KiB =
  **128 levels**.
- **Everywhere else** the limit unlocks automatically: a tree deeper than 32 levels is compared on a
  thread of its own with a 64 MiB stack (address space that is only touched as the recursion goes
  deep), so the limit is 64 MiB / 8 KiB = **8,192 levels**, whatever thread called and however small
  its stack is. Shallow trees run on the caller's thread with no extra cost. If the operating system
  refuses the stack, the call returns an error that says so; it does not crash.

Depth is rarely the practical limit: real source trees are far shallower than 128 levels, and the
node limit and the quadratic cost of `general` bite first. Memory for `general` grows with the square
of the node count, so a very deep chain is slow before it is refused. Anything else malformed, or a
script that does not fit, is an error (`ValueError` / `Error`), never a crash.

Not exposed: tree edit scripts and mappings (`ted` reports postorder indices, and translating them is
a design decision rather than a binding), cost models, and the experimental aligners.

## Python

```python
import difffold
difffold.diff_lines("a\nb\n", "a\nc\n")      # [('equal', 'a\n'), ('delete', 'b\n'), ('insert', 'c\n'), ...]
difffold.unified_patch(old, new, name="src/x.rs")
```

```bash
scripts/test-python.sh        # builds the extension, runs the tests (no maturin needed)
maturin build --release       # a wheel (abi3: one wheel for Python 3.9+)
```

## TypeScript / JavaScript

```bash
scripts/build-wasm.sh         # needs the wasm32-unknown-unknown target and a wasm-bindgen CLI matching Cargo.lock
node tests/wasm/test.mjs
```

`build-wasm.sh` writes `dist/` (a Node.js module and `difffold_bindings.d.ts`).

## What the tests check

Against the built artifacts, not just the Rust: edit scripts are rebuilt by hand into both texts and the
minimal one is compared with an LCS table; unified patches go through real `git apply` (forwards and
`--reverse`) on random texts, missing final newlines, CRLF, quoted and non-ASCII file names and a
200,000-character line; the tree distances are checked against hand-computed values; and the limits
and error paths are exercised. `tests/git_apply.rs` does the same from Rust.

## Not done

Go, Java/Kotlin, Swift and C bindings. A C ABI (`cbindgen`) would serve Go and C; UniFFI would serve
Kotlin and Swift but is MPL-2.0, which `deny.toml` does not allow.
