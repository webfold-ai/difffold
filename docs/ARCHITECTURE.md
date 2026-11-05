# Architecture

This document describes how the code in this repository fits together. Every statement can be checked in
the file named next to it. For contracts see [SPEC.md](../SPEC.md); for what is proved and tested see the
Evidence table in the [README](../README.md#evidence).

## Inputs and outputs

The library (`src/`, crate `difffold`) has no parser, no I/O and no `unsafe` code (`#![forbid(unsafe_code)]`
in `src/lib.rs`). Callers supply already-structured input.

| Engine | Input | Output |
|---|---|---|
| `lines` | Two byte strings (`&[u8]`), or two slices of dense line ids | `LineDiff`: one `deleted` flag per old line and one `inserted` flag per new line; `cost()`; `replay_ok` checks it |
| `unified` | Two byte strings, a file name, a context size, an `Algo` | A unified patch as bytes (`git apply`-able); empty when the texts are equal |
| `merge` | Base, left and right byte strings | `Merged { text, conflicts }` |
| `diff` | An `Arena` and two root `Id`s | `Diff { cost, edit: Edit, stats }`; `Edit` is `Keep` / `Del` / `Ins` / `Upd` over canonical nodes |
| `mapping` | An arena, two roots and an `Edit` | `Correspondence`: node pairs by preorder index with a `PairKind` (identical, relabel, changed) |
| `ted` | Two `PostTree`s (postorder labelled trees) | Distance (`ted`, `ted_stats`, `ted_within`, `ted_unpruned`); `Mapping { cost, pairs }` with 1-based postorder indices (`ted_mapping`); validation results (`check_mapping`, `replay_script`) |

Tree engines take labels as `u32`. Turning a source file into labelled trees is the caller's job. The
research binaries (`ts` feature) and the harness do it with tree-sitter: every node is kept, a leaf's label
is its (kind, text) pair, an inner node's label is its kind (see `Interner` in `src/bin/score_accuracy.rs`
and `src/bin/ted_map.rs`).

## Main path

### Raw text, lines, unified patch

```text
bytes old, bytes new
  -> lines::diff_text_with(old, new, Algo)
       cut common prefix and suffix on raw bytes, backed up to line starts
       dense id per distinct line of the middle (hash only picks a bucket; bytes are compared on a hit)
       lines whose id occurs on one side only are marked as edits and leave the search
       linear-space bidirectional Myers (middle snake) on what is left        [Algo::Minimal]
       or histogram: anchor on the rarest common line and recurse             [Algo::Histogram, not minimal]
  -> LineDiff { deleted, inserted }           (lines::replay_ok re-applies it to check)
  -> unified::unified / unified_with          hunks with context, `\ No newline at end of file`, headers
  -> bytes of a patch that `git apply` accepts (forward and reverse)
```

`src/bin/dfdiff.rs` wraps this and can run as `GIT_EXTERNAL_DIFF`. `tests/roundtrip.rs` runs real `git
apply` on the output. `lines.rs` is written with recursion only, no loops (module doc); `unified.rs` and
`merge.rs` are ordinary loop code.

`gitcompat/` is a separate path to a patch: its own Myers (`gitcompat/src/myers.rs`, with a work budget and a
delete-all/insert-all fallback when the budget runs out), binary-file handling that delegates to `git diff
--binary --no-index` or refuses, and `gitcheck.rs`, which verifies a patch with `git apply --check`,
`git apply` and `git apply --index`. It does not use `difffold::lines`.

### Parsed structure, interned arena, top-down diff

```text
caller's tree (e.g. tree-sitter)  ->  u32 labels
  -> Arena::mk(label, &[kid ids])  bottom-up        equal subtrees get one Id (invariant I1)
  -> diff::diff(&arena, before, after)               Config::PRODUCTION by default
       dist(x, y) = 0 if x == y by id; memoised on the (id, id) pair
       child lists: strip equal first and last children, then
       threshold DP (kernel::fill): keep a cell only if F + h <= tau, h = |R_a(i) - R_b(j)|;
       tau starts at h(0,0) and doubles until a result fits
       the recursive pair cost is supplied to the kernel through the `Oracle` trait
  -> Diff { cost, edit, stats }
  -> diff::diff_checked(&mut arena, ..)              panics unless apply(before, edit) == after and cost(edit) == cost
  -> mapping::correspondence(&arena, before, after, &edit)   preorder node pairs
```

The objective is the top-down (Selkow) distance in the `diff.rs` module doc: unit cost per node, a node pairs
only if its parent does, roots always pair, deleting or inserting a child costs its subtree size.
`Config` switches (`deep_eq`, `memo`, `threshold`, `tau0`, `growth`) exist for the ablation ladder; every
setting computes the same distance (`tests/boundaries.rs`, `schedules_and_configs_agree_on_distance`).

### Parsed structure, PostTree, general TED, mapping and replay

```text
caller's tree  ->  PostTree::from_kids(label, kids)      postorder, children before parents
        or         PostTree::from_arena(&arena, root)    expands the shared-subtree DAG into a tree
   (optional)      .with_kinds(kind)                     relabel across kinds costs 2
  -> ted::ted_stats(a, b)
       build the mirror image of both trees; use the orientation whose keyroot sizes give the smaller
         work estimate (left paths or right paths)
       first threshold tau = max(|n - m|, label multiset lower bound, 1); double on failure;
         once 3 * tau >= max(n, m), jump straight to tau = n + m (no band pruning left to gain)
       per attempt: Zhang-Shasha keyroot windows over banded arrays of width 2 * tau + 1;
         window pairs with |lml_a - lml_b| > 2 * tau are skipped (position filter)
       an attempt that finds no result of cost <= tau returns None and the loop widens
  -> distance (exact)
  -> ted::ted_mapping(a, b)          re-run at the exact distance, trace back through the forest tables
  -> ted::check_mapping(a, b, pairs) independent validity check: one to one, ancestor relation preserved
                                     both ways, sibling order preserved; returns the implied script cost
  -> ted::replay_script(a, b, pairs) executes relabel, delete-with-promotion, insert on a mutable copy of a
                                     and requires the result to equal b; returns the operation count
```

`ted_unpruned` runs plain Zhang-Shasha (left paths only, threshold at its maximum `n + m`) as the
objective-matched baseline. `replay_script` places inserts using the structure of `b`, so it shows the
mapping is executable and the operations compose to `b`; it does not derive the script independently of `b`
(doc comment in `src/ted.rs`).

## Key modules

| Module | Role |
|---|---|
| `intern` | `Arena`: hash-consed forest with exact identity (I1). A 64-bit fold only selects a bucket; every candidate is compared against its stored label and children. Bucket heads live in apeiron's `map::table::Table` |
| `kernel` | The threshold DP `fill` and its row helpers, written in the subset Aeneas can translate. `diff.rs` calls it, and `proof/extract/` includes the same file by `#[path]` |
| `diff` | Top-down differ: `Differ` (memo, align, trace, edit), `Config`, `Stats`, `apply`, `cost`, `diff_checked` |
| `mapping` | Edit script to node correspondence for the top-down engine |
| `ted` | General TED: `PostTree`, `ted*`, mapping, validator, replay, and the `proof_api` hidden module used by `tests/ted_core.rs` |
| `lines` | Exact line diff, histogram variant, `replay_ok`, `proof_api` hidden module used by `tests/agree.rs` and `tests/myers_core.rs` |
| `unified` | Unified-patch writer for `lines` |
| `merge` | Three-way merge with diff3 semantics on `lines` |
| `frontier` | Experimental, see below |

## State and caching

- **Arena**: owned by the caller, passed as `&Arena` to `diff` and `&mut Arena` to `diff_checked` and
  `apply`. It only grows; there is no removal. Ids from one arena are meaningless in another.
- **Memo**: `diff::Differ` keeps a memo of `dist` keyed on the `(Id, Id)` pair (apeiron's `freq::Table`).
  It is created per call to `diff`, `diff_with` or `distance_with` and dropped with the `Differ`. Nothing
  persists between calls.
- **`ted`**: no cross-call state. Every attempt allocates its own banded tables (`td`, `fd`); the mirrored
  trees are rebuilt per `ted_stats` call.
- **`lines`**: per-call hash tables for line ids. No cross-call state.
- **Results on disk** (`results/`, `harness/results/`) are recorded outputs, not caches; nothing in the
  library reads them.

## Error and resource boundaries

- **Contract violations panic**: `diff_checked` asserts the C3 contract (script cost equals distance, replay
  rebuilds the after-tree). `Arena::mk` panics if the arena would exceed `u32::MAX - 1` nodes or if the head
  table refuses an insert (documented under `# Panics`).
- **Recoverable errors are values**: `diff::apply`, `ted::check_mapping` and `ted::replay_script` return
  `Err(String)`; `ted_within` and `diff::align_within` return `None` when the optimum exceeds the threshold.
- **Unchecked preconditions**: `kernel.rs` states that the total size of both lists must stay below `2^28`
  and `tau` below `INF`, and that these are not checked at run time in release builds.
- **Recursion depth**: `diff`, `apply`, `mapping` and `PostTree::from_arena` recurse over tree depth. The line
  sweep recurses to depth at most `D / 2 + 1` for edit distance `D`; `lines.rs` advises calling from a thread
  with a large stack on adversarial inputs, and `tedbench` runs in a thread with a 256 MiB stack
  (`linebench/src/tedbench.rs`).
- **Memory in `ted`**: at threshold `tau` the subtree-distance table has `(n + 1) * (2 * tau + 1)` `u32`
  entries and the forest table `(max(n, m) + 1) * (2 * tau + 1)`. Because `tau` can be raised to `n + m`, the
  worst case is quadratic in the tree sizes. No peak-memory measurement is recorded in the repository
  (`notes/lanes/RESULTS.md` lists peak memory under "Not established").
- **No deadlines in the library.** The harness has its own: 60 s per tool run and a 55 s internal deadline in
  `dfold-cli` (`harness/results/machine.txt`). `gitcompat::myers` has a work budget instead
  (`DEFAULT_BUDGET`), after which it emits a valid but larger script and reports that it was capped.
- **Binary input**: `lines` works on bytes. `gitcompat` treats any NUL byte as binary and does not produce a
  text patch for it.
- **Trust**: files read by `dfdiff` are read with `expect`, so an unreadable path aborts the process.

## Dependencies and optional features

Library crate `difffold` (`Cargo.toml`, versions resolved in `Cargo.lock`):

| Dependency | Source | Required or feature-gated | Purpose |
|---|---|---|---|
| apeiron | git, `https://github.com/webfold-ai/apeiron`, rev `07ab506` (`Cargo.lock`: 0.1.0) | Required | `map::table::Table` for the interner's bucket heads (`src/intern.rs`); `freq::Table` for the `diff` memo (`src/diff.rs`) |
| tree-sitter 0.25 | crates.io | Optional, `ts` feature | Parsing in the research binaries |
| tree-sitter-java 0.23, -go 0.25, -c 0.24, -python 0.25, -javascript 0.25, -typescript 0.23, -rust 0.24 | crates.io | Optional, `ts` feature | Language grammars for the eight supported languages |
| serde_json 1 | crates.io | Optional, `ts` feature | Reading ground-truth JSON in `score_accuracy` |

Other crates in the repository. None is part of the library API:

| Dependency | Where | Source | Required or feature-gated | Purpose |
|---|---|---|---|---|
| `difffold` (path), `ts` feature | `gitcompat`, `harness/rust` | Workspace | `gitcompat`: optional, behind its `structural` feature; `harness/rust`: required | Structural summaries; harness CLI |
| tree-sitter, -java, -go, -c | `gitcompat` | crates.io | Optional, `structural` feature | Structural certificate for Java, Go and C |
| tree-sitter, -java, -go, -c, libc 0.2 | `harness/rust` | crates.io | Required for that crate | Harness CLI and process measurement |
| similar 2, imara-diff 0.1, fast_rsync 0.2, qbsdiff 1, flate2 1, apted 0.1, tree-sitter and -java/-go/-c | `linebench` (not published) | crates.io | Required for that crate | Baselines for line, sync, merge and TED benchmarks. `tree-edit-distance 0.4` is also declared but is not referenced by `linebench/src` |
| libfuzzer-sys 0.4 | `fuzz/` (own workspace) | crates.io | Required for that crate | libFuzzer targets |
| git2 0.20 (no default features) | `tools/xdiff-baseline` (own workspace and lock file) | crates.io | Required for that crate | Git xdiff via libgit2 as a baseline |
| omnidiff, anyhow 1 | `tools/omni_dump` (excluded from the workspace) | omnidiff by absolute local path; anyhow from crates.io | Required for that tool | Dumping OmniDiff's node mapping for `score_accuracy` |

Not Cargo dependencies but needed for some checks: `git` on `PATH` (round-trip tests, `gitcompat`), Lean
4.31.0 with the Aeneas library and Mathlib, Charon and Aeneas (proofs, `proof/README.md`), an OmniDiff
checkout (harness and scorer), a JVM (GumTree and RefactoringMiner runs).

Features: the root crate defines only `ts` (off by default). Six research binaries (`ablate`,
`frontier_exp`, `bench_fixtures`, `score_accuracy`, `abi_cutoff`, `ted_map`) require it
(`required-features` in `Cargo.toml`); `dfdiff` does not. The MSRV is Rust 1.89.0.

## Experimental modules

- `frontier` (`src/frontier.rs`): best-first (A\*) and linear-space (Hirschberg-style) aligners for the same
  top-down objective as `diff`. Its module doc says nothing in it is used by the production differ;
  `frontier_exp` compares it with `diff.rs` counters.
- `ted` itself is a "loop-based first version" in its module doc: the recursion-only discipline of `lines`
  has not been applied to it. It is a supported engine, but the least hardened of the three.
- `merge`: three-way merge on exact lines; compared against `git merge-file` and Mergiraf on a labelled set
  only (README).
- Hidden `proof_api` modules in `lines` and `ted`: entry points for the agreement tests of the proof copies in
  `proof/extract/`. Not part of the API.
- Research binaries behind the `ts` feature (`ablate`, `abi_cutoff`, `bench_fixtures`, `frontier_exp`,
  `score_accuracy`, `ted_map`). `ted_map` prints a node mapping as JSON for the DiffBenchmark adapter in
  `tools/diffbenchmark_adapter/` (`--algo ted` or `--algo topdown`).
- `corpus/`: a mutation-corpus generator excluded from the build; some of its sources are missing
  (`Cargo.toml` comment).
- `proof/`: Lean models and Aeneas extraction. See the README Proofs section.
