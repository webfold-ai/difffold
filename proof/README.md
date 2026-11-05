# difffold proofs: status

Lean 4.31.0 (the version `apeiron/proof/lean-toolchain` pins), no Mathlib, plain `lean`. Five modules,
about 910 lines, **no `sorry`, no custom axiom**. Re-checked from clean `.olean` files by the lead
after the worker that wrote them was interrupted; the output is in `AXIOMS.txt`. Every headline
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, or on `propext` and
`Quot.sound` alone.

```sh
source env.sh        # puts the pinned Lean on PATH (the toolchain lives in the session scratchpad)
./build.sh Basic Prune Decision Link Strip
```

`env.sh` points at a scratchpad toolchain that is deleted with the session; re-install Lean 4.31.0
with `elan` to reproduce.

## What is proved, and about what

**Everything here is about the Lean model, not the Rust code.** The model (`Basic.lean`) is the
top-down (Selkow) objective: a deleted node removes its whole subtree, a pair needs matched
parents, a label change costs one. It is not classical Zhang-Shasha, where deletion promotes
children. No theorem here is stated over Aeneas-extracted Rust.

| theorem | statement | file |
|---|---|---|
| `h_admissible` | for any pair-cost function respecting the size bound, `size X <= size Y + c` and `size Y <= size X + c` for every alignment of forests X, Y of cost c (the pruning bound is admissible) | Basic |
| `tedit_bound` | every top-down edit of x to y costs at least `|size x - size y|` (the size lower bound C7) | Basic |
| `prune_sound` | with `h <= R*`, a cell with `F*(i,j) + R*(i,j) <= tau` is kept, and its value is exactly `F*(i,j)`, although the DP computes from kept predecessors only | Prune |
| `path_cells_kept` | every cell on a path of cost at most `tau` is kept | Prune |
| `decision` | the final cell holds a result iff the true minimum is at most `tau` | Decision |
| `result_is_min` | and then the result is the true minimum | Decision |
| `search_min` | the threshold-widening loop, if it returns, returns the true minimum | Decision |
| `search_total` | if the true minimum is at most `tau + k`, the loop returns within `k + 1` rounds (termination of widening) | Decision |
| `skip_sound` | skipping the recursive pair cost when `F_diag + |size a - size b| + h > tau` changes neither a kept cell's value nor whether it is kept | Decision |
| `hLists_admissible` | `h(i,j) = |R_a(i) - R_b(j)|`, with R the reversed accumulation of sizes, is admissible for child lists | Link |
| `fstar_is_opt` | the grid's `F*` at the final cell is the optimal alignment cost | Link |
| `prune_correct_lists` | end to end on child lists: the kept-cell DP returns a result iff the optimal alignment cost is at most `tau`, and the result is that cost | Link |
| `widen_correct_lists` | the widening search returns an alignment that is optimal | Link |
| `strip_safe`, `strip_safe_iff` | pairing equal leading and trailing children at cost zero loses no optimality; the side conditions (`d x x = 0`, the size bound) are proved from the Selkow cost model, and no triangle inequality is needed | Strip |

`prune_sound` is the corrected statement. It does not claim that the DP's `F` is a lower bound on
the prefix cost (it can overestimate when predecessors are pruned); it claims that cells that lie
on some path of cost at most `tau` are kept and exact.

## Extraction chain (caretaker's standard) status

caretaker's `docs/agents/proof-verifier.md` allows the label `ProvenByLeanKernel` only when Charon
extraction, Aeneas translation and the Lean check all pass for the same source, with each stage's
input digest equal to the previous stage's output digest, and it forbids calling a weaker model a
proof. Against that standard the Lean files above are **a model**, not a proof of the Rust code.
What exists for the Rust code:

| stage | status | evidence |
|---|---|---|
| source | `src/kernel.rs` is the only implementation of the threshold DP; `diff.rs` calls it and `proof/extract/lib.rs` includes the same file by `#[path]` | `gen/RECEIPT.txt` has its sha256 |
| Charon | passes, nightly-2026-08-18, Charon 0.1.254 | `gen/RECEIPT.txt`, `extract.sh` |
| Aeneas | passes, release nightly-2026.09.09, no errors, no unknown external definitions | `gen/lean/DifffoldKernel.lean` |
| Lean check of the generated file | **passes** (Lean 4.31.0, Mathlib at the Aeneas-pinned revision with its cache, Aeneas library built); the digest it checked equals the one in `gen/RECEIPT.txt` | `check-kernel.sh` prints `stage 3 ok: DifffoldKernel.lean sha256 2446d3cc...` |
| theorems stated over the extracted code | **three so far**, zero `sorry` (below) | `Kernel/Spec.lean` |
| refinement: extracted code = Lean model, so the model theorems transfer | **not started**; needs loop specs for `row_cells`, `first_row`, `trim_row`, `fill` | |

The Aeneas release archive was verified against its published sha256
(`d5ba53b1370d30866bcd86de5e34abfbadf09e76b3689a7f70f458cd0c133591`). The binaries are the stock
release, **not apeiron's patched build**, so apeiron's `regen.sh` tool-identity check would reject
them; the kernel avoids the constructs those two patches repair (array repeat).

What Aeneas forced, and why the kernel looks the way it does: no early `return` inside nested
loops, no `continue` to an outer loop, and no arithmetic written directly into an indexed store
(`out[i] = a + b` fails with "unimplemented binary operation"; `let s = a + b; out[i] = s;` works).
`fill` is therefore split into `first_row`, `row_cells`, `trim_row` and a flat driver. The tests
still pass in debug and release after the change.

Preconditions the extracted code carries and that a proof over it must discharge, because Aeneas
makes every `+` overflow-checked: total size of both lists below 2^28, and `tau < INF`.

### Theorems over the extracted code (`Kernel/Spec.lean`)

| theorem | statement | status |
|---|---|---|
| `adiff_spec` | `kernel::adiff x y` returns `|x - y|` | checked |
| `umin_spec` | `kernel::umin x y` returns the smaller value | checked |
| `row_at_spec` | `Row::at r j` returns the held value for `j` inside the span and `INF` for every column outside it | checked |

These are small. They are listed because they are the first statements in this project that are about
the Aeneas translation of the shipped Rust, and because they show the toolchain is in place. The
loop functions are next: `suffix_sums` (result length `n + 1`, value `sum x[i..]`, no overflow under a
total-size precondition), then the three row functions, then `fill`.

Reproduce with `extract.sh` and then `LEAN_WS=<Aeneas backends/lean copy with Mathlib cache and
\`lake build Aeneas\`> ./check-kernel.sh Spec`.

## Interner on apeiron's certified table

`src/intern.rs` now keeps its bucket heads in apeiron's `map::table::Table<i64, i64, WordHome>`, the
total-default table whose canonical object is `Apeiron.Table.HMap` with `get` and `insertWith`
(`proof/canonical/Apeiron/Table/Basic.lean`: `get_insertWith_self`, `get_insertWith_ne`). An absent
bucket reads as the default `NIL`. The earlier version used the hashtrinity-port `freq::Table`, which
contains `MaybeUninit` and cannot be extracted by Aeneas. Not done: the Lean statement `mk_exact`
over `Apeiron.Table.HMap`, the extraction of the chain walk, and any import of apeiron's own
refinement corpus, which needs apeiron's patched toolchain. Until then the Rust interner is
covered by tests only, including the constant-bucket test.

## Theorems over the extracted Rust: current state (verified by compiling, zero sorry)

Compiled with Lean 4.31.0 in this session; `check-kernel.sh`, `check-lines.sh` and `check-ted.sh` exit 0. Digests: `gen/RECEIPT.txt`
(kernel), `gen/RECEIPT-lines.txt` (lines, ted).

| extracted code | theorems (about the Aeneas translation) | status |
|---|---|---|
| `src/kernel.rs` (threshold DP) | `adiff_spec`, `umin_spec`, `row_at_spec`; `suffix_sums` loop specs; `trim_row`; `first_row`, `bound`, `hh`; `del_cand`, `ins_cand`, `lower_bound`, `diag_stage`; `cell_value_spec` (equals the model cell); `row_cells_loop_spec` (the row loop builds the model row) | checked |
| `src/kernel.rs` | `row_cells_spec` (wrapper), `fill_loop_spec` (each stored row equals the model row, or a fully pruned row ends the search), `fill_spec` (returns a result exactly when the model cell `(n, m)` survives pruning, with its value; `none` when pruned) | checked |
| `src/kernel.rs` | `fill_optimal`: under admissibility of the heuristic (`h <= B`), `fill` returns a result iff the grid optimum `F*(n, m) <= tau`, the stored value is that optimum, and `none` means the optimum exceeds `tau` (composes `fill_spec` with the model's `decision` and `result_is_min`) | checked, conditional on admissibility |
| admissibility of the bound | `ad_le_B` (for any grid whose pair costs respect the size bound, `|R_a(i) - R_b(j)| <= B(i, j)`), `RS_eq_sumU`, `hK_admissible` (with `ra`, `rb` the suffix sums that `suffix_sums_spec` proves the extracted `suffix_sums` returns) | checked |
| `src/kernel.rs` | `fill_correct`: `fill_optimal` with the heuristic discharged. Remaining hypotheses: `ra`, `rb` are the suffix sums of `sa`, `sb`; the oracle's pair cost respects the size bound; size limits below 2^27; `tau` at least the bound at the origin | checked |
| what `fill_correct` does **not** cover | that the grid is the child-list alignment of two nodes and that the oracle's `pair_cost` is the recursive distance (properties of `diff.rs`); the Myers line search; TED | **not done** |
| `src/lines.rs` helpers (real file, included by `#[path]`) | `common_prefix_spec`, `common_suffix_spec` (generic and `u8`): length <= min, prefixes equal, and either the minimum or the next elements differ; `nl_mask_bv` (SWAR mask equals the bit-vector definition); `nl_mask` bit k set iff byte k is `0x0A`; `word_spec` | checked |
| `first_in_block`, `first_nl` | `first_in_block_spec`, `first_nl_spec`: the index of the first `0x0A` or none. **Conditional on `TzSpec`**, a hypothesis that `u64::trailing_zeros` returns the index of the lowest set bit (Aeneas has no model of it) | checked, conditional |
| `first_nl`, `last_nl` | Aeneas rejects the real functions (mutually recursive closure impls), so the extraction uses a closure-free copy `extract/lines_core.rs`. The copy is tied to the real source by `tests/agree.rs` on 60,000 random inputs, **not by a proof**. `last_nl` has no spec. | tested only |
| `src/ted.rs` (real file, `#[path]`) | Extracted by `extract-lines.sh` with roots `PostTree::from_kids`, `label_lower_bound`, `fill_window`, `within_td`; no hand copy remains. `src/ted.rs` was refactored non-semantically so those functions use only constructs stock Aeneas translates (while loops, `if`-based min/max/abs_diff helpers, counting instead of `sort_unstable`, `wrapping_add` counters). `gen/lean-ted/DifffoldTed.lean` has no axiom and elaborates (`check-ted.sh`). `ted_oriented`, `mirror`, `ted_mapping`, `check_mapping`, `replay_script` are not extracted yet. | extracted, elaborates |

### TED theorems over the extracted code (`Ted/*.lean`, `check-ted.sh`, zero `sorry`, standard axioms only)

All statements are about the Aeneas translation of the real `src/ted.rs` (included by `#[path]`, no copy). Output: `AXIOMS-ted.txt`.

| theorem | statement | file |
|---|---|---|
| `from_kids_spec` | `lml` satisfies the leftmost-leaf equations; keyroots are strictly ascending and are exactly the last node per leftmost leaf | `FromKids` |
| `label_lower_bound_spec` | result is `max(n, m) - overlap` (multiset intersection, `Ted.count_interM`), no sort axiom | `LabelLB`, `Overlap` |
| `Ted.D`, `D_size` | the Zhang-Shasha forest recursion on postorder indices (right-to-left, whole-tree match when both last trees start at the forest ends), and `|size F - size G| <= D <= size F + size G` | `Zs` |
| `Ted.D_le_cost`, `Ted.exists_map` | `D l x l' y` **equals the minimum cost of a valid tree edit mapping** between the node ranges (one to one, preserving postorder and the descendant relation; cost = unmapped nodes + relabel costs). This is the independent mapping-based specification | `Mapping` |
| `Ted.D_row_mono` | rows of the forest table never get cheaper (the early exit is sound) | `Mono` |
| `cell_truth_leaf`, `cell_truth_nonleaf`, `cellNew_fok` | one cell of the banded table is ok: never below `min(true, tau + 1)`, never above `tau + 1`, exact when the true value plus the position offset of the window fits the budget | `Truth`, `Window` |
| `fill_inner_loop_spec`, `fill_rows_loop_spec`, `fill_window_spec` | the three nested loops of `fill_window` maintain that invariant, the early exit `row_min > tau` and the empty band lose nothing, and the subtree-distance table `td` ends ok for all pairs of the window's subtrees; entries of other windows are untouched | `Window` |
| `within_inner_spec`, `within_outer_spec`, `within_td_spec` | the loops over keyroot pairs (ascending order argument through `krf`), the skip filter `|li - lj| > 2 tau`, and the driver: `within_td` returns `some d` exactly when `ted <= tau`, and then `d = ted`, where `ted = D 1 n 1 m` (trees given by leftmost-leaf maps that nest, `WfL`, with a single root); it also returns a table that is ok for every pair | `Driver` |
| `cell_step`, `get_spec`, `bidx_spec`, `relabel_cost_spec` | one inner-loop iteration and the arithmetic helpers, including the kind-aware relabel cost 0/1/2 | `Cell` |

Hypotheses of the driver theorem (all stated, none assumed silently): `WfL` of both leftmost-leaf maps (subtrees are intervals that nest), a
single root (`lml n = 1`), keyroot lists that are sorted and exactly the last node per leftmost leaf (`from_kids_spec` gives this), fewer than
`2^14` nodes per tree and `tau <= n + m` so that no `usize` addition overflows on a 32-bit platform.

**Not done** (reported honestly): `ted_oriented` (the doubling loop), `mirror` and the invariance of the distance under mirroring,
`ted_mapping` (traceback), `check_mapping`, `replay_script` are not extracted or proved. `WfL` of the `lml` array that `from_kids` builds is
assumed, not derived from a validity predicate on the child lists (it holds for postorder trees built by `expand`).

## What is not proved

- `replay_sound`: that `apply` rebuilds the after-tree from a script `edit` produced.
- `mk_exact`: exact identity of the hash-consing arena for any bucket function, with last-write
  semantics on the head table. (The interner defect found by the constant-bucket test was in this
  area; its fix is covered by a Rust test, not by a proof.)
- Termination and totality of the recursive `dist` itself, and that the Rust `dist` is the model's
  distance.
- A link from the Rust line differ or TED solver to a statement of optimality. Theorems exist only for the
  helpers and kernel pieces listed in the table above.
- Comparison against apeiron's `AxiomAudit` policy. The axioms observed are the standard three; the
  policy file was not read against them.
- The model assumes unit costs and the Selkow objective. Custom costs are out of scope.
