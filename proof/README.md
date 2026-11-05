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

### TED theorems over the extracted code (`Ted/*.lean`, `check-ted.sh`, zero `sorry`)

| theorem | statement | status |
|---|---|---|
| `from_kids_spec` (`Ted/FromKids.lean`) | `lml` satisfies the leftmost-leaf equations at every node (`lml[j] = j+1` for a leaf, `lml[j] = lml[first child]` otherwise, values in `1 .. j+1`); `keyroots` is strictly ascending and `v` is a keyroot iff it is the last node of the postorder with its leftmost leaf (`LastWithLml`). Hypotheses: fewer than 2^31 nodes, one child list per node, the first child of a node precedes it. Loop specs `from_kids_loop{0,1,2,3}_spec`. | checked |
| `label_lower_bound_spec` (`Ted/LabelLB.lean`) | for the real counting `label_lower_bound`: the result is `max n m - overlap(A, B)`, `overlap` the size of the multiset intersection (`Ted.interM`, `Ted/Overlap.lean`, pinned by `Ted.count_interM`: `count x (interM A B) = min (count x A) (count x B)`). Merge loop spec `llb_loop_spec`. Unconditional (the sort was replaced by a count table). Hypotheses: fewer than 2^31 nodes, labels of `a` below 2^31. Loop specs `llb_top_loop_spec`, `llb_count_loop_spec`, `llb_consume_loop_spec`. | checked |
| `cell_step` (`Ted/Cell.lean`) | one iteration of the inner loop of `fill_window` writes `fd[p,q] = min(min(min(del, ins), X), inf)` where `del`, `ins` read the up and left neighbours, `X` is the diagonal neighbour plus the relabel cost when `lx = li` and `ly = lj` (and then also stores the value in `td`), else the neighbour at the subtree boundaries plus the stored `td[x,y]`; `row_min` becomes the min; out-of-band reads give `inf`. Helpers `get_spec`, `bidx_spec`, `tdv_if_spec`, `upd_if_spec`. | checked (one cell) |
| `cellNew_cap` | if the four values a cell reads hold `min(true, inf)` then the cell holds `min(textbook recurrence, inf)` | checked (algebra) |
| `Ted.fdist` (`Ted/Model.lean`) | the textbook forest recursion as a Lean function, `fdist_node` (the equation), `fdist_leaf_leaf` | a model, nothing about Rust |

**Not proved (item (c) of the TED task):** that the banded `fill_window`/`within_td` tables equal `min(Ted.fdist, tau+1)`.
What is missing is (1) the loop-level statement that a whole row `q in [qlo, qhi]` satisfies the one-cell equation with
neighbours read from the final table (needs the band index to be injective, `bandIdx_inj`, proved in `Ted/Cell.lean`, and the row
loop invariant), (2) the identification of the table cell `(p, q)` of window `(i0, j0)` with `fdist` of the postorder
prefixes `li .. li+p-1` and `lj .. lj+q-1` read as forests, (3) the Zhang-Shasha lemma that the `td` entries read by the
non-leaf-path branch are the subtree distances computed by an earlier window (keyroot order), (4) that cells outside the
band cost more than `tau` (the size-difference bound on `fdist`), (5) the early exit on `row_min > tau`, and (6) the
`within_td` driver (keyroot loops, the `|li - lj| <= 2 t` skip). `ted_oriented`, `ted_stats`, `mirror`, `ted_mapping`,
`check_mapping` and `replay_script` are not extracted at all. Axiom output: `AXIOMS-ted.txt`.

What backs the TED solver instead is testing, not proof: a brute-force forest-recursion oracle on 6,000 random pairs,
agreement of all distances with two APTED implementations on 237 real ASTs, validated mappings and an executed
edit-script replay (see `notes/lanes/RESULTS.md`).

The stock Charon and Aeneas releases were used, not apeiron's patched build, so apeiron's `regen.sh` identity
check would reject these digests. `last_nl`, the line differ's Myers search and the interner are not covered.

## Line search (`src/lines.rs`)

Two layers. **Layer 1 (`Myers/*.lean`, plain Lean 4.31.0, no Mathlib)** is a Lean model of the algorithm with
its optimality theorem. **Layer 2 (`Myers2/Real*.lean`, over Aeneas)** proves that the Aeneas translation of the
real `src/lines.rs` search refines that model. Both layers have zero `sorry` and use only `propext`,
`Classical.choice`, `Quot.sound` (`AXIOMS-myers.txt`, `AXIOMS-myers-extract.txt`).

Build: `./run-myers.sh Lcs Script Solve Snake Reach Compl Path Mid Good Pipeline Bound Glue TrimSpec Splice SolveLen CpreChar AxiomAudit`
then `AENEAS_HOME=... ./extract-real.sh` and `LEAN_WS=... ./check-real.sh RealCommon RealSnake RealDefs RealX0 RealFwd
RealSnakeBack RealBack RealScan RealBits RealHalve RealSweep RealMiddle RealSolve` (oleans in `build-myers/`).

### Layer 1: the model (proved)

| obligation | theorems (file) |
|---|---|
| `lcs`, sublist characterisation | `lcs_le`, `lcs_ex` (Lcs) |
| (a) trimming equal ends | `lcs_prefix`, `lcs_suffix`, `lcs_trim` (Lcs), `opt_trim` (Script) |
| (b) dropping ids absent from the other side | `lcs_filter`, `kept_expand`, `filter_optimal` (Script) |
| (c) script soundness and optimality | `cost_eq`, `cost_ge`, `optimal_iff`, `exists_optimal`, `optimal_min` (Script) |
| (d) divide step, model of `solve` | `optimal_append` (Script), `solve_optimal`, `solve_total` (Solve) |
| (e) furthest-reaching recurrence | `F_sound` (Reach), `compl_all` (Compl), `F_le` (Bound) |
| (e) middle snake, both parities | `path_point`, `exists_hit`, `sweep_sound`, `sweep_some`, `fhit_good`, `bhit_good`, `two_le`, `midPt_spec`, `mid_spec` (Path, Mid, Good) |
| pipeline | `line_search_optimal`, `line_search_cost` (Pipeline) |

### Layer 2: the real extracted code refines the model (proved)

The real `src/lines.rs` is included by `#[path]` (`extract-myers/lib.rs`); Aeneas translates it with no copies
(`gen/lean-real/DifffoldReal.lean`, `gen/RECEIPT-real.txt`). `src/lines.rs` was refactored without changing
behaviour (`or_else` as `match`, `snake`/`snake_back` take the two slices). Under the precondition
`|A| + |B| <= 2^28` (so no `i32` overflow; the `i32` side goals are discharged in the proofs):

| extracted function | theorem | states |
|---|---|---|
| `common_prefix`, `common_suffix` | `common_prefix_u32`, `common_suffix_u32` (RealCommon) | length, equal ends, maximality |
| `snake`, `snake_back` | `snake_spec` (RealSnake), `snake_back_spec` (RealSnakeBack) | equals the model run length, with size bounds |
| `forward_one` | `forward_one_spec` (RealFwd, RealX0) | writes `vf[off+k] = F A B d k`, reports the model overlap, reads only what round `d` is entitled to |
| `backward_one` | `backward_one_spec` (RealBack) | the same for `vb` with the reversed lists; reported point is `(n - Bk, m - (Bk - k))` when nonnegative |
| `forward_seq`, `backward_seq` | `forward_seq_spec`, `backward_seq_spec` (RealScan) | scan of `lo, lo+2, .., hi`: first hit, written entries, untouched entries |
| `forward`, `backward` | `forward_spec`, `backward_spec` (RealHalve) | the halving visits the same diagonals, leftmost hit wins |
| `sweep` | `sweep_spec` (RealSweep) | returns exactly the model `Myers.sweep` result (arrays hold `F` at every round, indices in bounds) |
| `middle` | `middle_spec` (RealMiddle) | returns the model `midPt`, scratch arrays keep their sizes |
| `solve` | `solve_spec` (RealSolve) | the flag arrays receive the flags of `Myers.Solve Myers.mid`, hence (by `solve_optimal`, `mid_spec`) a minimal edit script |

`Myers.Solve Myers.mid` is optimal by `solve_optimal`, so the real `solve` writes a minimal script into the
segment it is given.

### Not yet done (open, nothing here is claimed proved)

- `diff_ids`: still uses `each` closures (compaction of ids that occur on one side only). It must be refactored to
  plain recursion, extracted, and connected to `filter_optimal` and `trim` (model lemmas exist).
- `diff_text_with`: the byte-level cut (`line_start`, `suffix_on_line_start`, `count_lines`, `split_lines`,
  `first_nl`/`last_nl` with `trailing_zeros`, `count_ones`), final-newline handling, and the application of the
  script to the texts.
- `intern`: uses `std::collections::HashMap` with a keyed hasher; Aeneas has no model of it. Planned replacement:
  an open-addressing interner with real byte equality on probe, then a proof that equal ids mean equal lines.
- `Algo::Histogram` (`hist`, `find_anchor`, `walk_chain`, `index_a`): soundness (valid script) not started;
  optimality is not claimed for it.
- Performance check of the refactors with `linebench` has not been re-run.

Earlier, smaller extraction of closure-free copies (`extract/myers_core.rs`, `Myers2/CommonCopy.lean`,
`Myers2/SnakeSpec.lean`, `tests/myers_core.rs`) is superseded by the real-source extraction above and kept only as
a record.

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
