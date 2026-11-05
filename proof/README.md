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
| `ted_oriented_loop_spec`, `ted_oriented_spec` | the threshold-doubling loop of `ted_oriented` terminates and returns exactly `ted` (non-empty trees, single roots, `tau <= n + m`, fewer than `2^14` nodes per tree) | `Oriented` |
| `ted_eq_min_mapping` | `ted` is the minimum cost of a valid tree edit mapping, and a mapping with that cost exists | `Oriented`, `Mapping` |
| `cell_step`, `get_spec`, `bidx_spec`, `relabel_cost_spec` | one inner-loop iteration and the arithmetic helpers, including the kind-aware relabel cost 0/1/2 | `Cell` |

Hypotheses of the driver theorem (all stated, none assumed silently): `WfL` of both leftmost-leaf maps (subtrees are intervals that nest), a
single root (`lml n = 1`), keyroot lists that are sorted and exactly the last node per leftmost leaf (`from_kids_spec` gives this), fewer than
`2^14` nodes per tree and `tau <= n + m` so that no `usize` addition overflows on a 32-bit platform.

**Not done** (reported honestly): `ted_stats` (the left/right path choice) with `mirror` and the invariance of the distance under
mirroring (`mirror_expand` uses closures and recursion over child lists, not extracted), `ted_mapping` (the traceback),
`check_mapping` and `replay_script` (they use `HashMap`, `splice`, `mem::take`) are neither extracted nor proved. `WfL` of the
`lml` array that `from_kids` builds (subtrees are nested intervals) is assumed as a hypothesis, not derived from a validity
predicate on the child lists; `Keys` (sorted keyroots, exactly the last node per leftmost leaf) follows from `from_kids_spec` but the
translation lemma is not written. The size limits (fewer than `2^14` nodes) come from Aeneas modelling `usize` as 32 or 64 bits.

## Line search (`src/lines.rs`)

Two layers. **Layer 1 (`Myers/*.lean`, plain Lean 4.31.0, no Mathlib)** is a Lean model of the algorithm with
its optimality theorem. **Layer 2 (`Myers2/Real*.lean`, over Aeneas)** proves that the Aeneas translation of the
real `src/lines.rs` search refines that model. Both layers have zero `sorry` and use only `propext`,
`Classical.choice`, `Quot.sound` (`AXIOMS-myers.txt`, `AXIOMS-myers-extract.txt`). An earlier `bv_decide` proof of one bit lemma pulled in a native-code axiom; it is now a kernel proof and the audit shows the three only.

Build: `./run-myers.sh Lcs Script Solve Snake Reach Compl Path Mid Good Pipeline Bound Glue TrimSpec Splice SolveLen CpreChar Text HistPure AxiomAudit`
then `AENEAS_HOME=... ./extract-real.sh` and `LEAN_WS=... ./check-real.sh RealCommon RealSnake RealDefs RealX0 RealFwd
RealSnakeBack RealBack RealScan RealBits RealHalve RealSweep RealMiddle RealSolve RealCompact RealDiffIds` and then `RealSwar RealWord RealNL RealLines RealSplit RealCut InternExact RealIntern RealHist RealText RealDiffText` (oleans in `build-myers/`).

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
| `mark_ids`, `compact_ids`, `scatter_flags` | `mark_ids_spec`, `compact_ids_spec`, `scatter_flags_spec` (RealCompact) | equal their sequential models (`markOf`, `posOf`/`editOf`, `scatterOf` of `Compact.lean`) |
| `diff_ids` | `diff_ids_spec` (RealDiffIds) | for ids below `n_ids` and `|A|+|B| <= 2^28`, returns flags with `Myers.Optimal A B da di`, a minimal edit script, through prefix/suffix cut, one-sided id compaction, the real `solve`, and scatter back |
| `solve` | `solve_spec` (RealSolve) | the flag arrays receive the flags of `Myers.Solve Myers.mid`, hence (by `solve_optimal`, `mid_spec`) a minimal edit script |

`Myers.Solve Myers.mid` is optimal by `solve_optimal`, so the real `solve` writes a minimal script into the
segment it is given.

### Layer 2b: the byte level and the whole differ (proved)

`Myers/Text.lean` (plain Lean, no Mathlib) models a text as a list of byte values: `lines` (each line keeps its
`\n`, a final unterminated line is kept, no empty trailing line; `lines_spec` gives flatten, nonempty chunks,
newline only at a chunk end), `applyS` (apply a flag script: drop deleted lines, take inserted lines from the
new side, copy kept lines; `applyS_eq` shows it rebuilds the new side from any valid script), `MinL` (valid and
no valid script is cheaper, for arbitrary elements), its transport from the id model (`minL_of_optimal`,
`optimal_of_minL`, `VL_map`) and `minL_trim` (equal leading and trailing lines may be cut: this is `opt_trim`
at line granularity). Over the real extraction (`Myers2/RealSwar`, `RealWord`, `RealNL`, `RealLines`,
`RealSplit`, `RealCut`, `RealText`, `RealDiffText`):

| extracted function | theorem | states |
|---|---|---|
| `nl_mask`, `newline_count`, `lowest_byte`, `word` | `nl_mask_spec`, `newline_count_spec`, `lowest_byte_spec`, `word_spec` | the SWAR mask marks exactly the `0x0A` bytes of the little-endian word, the multiply-and-shift sums the marks, `lowest_byte` is the first marked byte, `word` loads the first eight bytes zero padded (kernel proofs, no `bv_decide`) |
| `first_in_block`, `first_nl`, `last_in_block`, `last_nl` | `first_in_block_spec`, `first_nl_spec`, `last_in_block_spec`, `last_nl_spec` | index of the first (last) `0x0A` or none |
| `count_block`, `count_byte`, `count_lines` | `count_block_spec`, `count_byte_spec`, `count_lines_spec` | the number of newlines; `count_lines t` is `(lines t).length` |
| `split_seq`, `split_into`, `split_lines` | `split_seq_spec`, `split_into_spec`, `split_lines_spec` | the slices pushed are exactly `lines t` in order (halving at a newline, depth `O(log n)`) |
| `line_start` | `line_start_spec` | start of the line holding byte `p` (`0` or just after a `0x0A`, no newline between) |
| `shrink_suffix`, `suffix_on_line_start` | `shrink_suffix_spec`, `suffix_on_line_start_spec` | the shrunk common suffix is still common and starts a line in both texts |
| `diff_text_core` | `diff_text_minimal` (RealText) | given `LineIdsExact inst` (the interner assigns equal ids exactly to equal lines), for `Algo::Minimal` the returned flags `(da, di)` satisfy `MinL (lines old) (lines new) da di` (a valid script, no valid script is cheaper) and `(applyS (lines old) (lines new) da di).flatten = new`, through the byte prefix cut, the suffix cut, `split_lines`, `intern`, the real `diff_ids`, and the `copy_from_slice` assembly |
| `intern_seeded`, `diff_text_core` | `diff_text_minimal_seeded` (RealDiffText) | the interner contract is discharged for the real `intern_seeded` for every seed (`seeded_exact`, from `intern_seeded_spec`), so the end theorem holds for the production interner up to its seed |

Hypotheses of `diff_text_minimal`: `old` and `new` have at most `B` bytes with `B + 8 <= Usize.max` (so the
word-at-a-time scans cannot overflow) and the two texts have at most `2^28` lines together (the `i32` bound of
the line search). `src/lines.rs` was refactored without changing behaviour: `diff_text_with` is now
`diff_text_core::<HashLines>`, generic over a private trait `LineIds` (interning and the histogram differ), which
Aeneas turns into an explicit instance argument; the `Algo::Minimal` path calls `diff_ids` directly.
The cut is not required to be maximal: any common prefix ending at a line start and any common suffix starting
at a line start give an optimal script for the middle (`minL_trim`).

### Layer 2c: the interner and the histogram differ (proved)

`intern` (the hash-table interner) was rewritten without changing any output: equal lines get equal ids, ids are
dense in `0..n_ids` and given in order of first appearance. The std `HashMap` with a custom `Hasher` and the
`each` closures, which Aeneas cannot extract, were replaced by a table of `a.len() + b.len()` buckets (a power of
two) over `Vec`s: `head[bucket]` is the newest id in the bucket, `nxt[id]` the next older id, `reps[id]` the line,
and a probe walks the chain comparing the real bytes (`find_in_chain`, a tail call that ends because links point
to older ids). The keyed hash only chooses a bucket (`hash_line`, a `while` loop over eight-byte words); the seed is
a parameter of `intern_seeded`, and `intern` passes a fresh random seed. This is chaining over index vectors, not
open addressing: the termination argument is that links strictly decrease, so no "table never full" side
condition is needed. Loops over `&[&[u8]]` do not extract (nested borrows), hence the halving recursion
`intern_all`; `Hist` no longer holds the id slices.

| extracted function | theorem | states |
|---|---|---|
| `hash_line` | `hash_line_total` (RealIntern) | the hash never fails (the only property of it that is used) |
| `table_size` | `table_size_spec` | result is at least 2 and at least the requested size, no overflow for `<= 2^28` lines |
| `find_in_chain` | `find_in_chain_spec` | returns an id whose stored line equals the query, or `NIL` when no id on the chain does |
| `intern_line`, `intern_all` | `intern_line_spec`, `intern_all_spec` | invariant `TInv` (chains reach every stored line, stored lines pairwise distinct, links decrease) is preserved; the new id is the next free one exactly when the line is new |
| `intern_seeded` | `intern_seeded_spec` (RealIntern) | for `|la| + |lb| <= 2^28`, every seed: `InternExact la lb ia ib n` (`InternExact.lean`): one id per line, ids below `n`, ids equal exactly when the byte lists are equal (within and across the two sides), every id below `n` is used |
| `index_a`, `unindex_a` | `index_a_spec`, `unindex_a_spec` (RealHist) | chain heads, links and counts of `a[alo..ahi)` are well formed; `unindex_a` restores the all-empty state |
| `walk_chain`, `find_anchor` | `walk_chain_spec`, `find_anchor_spec` | every anchor found is a run of equal ids inside both ranges, `bl < len` |
| `any_common` | `any_common_spec` | never fails |
| `hist_fallback` | `hist_fallback_spec` | the real `solve` on the range; the result is a valid script (`solve_optimal`) |
| `hist` | `hist_spec` | for ranges whose flags are unset and a clean state, the flag arrays receive a valid script for the range: `HPost` (`HistPure.lean`), kept lines of the two ranges equal; trimming, the two fill cases, the anchor split and the fallback are all covered |
| `diff_histogram_ids` | `diff_histogram_ids_spec` (RealHist) | for ids below `n_ids` and `|A|+|B| <= 2^28`, returns flags with `Myers.Valid A B da di`: deleting the flagged old lines and inserting the flagged new lines turns `A` into `B` |

The histogram theorem is soundness only. No optimality is claimed: the result is in general not minimal (the
anchor choice is a heuristic), and nothing here relates its cost to `lcs`. Its recursion depth cap
(`HIST_DEPTH`) and the occurrence limit (`HIST_LIMIT`) are not needed for validity and are not reasoned about
beyond the `u32` increment of the depth.

Performance of the refactors (release build, same machine, outputs byte for byte identical on every fixture):
PERF_PLACEHOLDER

### Not yet done (open, nothing here is claimed proved)

- `diff_text_with` itself is not extracted: it calls `intern` with `random_seed` (std `RandomState`). The end
  theorem is stated for `diff_text_core` with the real `intern_seeded` and an arbitrary seed.
- Optimality of `Algo::Histogram` is not claimed and is false in general; `diff_histogram_ids_spec` is the only
  statement about it.

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
