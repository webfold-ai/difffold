# Bounded unit-cost Levenshtein over token sequences

Status: implemented in `src/levenshtein.rs`, exported as `difffold::levenshtein`. Exact, tested,
not proved. No Lean proof is claimed for any part of this module. The current revision is version 2: it
adds a wavefront kernel, a symbol-count lower bound and a banded bit-parallel kernel, and replaces the
dispatcher. The version 1 measurements are kept below, labelled as history.

## Objective: three distances that must not be confused

| Distance | Operations and costs | Where in the repo | Example `[1,2,3]` vs `[1,9,3]` |
|---|---|---|---|
| Indel (LCS) | insert 1, delete 1, no substitution | `src/lines.rs` (Myers line diff) | 2 (delete 2, insert 9) |
| Unit-cost Levenshtein | insert 1, delete 1, substitute 1 | `src/levenshtein.rs` | 1 |
| Weighted | relabel cost depends on node kind | `src/ted.rs` (`PostTree::with_kinds`) | 1 within a kind, 2 across kinds |

Levenshtein is the objective of this module. Indel distance is what `lines` measures and it prices a
relabel as two edits. The two agree only when no substitution can help. The test
`indel_distance_differs_from_levenshtein_on_a_relabel` pins that case. The weighted objective is not
implemented here.

## Contract

- `levenshtein_within(a, b, limit: u32) -> Option<u32>`: the exact distance if it is at most `limit`,
  else `None`. Never a silent saturation: a limit larger than `usize` is clamped to `usize::MAX`, which
  is above any representable length, so the answer is unchanged.
- `levenshtein(a, b) -> u32`: the exact distance, found by threshold doubling `1, 2, 4, ...` capped at
  `max(n, m)`. Its cost follows the distance. It panics only if the distance exceeds `u32::MAX`, which
  needs an input longer than 4 billion tokens. The panic is documented.
- `levenshtein_within_u32(a: &[u32], b: &[u32], limit: u32) -> Option<u32>`: the same contract for
  integer ids, with dense or sorted class lookup instead of a linear scan.
- Hidden, for the test suite and benchmark only: `levenshtein_full_dp` (oracle),
  `levenshtein_within_band`, `levenshtein_within_wavefront`, `levenshtein_within_myers_single`,
  `levenshtein_within_myers_multi`, `levenshtein_within_myers_banded`, `histogram_lower_bound_u32`.

Every element type needs only `T: Eq`. Hashing and ordering are not required; the generic path uses a
linear class scan, and the `u32` path uses a table or binary search.

## Version 2 (kernels and dispatch)

This revision adds three exact kernels and replaces the dispatcher. The public entry points are unchanged:
`levenshtein_within`, `levenshtein`, `levenshtein_within_u32`. Hidden test and benchmark hooks gained
`levenshtein_within_wavefront`, `levenshtein_within_myers_banded` and `histogram_lower_bound_u32`.

Algorithms, in the order the code runs them:

1. Trim the common prefix and suffix. Both are compared in 16-token chunks, so long matches cost one slice
   comparison per chunk.
2. Length check: `||a| - |b|| > k` is an immediate `None`.
3. Choose a kernel by the cost model in `choose_kernel` (below).
4. Wavefront (furthest-reaching diagonals, the Ukkonen/Myers O(ND) idea, as in WFA's edit mode). A diagonal
   `d = j - i` keeps only its furthest reached pattern position for the current score. Monotonicity along a
   diagonal (`D[i+1][j+1] >= D[i][j]`) makes that position a complete summary. Each score step takes one
   substitution, deletion or insertion from the previous score's neighbours, then slides along matches. The
   work is `O((k + 1)^2)` diagonal steps plus the match extension.
5. Rolling band (Ukkonen), as before, with the row-budget probe removed.
6. Symbol-count lower bound (u32 path only, before a band or bit-parallel run). `sum over symbols of
   max(0, count_a - count_b)` never exceeds the distance: an edit changes this excess by at most one, and
   the excess is zero for equal multisets. Dense ids are counted in linear time; sparse ids are sorted.
7. Bit-parallel. Patterns of at most 64 tokens use the single-word kernel. Longer patterns use the banded
   multiword kernel: in each text column only the blocks that hold a row of the band `|i - j| <= k` are
   updated. The blocks above the band are dropped; the top boundary of the first active block takes the
   horizontal delta `+1`, the same boundary as row 0. Values below the band are added as the band grows.
   The full multiword kernel is kept as a test hook.

Cost model (`choose_kernel`), in nanoseconds on the reference machine:

- rolling band: `n * (2k + 1) * CELL_COST`, with `CELL_COST = 4`;
- bit-parallel: `m_text * (window_blocks * BLOCK_COST + lookup)`, with `BLOCK_COST = 8` and
  `window_blocks = min(blocks, ceil((2k + 1) / 64) + 1)`, `lookup = 0` for the single-word kernel;
- wavefront: `(k + 1)^2 * WF_STEP_COST`, with `WF_STEP_COST = 10`.

The cheapest wins; ties go to the band. The constants were fitted on this machine with `taskset -c 0`:
the rolling band at about 4 ns per cell, the banded kernel at about 4 to 12 ns per window block per
column, and the wavefront at about 8 ns per step on alphabet 256 and 15 to 20 ns on alphabet 2 and 4
(the model uses 10, so it under-prices the wavefront on small alphabets; no decision in the sweep flipped
because of this). They are not portable.

Correctness argument for the banded kernel (informal; tested, not proved):

- Every value computed is at least the true value, because the approximate top boundary and the blocks
  added below are upper bounds, and min-plus recurrences are monotone.
- An optimal path of cost at most `k` stays inside `|i - j| <= k`, so every cell on it is computed exactly.
  Hence `D[m][n]` is exact whenever it is at most `k`, and it is above `k` otherwise.
- No column-minimum cutoff is used. A bottom-row bound `D[m][j] - (n - j)` is valid only for the true
  values, and the banded grid only gives upper bounds, so that cutoff would be unsound here.

Wavefront argument: monotonicity along diagonals makes the furthest point a complete summary; the
candidates are exactly the moves from the previous score; out-of-range moves are never generated because
each move checks the bound of the cell it leaves.

## Version 2 tests

`tests/levenshtein.rs` keeps every test of version 1 and adds:

- `wavefront_exhaustive_alphabet3_length6`, `wavefront_exhaustive_alphabet4_length5`: every pair, both
  orientations for alphabet 3, every limit `0..=max+1`, against the oracle;
- `banded_bit_parallel_exhaustive_small`: the banded kernel on the same exhaustive set;
- `banded_bit_parallel_multiword_boundary_lengths`: lengths 63, 64, 65, 127, 128, 129, 191, 192, 193 over
  alphabets 2, 4, 256 and sparse ids, thresholds around the distance, and the bounds 1, 8, 32 and 128;
- `random_long_pairs_threshold_regimes`: lengths 200 to 2000, alphabets 2, 4, 256 and sparse ids, with
  `d > k`, `d == k`, `d < k` and `d >> k` cases;
- `histogram_bound_never_exceeds_distance_exhaustive` and `..._random`: the dense and sparse branches
  against the oracle, and the identities used by the bound.

### Version 2 measurements

Machine: Intel Xeon @ 2.10 GHz (virtualised, 4 vCPUs). Every timed run is pinned with `taskset -c 0`, and
the release build has `debug = 0`. A timed cell runs seven passes after one warm-up, and the median is
reported. The 1-minute load at the start of each cell is recorded in the TSV. Another agent's benchmark
shared CPU 0 for part of the session, so cell timings carry noise of the order of 10 to 30 percent, and
the sub-microsecond cells are close to the timer's resolution.

Fitted constants used by `choose_kernel` (nanoseconds, this machine):

- rolling band: about 4 ns per cell (`CELL_COST = 4`);
- banded bit-parallel: about 4 to 12 ns per window block per text column (`BLOCK_COST = 8`);
- full multiword bit-parallel, for comparison: about 9 ns per block per column;
- wavefront: about 8 ns per diagonal step on alphabet 256, and 15 to 20 ns on alphabets 2 and 4
  (`WF_STEP_COST = 10`, which under-prices the wavefront on small alphabets).

A kernel-level sweep of the integer-id path against the wavefront alone (lengths 1,000 to 100,000, k from 1
to 128) found the chooser never slower than the wavefront where the wavefront was the cheaper kernel, and
3 to 8 times faster than the wavefront where the band or bit-parallel kernel was the cheaper one (for
example 54 us against 277 us at length 1,000, alphabet 2, k = 128). It did not flip any decision when the
wavefront constant was varied within the measured range, so the constant was not changed.

Correctness and mutation checks (final source):

| check | result |
|---|---|
| `tests/levenshtein.rs` | 18 passed, 0 failed (11 kept from version 1, 7 new) |
| workspace `cargo test --locked --workspace` | 67 passed, 0 failed |
| mutation M1: wavefront deletion candidate `del + 1` to `del` | caught by `wavefront_exhaustive_*`, but as an arithmetic underflow panic in `extend` (a bad index), not a clean oracle mismatch |
| mutation M2: banded top boundary `hin = 1` to `0` | caught by `banded_bit_parallel_*` (oracle mismatch) |
| mutation M3: histogram excess `+ 1` on the positive count | caught by both `histogram_bound_*` tests |
| mutation M4: wavefront termination `>= n` to `> n` | caught by `wavefront_exhaustive_*` |

Each mutation was applied once to the source, the named tests were run, and the file was restored and
checked against its SHA-256 afterwards. The first run of the M3 script had a bad argument split and
aborted before changing the file, and M3 was run again with the arguments passed correctly.

One experiment was not kept. Running the symbol-count bound before the wavefront for dense ids made
unrelated pairs with a small bound about 230 times slower at length 100,000, because the linear pass costs
more than the wavefront's early exit. It was reverted, and the code described here is the final code.

Bounded and exact matrix results (subset of `tools/strbench`, run this session; the full tables are in
`STRING-BASELINES.md`, section "After v2"):

- Bounded job, difffold before and after, RapidFuzz in the same run. Geometric mean of the after/before
  ratio: 0.22 at length 1,000, 0.068 at 10,000 and 0.028 at 100,000. Against RapidFuzz after the same
  run, difffold is faster in 37 of 80 cells at length 1,000 (8 are ties within 1.3x, 35 are slower),
  59 of 80 at 10,000 (5 ties, 16 slower) and 70 of 80 at 100,000 (1 tie, 9 slower).
- Exact job: the wavefront and the threshold doubling make similar pairs far cheaper. For example, at
  length 100,000 and alphabet 2 with 16 edits, difffold takes 50 us against 37 ms before. Unrelated exact
  pairs at length 100,000 still time out at 60 s for difffold, as they did before.

Known losses (version 2):

- Unrelated pairs with a small or moderate bound on alphabets 256 and sparse ids, and on alphabet 2 at
  k = 128, are slower than before. The version 1 band exited after a few rows on these pairs, and the
  wavefront does not. The slowdown ranges from about 1.2 to 4.5 times on the affected cells, and the
  largest absolute cost is about 0.3 us to 14 us per pair at small k (the affected cells are listed in
  `STRING-BASELINES.md`).
- Sparse ids at length 1,000 with k = 128 are about 1.4 times slower than before. The difference is about
  the cost of the sort that the symbol-count bound makes for sparse ids before a band or bit-parallel run.
  This is inferred from the size of the difference and was not profiled.
- The banded kernel has no column-minimum cutoff, so it does not exit early on dissimilar pairs with
  a mid-range bound. The symbol-count bound and the wavefront cover the unrelated cases that matter at
  these bounds.
- The generic path (`levenshtein_within`, `levenshtein`, used for non-integer tokens) has no symbol-count
  bound, because it needs no hashing for the other kernels.
- Edlib and WFA2-lib were not rebuilt in this session. Their rows are the results of the previous matrix,
  not re-measured, and the source trees needed to build them are not on this machine.


## Version 1 history

The measurements below are for version 1 (rolling band and full bit-parallel only, with the row-budget probe).
They are kept for comparison and do not describe the current code.

### Measured crossover (version 1)

Machine: Intel Xeon @ 2.10 GHz (virtualised, 4 vCPUs), one core pinned with `taskset -c 0`, release
build, one warmup pass and 7 timed passes, median reported. Times are for the whole pair set (8 pairs
up to length 1024, 4 pairs up to 4096, 2 pairs at 20000). Timer noise is about 10 to 20 percent, and
at lengths 16 and 64 it dominates. Every timed result is checked against the exact distance first.

Headline, from the final grid (2560 timed cells, 634 where the dispatcher and all three fast kernels
ran):

- The dispatcher's median ratio to the best fast kernel, by length: 1.50 (16), 1.22 (64), 1.14 (256),
  1.11 (1024), 1.03 (4096), 1.01 (20000). At small sizes the gap is per-call overhead, which is noise
  at microsecond scale.
- It is within 1.25x of the best fast kernel in 417 of 634 cells. The best fast kernel was the band in
  421 cells, the integer-id path in 133 and single or multiword bit-parallel in 80.
- Worst cases, all on dissimilar pairs (`far`) with a small or moderate limit, where the band empties
  early: 96x at length 20000 over alphabet 256 with k=128 (11.3 ms against 0.12 ms, both absolute
  times tiny for a 20000-token pair); 20x at length 1024 over alphabet 4 with k=8.
  Before the bounded band probe these reached 136x. The probe bounds the loss but does not remove it.
- Generic path on large alphabets has a long tail: on sparse ids at length 1024 the dispatcher is up to
  15x slower than the integer-id path (k=128, `eq` case). The class scan costs one comparison per class
  per token. Across all cells with length 256 or more, the median dispatcher time over the median
  integer-id time is 0.95, so the integer-id path is not uniformly faster. It is kept because the
  generic path's tail on wide alphabets is the case it removes.

Crossover (the `eq` case, where `d == k`). Cell letter is the fastest kernel: B = band,
P = bit-parallel (generic, single or multiword), U = integer-id path. `*` means the dispatcher was more
than 1.25x slower than that kernel. `-` means no pair with `d == k` was found.

```
len  | alph       | k1    k2    k4    k8    k32   k128
16   | 2          | B*    B*    P     P     -     -
16   | 4          | U*    B*    P     P*    -     -
16   | 256        | U*    B*    B*    P     -     -
16   | sparse_u32 | U*    B*    B*    P     -     -
64   | 2          | B     P     P     P     -     -
64   | 4          | P     B     P     P     -     -
64   | 256        | B     B*    U     U*    U*    -
64   | sparse_u32 | B     B     B     U*    -     -
256  | 2          | B     P     P     P     -     -
256  | 4          | B     B     B     U     U     -
256  | 256        | B*    B     B     U     U*    -
256  | sparse_u32 | B     B     B*    B     U*    -
1024 | 2          | P     B*    B*    U     -     -
1024 | 4          | B     B     B*    B*    U     -
1024 | 256        | P     U     B*    B     U*    U*
1024 | sparse_u32 | B     B     B     B*    U     U*
4096 | 2          | B     B     B     B     -     -
4096 | 4          | B     B     B     B     B     -
4096 | 256        | B     U     U     B     B     U*
4096 | sparse_u32 | B     U     B*    U     B     U
20000| 2          | B     B     U     B     B     -
20000| 4          | U     B     U     B     B     -
20000| 256        | B     U     B     B*    U     B
20000| sparse_u32 | B     B     B     B     B*    B
```

Reading the table: at small k the band wins at every length, so the sharpest benefit of the bit-parallel
kernels is at larger k. Cells flip between B, P and U where the kernels are within noise of each other.
The dispatcher's `*` cells are mostly those near these ties, plus the dissimilar-pair losses above.

### Real AST label sequences (version 1)

Inputs: 25 consecutive-revision pairs of Rust source files from this repository's git history
(`src/ted.rs`, `diff.rs`, `lines.rs`, `intern.rs`, `mapping.rs`, `frontier.rs`, `kernel.rs`, `merge.rs`),
parsed with tree-sitter-rust. Token sequences are kind ids, in preorder and postorder. That gives 50
sequences, 50 pairs (each file pair contributes its preorder and its postorder sequence), and lengths up
to 11,722 tokens. Each timed result is checked against the exact distance first.

Median time per pass over the 50 pairs (ms), `lev_bench app`:

| limit k | band | bit-parallel | dispatch | integer-id path |
|---|---|---|---|---|
| 1 | 0.207 | 0.233 | 0.236 | 0.162 |
| 2 | 0.121 | 0.208 | 0.113 | 0.153 |
| 4 | 0.149 | 0.264 | 0.144 | 0.238 |
| 8 | 0.341 | 10.325 | 0.352 | 0.428 |
| 32 | 16.302 | 49.069 | 15.391 | 23.687 |
| 128 | 103.172 | 100.873 | 125.835 | 94.059 |

At k up to 8 every kernel takes well under a millisecond per pass, and the dispatcher matches the best
kernel. At k=32 the band is fastest (16.3 ms), and the dispatcher is within 6 percent of it. At k=128 the
integer-id path is fastest (94 ms), and the dispatcher is about 25 percent slower. The alphabet of kind
ids was not counted, so the alphabet explanation for the integer-id win is not checked.

Tree edit distance check: `ted_checked=3`, `ted_bound_violations=0`. Only 3 file pairs had both trees at
or below 1500 nodes, so this is a weak check. It confirms the bound on those three pairs and nothing more.

### Limitations (version 1, superseded by the version 2 list above)

- The bit-parallel kernels have no Ukkonen-style cutoff. For dissimilar pairs with small `k` the band
  empties after roughly `k` rows, far faster than a full bit-parallel pass. The bounded band probe
  recovers most of this, but a probe that does not finish in its budget still pays a quarter of the
  bit-parallel work. Residual losses on dissimilar pairs remain (up to 96x at length 20000, k=128, see
  above). A real fix would be a cutoff inside the bit-parallel kernel.
- The cost model is fitted on one machine. The constants are measured, not portable.
- The generic path's class scan costs one comparison per class per token, so large alphabets on that
  path are slow. The integer-id path avoids this.
- Trimming makes some workloads cheap. The `lt` and `affix` cases shrink to a short middle, so they
  overstate the benefit for those inputs.
- No traceback (edit script). No weights. No wavefront algorithm.
- The `levenshtein` function panics if the distance does not fit `u32`. Use `levenshtein_within` for
  bounded queries.

### Relation to tree edit distance

For ordered trees, the Levenshtein distance between preorder (or postorder) label sequences is a lower
bound of the unit-cost tree edit distance. A tree mapping preserves ancestor and sibling order, so it
induces an alignment of the two sequences whose cost is at most the mapping's cost. The bench checks
this on real Rust ASTs for trees up to 1500 nodes, using `difffold::ted::ted`.

This module is not wired into `ted` or into any filter. Another lane has a private
bounded Levenshtein that will be unified with this one later.

### Not yet compared against external libraries (version 1)

Not yet compared against Edlib, RapidFuzz or WFA2. A separate agent will build and run them against this
kernel. This line is updated when that agent reports.

### Command line

`cargo run --release --example levenshtein_tokens -- a.txt b.txt [--limit K]` prints the exact distance,
or `exceeds K` when a limit is given and the distance is larger. Each file holds whitespace-separated
`u32` token ids. The exit status is nonzero on bad input.

### Benchmark

`cargo run --release --features ts --bin lev_bench -- synthetic [quick]` and
`cargo run --release --features ts --bin lev_bench -- app <dir>`. Run under `taskset -c 0`.
The `app` mode reads `NAME.a.rs` and `NAME.b.rs` pairs from `<dir>`.
