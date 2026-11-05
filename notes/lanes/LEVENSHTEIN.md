# Bounded unit-cost Levenshtein over token sequences

Status: implemented in `src/levenshtein.rs`, exported as `difffold::levenshtein`. Exact, tested,
not proved. No Lean proof is claimed for any part of this module.

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
  `levenshtein_within_band`, `levenshtein_within_myers_single`, `levenshtein_within_myers_multi`.

Every element type needs only `T: Eq`. Hashing and ordering are not required; the generic path uses a
linear class scan, and the `u32` path uses a table or binary search.

## Algorithms

1. Trim the common prefix and suffix. This is valid for unit-cost Levenshtein: for equal first tokens,
   an optimal alignment can always match them, so `lev(xA, xB) = lev(A, B)`, and symmetrically for
   suffixes. Trimming is not one-sided token elimination, which is invalid: a token absent from the
   other side can still be substituted at cost 1.
2. Length check: `||a| - |b|| > k` is an immediate `None`.
3. Band (Ukkonen): row `i` holds columns `j` in `[i - k, i + k]` in a `2k + 1` buffer, two rows kept,
   `O(k)` memory. Values are capped at `k + 1`. The row loop has no per-cell range checks. It exits
   as soon as every cell of a row exceeds `k`.
4. Bit-parallel (Myers 1999, global form with Hyyro's block carries): one 64-bit block per 64 pattern
   tokens. Single-word kernel for patterns of at most 64 tokens, multiword kernel otherwise. The
   pattern is the shorter side. The score tracks the bottom cell and exits when it cannot return to
   `k`.
5. Match masks: one row per distinct pattern class plus a zero row. Their size is
   `(classes + 1) * blocks` words, bounded by the pattern length squared over 64, and capped at
   `MAX_MASK_WORDS = 2^21` words (16 MiB). Beyond the cap the band is used.
6. Dispatcher: chooses band or bit-parallel per call from a cost model in quarter-cell units: a band
   cell costs 4, a 64-bit block costs 3, one class comparison in the generic scan costs 1, and an
   integer-id lookup costs 2. The generic class scan is capped at the band width. When the model picks
   bit-parallel, the band first runs for a row budget equal to a quarter of the bit-parallel work. If
   the band finishes, its answer is used. Otherwise the bit-parallel kernel runs. This bounds the
   loss on dissimilar pairs, where the band empties after a few rows.
   The constants were fitted to the measurements below. They are not portable.

## Correctness argument (informal)

- Band: the distance is at most `max(n, m)`, so clipping `k` there does not change the answer. A cell
  whose true value is at most `k` has an optimal path whose prefix costs are all at most `k`, so it is
  computed exactly under the cap. A row whose minimum is at least `k + 1` implies every later row
  exceeds `k`, because costs never decrease along a path.
- Bit-parallel: the recurrences are Myers' and Hyyro's. The score changes only by the horizontal delta
  of the bottom row. Bits above the pattern length never flow downward, so garbage above bit `m - 1`
  cannot change bits below it. The score falls by at most one per remaining text token, which gives the
  early exit.
- Dispatch: both kernels are exact, so the choice affects only time.

## Test coverage (tested, not proved)

`tests/levenshtein.rs`, every implementation checked against `levenshtein_full_dp` at every limit in the
range, and `levenshtein` checked against the oracle:

- exhaustive: all sequences up to length 6 over alphabet 3, and up to length 5 over alphabet 4, all
  limits `0..=max_len + 1`, all implementations (band, single-word, multiword, dispatcher, u32 path);
- randomised: lengths up to 3000 over alphabets 2, 4, 256 and sparse `u32` ids, probed at
  `d - 1, d, d + 1, 2d + 1, d / 2` and beyond the longest input, both orientations;
- short patterns (1 to 64 tokens) against texts up to 3000 tokens;
- multiword boundaries 63, 64, 65, 127, 128, 129, 191, 192, 193;
- empty and identical inputs; length-difference rejection; a long equal prefix and suffix hiding a small
  middle; the regression `[1]` vs `[2]` must be 1, not 2;
- the indel versus Levenshtein relabel case.

Mutation check (on the bit-parallel code before the later changes): removing the `|1` top-row carry
from the single-word kernel makes three tests fail (exhaustive alphabet 3, exhaustive alphabet 4,
multiword boundaries). The change was reverted. The band loop was also caught by a debug run during
the rewrite (an out-of-range `c - 1` on the first column), before that code was committed.

Final code, from the last commit: debug `levenshtein` test binary 11 passed, 0 failed (99 s).
Release 11 passed, 0 failed (about 7 s). Workspace `cargo test --locked --workspace` in debug: 60 passed,
0 failed across all test binaries. `cargo fmt --check` and `cargo clippy -D warnings` pass for the
workspace, and for the `ts` feature set.

## Measured crossover

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

## Real AST label sequences

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

## Limitations

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

## Relation to tree edit distance

For ordered trees, the Levenshtein distance between preorder (or postorder) label sequences is a lower
bound of the unit-cost tree edit distance. A tree mapping preserves ancestor and sibling order, so it
induces an alignment of the two sequences whose cost is at most the mapping's cost. The bench checks
this on real Rust ASTs for trees up to 1500 nodes, using `difffold::ted::ted`.

This module is not wired into `ted` or into any filter. Another agent on `feat/ted-filter` has a private
bounded Levenshtein that will be unified with this one later.

## Not yet compared against external libraries

Not yet compared against Edlib, RapidFuzz or WFA2. A separate agent will build and run them against this
kernel. This line is updated when that agent reports.

## Command line

`cargo run --release --example levenshtein_tokens -- a.txt b.txt [--limit K]` prints the exact distance,
or `exceeds K` when a limit is given and the distance is larger. Each file holds whitespace-separated
`u32` token ids. The exit status is nonzero on bad input.

## Benchmark

`cargo run --release --features ts --bin lev_bench -- synthetic [quick]` and
`cargo run --release --features ts --bin lev_bench -- app <dir>`. Run under `taskset -c 0`.
The `app` mode reads `NAME.a.rs` and `NAME.b.rs` pairs from `<dir>`.
