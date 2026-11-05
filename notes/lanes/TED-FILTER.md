# Exact threshold filter for tree edit distance (`src/tedfilter.rs`)

Status: **TESTED, not proved.** The filter is checked against an independent forest-recursion oracle on random
and degenerate pairs, and against the exact solver on a real corpus. Nothing here is a Lean theorem. The
extracted functions in `src/ted.rs` are unchanged, and nothing under `proof/` is touched.

## Question answered

`tedfilter::within(a, b, tau)` returns `Some(d)` with `d = TED(a, b)` when `d <= tau`, and `None` otherwise.
`within_stats` returns the same answer with per-stage counts and wall times.

## Method

Stages run cheapest first. A stage rejects a pair only when its lower bound exceeds `tau`. Only survivors reach
the exact solver.

1. Size bound: `|n - m|`.
2. Label multiset bound: `max(n, m) - |multiset intersection of labels|`.
3. Preorder label sequence: bounded Levenshtein (Ukkonen band, early exit when the row minimum exceeds `tau`),
   substitution, insert and delete all cost 1.
4. Postorder label sequence: the same, on postorder.
5. Exact: `ted::ted_within(a, b, min(tau, n + m))`, the existing threshold search of the exact solver.

Preorder order is computed from the public `lml` array alone: sort by `(lml ascending, postorder index
descending)`. `src/ted.rs` has a private `preorder` helper, but it was not edited or exported.

The Levenshtein stage is a plain loop-based DP in `src/tedfilter.rs`. It is not the Myers insert/delete-only
line engine, which charges 2 per relabel.

## Cost model and why each bound is valid

The exact solver (`ted.rs`, `relabel_cost`) charges 1 per insert or delete. A relabel costs:
0 if the labels are equal (whatever the kinds), 1 if the labels differ and the kinds agree, 2 if the kinds differ.

- **Size.** A mapping of `k` pairs deletes `n - k` and inserts `m - k` nodes, so its cost is at least `|n - m|`.
- **Labels.** Let `e` be the number of mapped pairs with equal labels. Each unequal pair costs at least 1, so
  the cost is at least `n + m - k - e`. Since `k <= min(n, m)` and `e <= overlap`, the cost is at least
  `max(n, m) - overlap`. Kinds are ignored, which only weakens the bound.
- **Traversals.** A valid tree edit mapping preserves the ancestor relation in both directions. It is therefore
  monotone in postorder and also in preorder (for two mapped pairs, either one is an ancestor of the other on
  both sides, or both are disjoint subtrees in the same left-right order). Its mapped pairs form a monotone
  alignment, with unmapped nodes as indels (cost 1 each). A mapped pair with equal labels costs 0 in both. A
  mapped pair with different labels costs 1 or 2 in the solver and 1 as a substitution. So the Levenshtein
  distance over labels is at most the mapping cost.

**Symbol choice (a bug found by the tests).** The first version used `(label, kind)` as the symbol. That is
wrong. The solver charges 0 for equal labels with different kinds, but a kind-aware symbol makes the
substitution cost 1, so the bound could exceed the true distance and wrongly reject a pair. The regression test
`cross_kind_relabel_costs_two_and_the_filter_respects_it` (same label, kinds 0 and 1, distance 0) catches this
form of the bug. The traversal symbol is the label alone.

**Trap (insert/delete-only distance).** `n + m - 2 LCS` overestimates a single relabel (1 in a tree, 2 under
indel). `relabel_is_not_charged_as_delete_plus_insert` pins the pair `node(1)` vs `node(2)`: the indel distance
is 2, the tree distance is 1, and `within(.., 1)` must return `Some(1)` without the preorder stage rejecting it.

## Correctness tests (`tests/ted_filter.rs`, 7 tests, all passing)

Oracle: a forest recursion written in the test file, sharing no code with the crate. It uses the same cost model,
including kinds. It is cross-checked against `ted()` on every random pair.

- `within_is_exact_on_random_pairs_at_every_threshold`: 8000 random pairs (random shapes, 1-4 labels, 1-3 kinds,
  random mutations of relabel, delete and wrap kinds, and some unrelated pairs). For every tau in `0..=d + 2`,
  `within` and `within_stats` both equal `(Some(d) if d <= tau else None)`. Zero tolerance.
- `every_stage_lower_bound_is_below_the_exact_distance`: 6000 pairs, each of the four lower bounds `<= TED`.
- `levenshtein_stage_matches_the_naive_table`: 20000 random sequence pairs; `levenshtein_within(x, y, k)` equals
  the naive full table for every `k`.
- `relabel_is_not_charged_as_delete_plus_insert`: the Myers trap above.
- `cross_kind_relabel_costs_two_and_the_filter_respects_it`: cost 2 across kinds, cost 0 for equal labels.
- `degenerate_shapes_are_exact`: single node, chain, star, left comb and right comb, sizes 1 to 7, all pairs.
- `empty_trees_and_huge_thresholds`: empty trees, and `tau = u32::MAX` (the clamp to `n + m` is exercised).

Also run and green: `cargo +1.89.0 test --locked --workspace`, `cargo +1.89.0 test --locked -p difffold --features ts`,
`cargo +1.89.0 clippy --locked --workspace --all-targets -- -D warnings` (default and `ts`), and
`cargo +1.89.0 fmt --all -- --check`.

## Benchmark (`examples/ted_filter_bench.rs`)

Command: `cargo run --release --example ted_filter_bench --features ts`.
CPU: Intel Xeon Processor @ 2.10 GHz (4 vCPUs in the container). The benchmark is single-threaded. Times are
medians of 5 timed runs after one warm-up run.

Methods, all asserted to return identical result sets (the run completed, so the assertions held):

- `A`: full exact `ted()` for every candidate, then compare with tau. Does not depend on tau.
- `B`: `ted_within()` for every candidate, the solver's own threshold search with no filter.
- `F`: `within_stats()`, the filter pipeline plus `ted_within()` on survivors.

### Synthetic workload (3 seeds, query of 140 nodes, 400 candidates per seed)

Candidates are 3/4 mutants of the query (0, 1, 2, 4, 8, 16 or 32 random edits) and 1/4 unrelated random trees.
Exact distances span 0 to about 200.

| seed | A (ms) | tau | within | B ted_within (ms) | F filter+verify (ms) | F/B | F/A |
|---|---|---|---|---|---|---|---|
| 0x51 | 120.3 | 1 | 89 | 15.7 | 9.8 | 0.62 | 0.08 |
| 0x51 | 120.3 | 4 | 163 | 104.3 | 75.2 | 0.72 | 0.62 |
| 0x51 | 120.3 | 8 | 201 | 417.0 | 322.5 | 0.77 | 2.68 |
| 0x51 | 120.3 | 32 | 294 | 3949.5 | 3536.3 | 0.90 | 29.4 |
| 0x77 | 108.5 | 1 | 87 | 11.2 | 7.5 | 0.67 | 0.07 |
| 0x77 | 108.5 | 4 | 159 | 97.5 | 66.9 | 0.69 | 0.62 |
| 0x77 | 108.5 | 8 | 199 | 324.9 | 250.2 | 0.77 | 2.31 |
| 0x77 | 108.5 | 32 | 296 | 3474.2 | 2671.4 | 0.77 | 24.6 |
| 0xa3 | 132.9 | 1 | 84 | 24.6 | 17.3 | 0.70 | 0.13 |
| 0xa3 | 132.9 | 4 | 166 | 122.1 | 86.4 | 0.71 | 0.65 |
| 0xa3 | 132.9 | 8 | 199 | 441.6 | 347.8 | 0.79 | 2.62 |
| 0xa3 | 132.9 | 32 | 292 | 3896.9 | 3005.0 | 0.77 | 22.6 |

Per-stage counts for seed 0x51 at tau 1 (400 candidates): size rejects 101; labels see 299 and reject 198;
preorder sees 101 and rejects 9; postorder sees 92 and rejects 0; exact verifies 92, rejects 3, accepts 89.
Stage median times: size 0.013 ms, labels 0.76 ms, prep (symbol sequences) 0.85 ms, preorder 0.16 ms,
postorder 0.14 ms, exact 7.7 ms. The filter costs about 1.9 ms of the 9.8 ms total.

Per-stage counts at tau 8 (seed 0x51): size rejects 5, labels see 395 and reject 155, preorder sees 240 and
rejects 26, postorder sees 214 and rejects 0, exact verifies 214 and rejects 13.

### Real workload (249 function subtrees of this crate's `src/` and `tests/`, 40 to 250 nodes)

Three queries (102, 148 and 226 nodes), each against the other 248 functions. Exact distances are 60 to 262, so
every pair is far apart.

| query | tau | within | B ted_within (ms) | F filter+verify (ms) | F/B |
|---|---|---|---|---|---|
| 102 nodes | 1 to 32 | 0 | 0.1 to 84 | 0.0 to 0.2 | 0.00 to 0.25 |
| 102 nodes | 64 | 1 | 229.9 | 4.6 | 0.02 |
| 148 nodes | 1 to 32 | 0 | 0.0 to 80 | 0.0 to 0.2 | 0.00 to 0.81 |
| 148 nodes | 64 | 0 | 377.8 | 0.7 | 0.00 |
| 226 nodes | 1 to 32 | 0 | 0.1 to 94 | 0.0 to 0.2 | 0.00 to 0.21 |
| 226 nodes | 64 | 0 | 306.6 | 0.3 | 0.00 |

At these tau values the size and label stages reject essentially all candidates. This is the easy regime: the
real pairs are unrelated functions, so no near-duplicate pair is measured.

## Where filtering does not help

- High tau on synthetic trees (tau of 8 or more on about 140-node trees): most candidates are within the threshold,
  so the exact solver verifies nearly all of them. The filter then saves at most about 10 to 25 percent of the
  time of `B`. Against the simplest baseline `A` (one full `ted()` call), `F` is slower: F/A is 2.3 to 29.
- `B` itself is slower than `A` at tau of 8 or more. `ted_within` does not switch to the full band when
  `3 tau >= max(n, m)` the way `ted_oriented` does, and it does not mirror. This is an observation about the
  existing solver, which was not changed. At high tau, calling `ted()` once is the faster choice.
- The postorder stage rejected nothing in any run here. The preorder stage catches what it would have. It is
  kept because it is cheap and sound, and it may matter on other corpora. This is not a claim of usefulness.

## Limitations

- Tested, not proved. The traversal bounds rest on the monotone-alignment argument above, and the tests cover it
  on random and degenerate trees with the solver's exact cost model. No Lean proof was attempted.
- The threshold `tau` is clamped to `n + m` before the exact stage, because `ted_within` allocates a band of width
  `2 tau + 1`. A huge tau costs nothing extra in the filter, but the exact stage is still a full solve.
- `prep` (building the label sequences) is paid for every pair that survives stage 2. A cache keyed by tree would
  remove it for repeated queries. Not done.
- The label bound is a re-implementation of the private `label_lower_bound` in `ted.rs`, because that function
  cannot be exported without editing the extracted code. It computes the same quantity.
- The real corpus is small (249 subtrees from this crate), contains no near-duplicate pairs, and has no
  workload with many within-threshold real pairs. Real similarity-search gains at small tau on near-duplicate code
  are not measured here.
- Wall times depend on the machine. Ratios are more stable than absolute times, but the numbers come from one
  container.
