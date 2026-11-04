# difffold

Ordered-tree diff on an exact hash-consed arena, built on apeiron's `freq::Table`.
Research prototype for a from-scratch OmniDiff / Difftastic-class differ. See `SPEC.md`.

## What is different from an anchor-and-window differ

| earlier caveat | here |
|---|---|
| fold collisions (2^-64) | none: ids are confirmed against stored nodes, so id equality is structural equality (I1) |
| anchors are a heuristic, optimality lost | no anchors; an exact threshold DP prunes by `forward cost + reversed size accumulation`, and a result is accepted only when it fits under the threshold (C2) |
| scripts only probably valid | every script is replayed on the before-tree and must rebuild the after-tree and match the distance (C3) |

## Measured (one run, 4 vCPU cloud VM, `--release`)

All 997 Java, Go and C fixtures from OmniDiff's corpus (`results/fixtures-java-go-c.csv`).
OmniDiff's number is its recorded `diff_code` time on already-parsed trees (tree-sitter parse
excluded); difffold's is interning + diff, also excluding the tree-sitter parse.

| | OmniDiff | difffold |
|---|---|---|
| total | 16,735 ms | 1,239 ms (13.5x) |
| per-fixture median | 9.6 ms | 0.89 ms |
| p90 | 33.5 ms | 2.3 ms |
| p99 | 126.7 ms | 4.3 ms |
| worst | 302.8 ms | 47.7 ms |

Per-fixture speedup: min 1.4x, median 9.2x, max 215x. Including the tree-sitter parse in
difffold's time but not OmniDiff's, the total speedup is 4.1x. That last figure is not a symmetric
comparison; it is only a stress view. Numbers were re-measured after moving the interner onto apeiron's certified `map::table::Table`
(about 7% slower than the hashtrinity-port table it replaced) and after moving the DP into
`src/kernel.rs` for extraction (no measurable cost).

The objective is not OmniDiff's. This computes the top-down distance; OmniDiff matches across
levels and recovers moves. **Accuracy against the hand-authored ground truth is not scored here.**
Moves, wrap/unwrap and cross-level matches are not implemented.

The slowest difffold cases are wholesale rewrites (cost 2,000 to 2,900). The `widenings` counter is
a sum over every nested align, not the number of outer attempts: across the corpus it is 207,771
extra rounds over 377,949 distinct pair computations, about 0.55 extra rounds per pair. Doubling
beat 4x and 8x on an earlier run.

## Defect found by the constant-hash test

`Table::insert_with` calls its merge as `f(new, old)`. The first interner passed `|_old, new| new`,
which returns the old value, so when two different nodes shared a bucket the second became
unreachable and I1 failed. Real fold values almost never collide, so random tests passed. A test
that injects a constant bucket function (`Arena::with_fold`) exposed it; the interner now uses
`insert_merge_last_write`. `tests/boundaries.rs` keeps that test.

## Run

```sh
cargo test --release                     # contracts against the oracle
cargo build --release --features ts --bin bench_fixtures
./target/release/bench_fixtures <omnidiff>/src/test/data/diffs baseline.csv out.csv [limit] [reps]
```

`baseline.csv` is `benchmark_diff_pairs --fixtures --output baseline.csv` from OmniDiff.
`../drafts/omnidiff-apeiron/` holds the earlier profile and design notes.
