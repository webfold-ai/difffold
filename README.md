# difffold

Line and ordered-tree differencing in Rust, with optimal tree mappings and Git-compatible unified patches.

**Research build. The API is unstable and the crate is not published to crates.io.** (`version = "0.0.1"`,
`publish = false` in `Cargo.toml`.) Interfaces, formats and results may change without notice.

[![CI](https://github.com/webfold-ai/difffold/actions/workflows/ci.yml/badge.svg)](https://github.com/webfold-ai/difffold/actions/workflows/ci.yml)
[![CodeQL](https://github.com/webfold-ai/difffold/actions/workflows/codeql.yml/badge.svg)](https://github.com/webfold-ai/difffold/actions/workflows/codeql.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

The library has three engines that solve different problems (see [Choose an engine](#choose-an-engine)):

- **`lines`**: exact minimal line diff (Myers objective), with a unified-patch writer (`unified`) that
  `git apply` accepts.
- **`diff`**: restricted, top-down ordered-tree edit distance on an exact hash-consed arena. A result is
  accepted only when an admissible bound certifies it, and every edit script is replayed on the
  before-tree (SPEC contracts C2 and C3).
- **`ted`**: general ordered-tree edit distance (the Zhang-Shasha objective, where deleting a node
  promotes its children), with an optimal node mapping, an independent mapping validator and an
  executable replay of the implied edit script.

On top of `diff`, `refine` (in the library, no parser needed) repairs the top-down mapping across levels:
moves, reorders, wraps and unwraps. Its output is a heuristic mapping, not an optimum of any objective.

Read [SPEC.md](SPEC.md) for the contracts of `diff`, [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for how the
modules fit together, and [paper/paper.md](paper/paper.md) for the algorithm, the evaluation and its limits
(draft 1.0). The earlier draft is archived in `notes/archive/` and is superseded.

## Choose an engine

| Need | Engine (module) | Entry points | Objective it solves |
|---|---|---|---|
| Line diff of two byte strings | `lines` | `lines::diff_text`, `diff_text_with(.., Algo::Minimal)` | Minimal line edit script: fewest deleted plus inserted lines (the `git diff --minimal` / Myers 1986 objective). `Algo::Histogram` returns a valid script that is **not** minimal. |
| Top-down tree diff with an edit script | `diff` | `diff`, `diff_checked`, `diff_with(.., Config)`, `mapping::correspondence` | Top-down (Selkow) ordered-tree distance: a node can be matched only if its parent is, deleting or inserting a subtree costs its size, relabel costs 1, roots always pair. No promotion, moves or wrap/unwrap. Unit costs only. |
| General tree edit distance and mapping | `ted` | `PostTree::from_arena` / `from_kids`, `ted`, `ted_mapping`, `check_mapping`, `replay_script` | General ordered-tree edit distance (Zhang-Shasha objective): deleting a node promotes its children, so matches can cross levels. Unit costs by default; `PostTree::with_kinds` changes relabel cost (see [Cost models](#cost-models)). No move operation. |
| Unified patch / Git helpers | `unified`, binary `dfdiff`; crate `gitcompat` | `unified::unified`, `dfdiff -U3 OLD NEW`, `GIT_EXTERNAL_DIFF` helper, `difffold-patch` | No objective of its own. `unified` formats the script of `lines` (Minimal or Histogram). `gitcompat` has its own Myers line diff with a work budget (`DEFAULT_BUDGET`); when the budget runs out the rest is emitted as delete-all plus insert-all, so that path is valid but not guaranteed minimal. The contract is that `git apply` rebuilds the after-bytes. |

Also in the crate: `merge` (three-way line merge with diff3 semantics on the `lines` engine) and `frontier`
(experimental aligners for the `diff` objective, not used by the production differ).

**The tree engines solve different objectives and must not be read interchangeably.** A distance, script or
mapping from `diff` is not comparable with one from `ted`. With default unit costs the general optimum is
never larger than the top-down optimum (stated in `harness/rust/src/lib.rs`), and the two mappings can differ
node for node. Every cross-tool number below is labelled with the objective it measures.

### Cost models

- `diff` (top-down): unit cost per node only. Custom cost models are not supported, and the pruning bounds
  are untested under them (SPEC, "Threshold boundary contract").
- `ted`, default: unit insert, delete and relabel. `PostTree::from_kids` and `from_arena` set every node's
  kind to 0, so every relabel costs 1.
- `ted` with `PostTree::with_kinds(kind)`: one kind per node, in postorder. Relabelling within a kind costs 1
  and **relabelling across kinds costs 2**, the same as deleting one node and inserting the other. Equal
  labels cost 0. This is the only cost variation `ted` offers; insert and delete stay at 1. It is checked by
  `kind_aware_cost_matches_the_oracle_and_maps_legally` in `tests/ted.rs` against a brute-force oracle with
  the same cost rule, which also asserts that no mapped pair crosses kinds. `score_accuracy` turns it on
  when the environment variable `DFOLD_KINDS` is set.

## Limitations

Read these before using the numbers below.

- **The objectives are not OmniDiff's.** `diff` computes top-down distance: it does not match across levels,
  detect moves, or recover wrap/unwrap. `refine` repairs its mapping heuristically (no objective, no certificate beyond a bijection that respects kinds). `ted` can match across levels by promotion (so it can express
  wrap/unwrap) but has no move operation, so a moved or reordered subtree is a delete plus an insert.
- **Accuracy has been scored against two ground truths, on overlapping inputs:** OmniDiff's hand-authored mappings
  (998 fixtures; `diff`, `diff` + `refine`, OmniDiff, and GumTree 4.0.0-beta4 on the Java subset) and DiffBenchmark's
  Defects4J oracle (`diff`, `diff` + `refine`, RefactoringMiner, GumTree 3.0; see
  [OmniDiff: cost and accuracy](#omnidiff-cost-and-accuracy)). Both oracles favour the tool they were derived from. `ted`
  was scored only in an earlier mixed run on the previous corpus (`results/accuracy/previous-fork-run/`). Accuracy against
  difftastic, diffsitter or imara-diff has **not** been measured.
- **Correctness evidence is of different kinds** and the kinds are not interchangeable: tests, oracle
  comparisons, Lean proofs about a model, and Lean proofs about Aeneas-extracted Rust. See the
  [evidence table](#evidence). No proof covers the `ted` solver as a whole, and none covers `diff` end to
  end.
- **Benchmark numbers are historical or preliminary** unless a machine and toolchain record sits next to
  them. See [Provenance of the recorded results](#provenance-of-the-recorded-results).
- **Languages.** The tree engines are measured on the eight languages with tree-sitter parsers wired in
  (`ts` feature): C, Go, Java, JavaScript, Python, Rust, TSX and TypeScript. The library itself has no parser
  dependency.
- **Speed numbers depend on machine load.** The newest timing run (tag `t4`) was taken on a shared VM with a load
  average of 20 to 85; per-fixture minima and medians of ten passes are reported, not an idle-machine figure.
  Older files are single runs; the repeated `ted-*` files below show how much the same cohort moves between runs.

## Evidence

What backs each claim, by kind. "Not re-run" means the artefact is in the repository but was not executed
when this table was written; check the command before relying on it.

| Claim | Evidence type | Scope | Reproduce |
|---|---|---|---|
| Node identity is exact: equal ids iff equal subtrees (I1), for any bucket function | Tests (property test against a plain-struct model; forced constant-bucket collisions) | `intern::Arena`. Not proved: `proof/README.md` lists `mk_exact` as not done | `cargo test --locked -p difffold --test contracts` |
| `diff` distance equals a naive full DP, in every `Config` (C4); symmetry, identity, size bound, triangle inequality (C5 to C8) | Oracle comparison (independent recursion in `tests/contracts.rs` and `tests/boundaries.rs`) | Random and exhaustive small trees; sizes are listed in SPEC.md | `cargo test --locked -p difffold` |
| `diff` scripts replay to the after-tree and cost the distance (C3) | Runtime assertion in `diff_checked`, plus tests | Every pair the tests and `bench_fixtures` run | `cargo test --locked -p difffold --test contracts` |
| Threshold pruning is sound and the widening loop returns the true minimum | Lean model proof (`proof/Difffold/`: `prune_sound`, `decision`, `search_min`, `widen_correct_lists`, `strip_safe`, ...) | A Lean model of the **top-down** objective, **not** the Rust code. Lean 4.31.0, no `sorry`, standard axioms only (`proof/AXIOMS.txt`). No CI | `proof/build.sh` (needs Lean; see `proof/README.md`) |
| The threshold DP kernel computes what the model says | Extracted-Rust proof (Aeneas translation of `src/kernel.rs`: `fill_spec`, `fill_correct`, ...) | `kernel::fill` under the hypotheses listed in `proof/README.md`. It does not cover that the grid is a child-list alignment of `diff.rs`, nor that the oracle's pair cost is the recursive distance. Status taken from `proof/README.md`, not re-run | `proof/extract.sh`, then `proof/check-kernel.sh` (needs Charon, Aeneas, Mathlib) |
| `ted` returns the exact general distance, also with `ted_within` at `tau` of d-1, d, d+1 | Oracle comparison (forest recursion; 6,000 random small tree pairs in `tests/ted.rs`) | Random small trees (node budget 1 to 9 per tree), 1 to 3 labels | `cargo test --locked -p difffold --test ted` |
| `ted` kind-aware cost (relabel across kinds = 2) | Oracle comparison (`fd_kind`, 4,000 random pairs) | Small trees, 5 labels | same |
| `ted_mapping` is a legal mapping whose cost is the distance; `replay_script` rebuilds the after-tree | Tests (4,000 random pairs against the oracle) and `tedbench` assertions on real ASTs (237 pairs in the `ted-map-*` files) | Replay places inserts using the structure of the after-tree, so it shows the mapping is executable, not that the script was derived independently (`ted.rs` doc) | `cargo test --locked -p difffold --test ted`; `tedbench` needs the OmniDiff corpus |
| `ted` distance equals the `apted` crate's on real tree-sitter ASTs | Oracle comparison inside `tedbench` (assertion per pair; the CSV stores only `dist`) | 97 + 100 + 40 pairs in `ted-map-a/b/c.csv`; Java, Go, C | `cargo run --release --locked -p linebench --bin tedbench -- DIFFS OUT.csv MAXNODES` |
| Lean helper lemmas for `ted` | Extracted-Rust proof, **partial**: `proof/Ted/` (`from_kids_spec`, `label_lower_bound_spec`, band-cell lemmas) are about a closure-free **copy** `proof/extract/ted_core.rs`, tied to `src/ted.rs` by agreement tests only | No theorem about the optimality of `ted`. `proof/README.md` still says "No TED theorem exists", which predates `proof/Ted/`; not re-run here | `cargo test --locked -p difffold --test ted_core`; `proof/check-ted.sh` |
| `lines` returns a minimal script and replays | Oracle comparison (LCS DP in `tests/lines.rs`, `tests/adversarial.rs`); seeded fuzz | Random and adversarial inputs | `cargo test --locked -p difffold --test lines --test adversarial` |
| Line search and helpers | Lean model proof of a model of `solve` (`proof/Myers*/`); extracted-Rust specs of `common_prefix`, `common_suffix`, SWAR newline helpers (`proof/Lines/`); `first_nl`/`last_nl` and Myers helpers are closure-free copies checked by tests only (`tests/agree.rs`, `tests/myers_core.rs`) | See `proof/README.md` (the Myers rows there are less detailed than the tree on disk) | `proof/check-lines.sh`, `proof/check-myers.sh` |
| `unified` patches apply with real `git apply`, forward and reverse | Tests with `git` (`tests/roundtrip.rs`, `gitcompat/tests/edge.rs`) | Edge cases: no final newline, CRLF, special filenames, create/delete headers | `cargo test --locked --workspace` (needs `git` on PATH) |
| Contracts hold on arbitrary small inputs | Fuzz targets `fuzz_tree`, `fuzz_lines`, run seeded under `cargo test` and under libFuzzer in `fuzz.yml` | Trees of at most 96 nodes and depth 4 | `cargo test --locked --manifest-path fuzz/Cargo.toml` |
| Speed relative to other tools | Benchmarks, single runs | See [Testing against other tools](#testing-against-other-tools); historical/preliminary where marked | per section |
| Correspondence accuracy | Scoring against OmniDiff's hand-authored mappings | 998 scorable fixtures of the public OmniDiff corpus; engine and configuration are named in each table | `score_accuracy` (needs the OmniDiff corpus) |

## Testing against other tools

difffold is compared against several baselines. They solve different problems, so the comparisons below
separate **what was measured** from **what was not**. Every number cites the file it came from. Where a
figure is a median computed from a CSV, the computation is described; the CSVs are the source.

**Status of these numbers.** Each section says whether the machine, toolchain and baseline versions were
recorded. Results without that record are **historical/preliminary**: they show what a run produced, not what
a reader can expect to reproduce. The per-file table is in
[Provenance of the recorded results](#provenance-of-the-recorded-results).

| Baseline | Problem it solves | What is measured here | Source | Not measured |
|---|---|---|---|---|
| similar (Myers) | line diff | time and edit cost, 2,302 fixtures | `results/lines/lines-xdiff.csv` | accuracy against a line-diff ground truth |
| imara-diff (Myers, Histogram, Myers-minimal) | line diff | time and edit cost, same fixtures | `results/lines/lines-xdiff.csv` | |
| git xdiff (libgit2, default and minimal) | line diff | time and edit cost, same fixtures | `results/lines/lines-xdiff.csv` | |
| fast_rsync and qbsdiff | delta encoding | time, delta size, round-trip check | `results/lines/sync.csv` | compression ratio against a reference encoder |
| git merge-file and mergiraf | 3-way merge | outcome labels, 800 cases per tool | `results/lines/merge.csv` | merge quality on real conflicts |
| difftastic 0.72.0 | syntax-graph diff | wall time, 80 fixtures | `harness/results/cli-t1.csv` | accuracy; its own syntax-tree objective |
| GumTree 4.0.0-beta4 | heuristic tree matching | wall time, 80 fixtures | `harness/results/cli-t1.csv` | accuracy in the harness (indicative accuracy elsewhere, see above) |
| diffsitter | AST node diff | wall time, 80 fixtures | `harness/results/cli-t3.csv` | accuracy |
| APTED (`apted` crate 0.1.1) | general tree edit distance | time against `ted` on 40 to 150 pairs per file; distance equality asserted by `tedbench` | `results/lines/ted-*.csv` | accuracy; **not** an objective match for `diff` |
| OmniDiff | structural diff with its own ground truth | cost and accuracy, 997 to 1001 fixtures | `results/fixtures-java-go-c.csv`, `results/accuracy/` | |

### Line diff: similar, imara-diff, git xdiff

`results/lines/lines-xdiff.csv` runs every line algorithm on the same 2,302 before/after fixture pairs. Each
timed call includes that library's own input preparation, as `linebench` times it. "Same cost as similar"
counts fixtures where the reported edit cost equals similar's Myers cost on that fixture. It is an agreement
check between tools, not a correctness score: the algorithms optimise different costs in some cases.

| algorithm | median µs per diff | total ms | same cost as similar-myers |
|---|---:|---:|---:|
| difffold-lines | 13.09 | 112.6 | 100.0% |
| difffold-histogram | 13.34 | 164.9 | 98.3% |
| similar-myers | 13.60 | 131.7 | 100.0% |
| imara-histogram | 19.74 | 150.9 | 98.1% |
| imara-myers-minimal | 21.22 | 157.1 | 98.1% |
| imara-myers | 22.89 | 161.7 | 98.1% |
| xdiff-minimal (libgit2) | 89.16 | 635.2 | 99.6% |
| xdiff-default (libgit2) | 93.16 | 642.4 | 99.6% |

**Historical/preliminary.** One run. The machine, toolchain and baseline versions for this file are not
recorded in `results/` (the library versions in use today are in `Cargo.lock`: similar 2.7.0, imara-diff
0.1.8, but the CSV does not say which versions produced it). The imara-diff README compares its Histogram and
Myers algorithms only against `similar`, on git tag-to-tag diffs of Linux, Rust, VSCode and Helix, and
reports its Histogram speedup as self-measured. This repository does not reproduce that benchmark, so no
speedup claim against imara-diff is made here beyond the table above.

Patch-stage timings (`patch-difffold`, `patch-similar-myers`, `patch-imara-myers`) are in the same file and
are not summarised here. In that file `patch-imara-myers` has the lowest median of the three.

### Tree diff: difftastic, GumTree, diffsitter (top-down `diff` engine)

The harness runs each tool as a command-line process on 80 fixtures and records wall time
(`harness/results/cli-t1.csv`, `cli-t3.csv`). The difffold rows run `dfold-cli --algo difffold` and
`--algo difffold-distance` (`harness/rust/src/bin/dfold-cli.rs`), which use the **top-down `diff` engine**,
not `ted`. The medians below are computed over the 80 per-fixture medians in `cli-t1.csv`, so they include
process start-up for every tool. `harness/results/SUMMARY.md` uses a different aggregation (for example 9.5 ms
for difffold where this table gives 10.49 ms), so the two should not be mixed.

| tool | median wall ms | p90 wall ms | cost equals `selkow-ref` |
|---|---:|---:|---|
| git-histogram | 3.39 | 4.04 | n/a (line diff) |
| git-myers | 3.40 | 4.12 | n/a |
| git-minimal | 3.47 | 4.29 | n/a |
| git-patience | 3.53 | 4.13 | n/a |
| difffold (distance and diff) | 10.49 | 23.91 | 80 of 80 |
| difffold-distance | 10.73 | 24.41 | 80 of 80 |
| difftastic 0.72.0 | 46.14 | 155.72 | n/a (different objective) |
| selkow-ref (plain top-down DP, reference) | 319.20 | 2365.57 | reference |
| GumTree 4.0.0-beta4 (`gumtree-simple`) | 1012.68 | 1184.41 | n/a (different objective) |

The cost column is read from the `cost=` field of `stdout_line` in `cli-t1.csv`; it is recorded only for the
three in-process tools. `diffsitter` was run on the same fixtures in `cli-t3.csv`; its aggregate is in
`SUMMARY.md`. `p90` is the value at index `floor(0.9 * (n - 1))` of the sorted 80 medians.

What these numbers do and do not show:

- **Objectives differ.** difftastic computes a shortest path through a syntax graph (with Dijkstra's
  algorithm, per its README). GumTree uses heuristic matching. difffold's `diff` computes exact top-down edit
  distance. Speed is not a quality comparison.
- **Machine and toolchain are recorded** in `harness/results/machine.txt` (see
  [Measurement setup](#measurement-setup)), so this section is not marked preliminary on that ground. It is
  still a single recording, and `difffold_src_head: ed61c79` in that file is not a commit in this repository's
  history, so the exact source is not recoverable from here.
- **difftastic was run with limits.** `harness/results/tools-t1.tsv` gives `--byte-limit 1000000
  --graph-limit 3000000` and `DFT_UNSTABLE=yes`. Results on larger inputs may change with those limits.
- **Accuracy against difftastic and GumTree is not measured in the harness.** There is no ground truth for
  these fixtures in the harness.

### Tree edit distance: `ted` against APTED (general objective)

**What is compared.** Both sides compute the same objective: unit-cost ordered-tree edit distance where
deleting a node promotes its children. The difffold side is `difffold::ted` (`ted_stats`, the production path:
doubling threshold `tau` starting from `max(|n - m|, label multiset lower bound, 1)`, banded forest-distance
arrays of width `2 tau + 1`, keyroot-pair windows skipped by a position filter, and the
cheaper of the left-path and mirrored right-path orientation chosen from keyroot sizes). The other side is the
Rust `apted` crate 0.1.1 (`APTED::new(StringUnitCostModel)`, in `Cargo.lock`) on the same trees, passed as
bracket strings. Trees are tree-sitter parses with every node, leaf label = (kind, text), inner label = kind.

**Producer.** `tedbench` (`linebench/src/tedbench.rs`). For each pair it times `ted_stats` and APTED (median of
`reps` runs, default 3), times `ted_unpruned` once when both trees have at most 3,000 nodes (`NaN` otherwise),
then runs `ted_mapping`, validates it with `check_mapping` and `replay_script`, and **asserts** before writing
the row that: `ted_unpruned` equals `ted_stats` (when run), the mapping's implied script cost equals the
distance, the replayed operation count equals the distance, and the distance equals APTED's. Any failure
panics, so a written row is an agreed pair. The CSV stores only difffold's `dist`, not APTED's. The binary's
stderr summary ("N pairs, all distances equal to APTED") was not saved.

**Which files that covers.** Only files whose header equals the 17-column header written by the committed
`tedbench` can be tied to it. The others have an unknown or older producer:

| file | columns | pairs | max nodes per side | difffold median ms | APTED median ms | unpruned median ms (pairs timed) | distance agreement with APTED | producer |
|---|---:|---:|---:|---:|---:|---:|---|---|
| `ted-map-a.csv` | 17 | 97 | 384 | 0.484 | 3.398 | 5.806 (97) | 97 of 97 asserted by `tedbench` | committed `tedbench` header |
| `ted-replay-a.csv` | 17 | 97 | 384 | 0.359 | 3.971 | 6.609 (97) | 97 of 97 asserted | committed `tedbench` header |
| `ted-map-b.csv` | 17 | 100 | 1,472 | 18.180 | 217.551 | 507.091 (100) | 100 of 100 asserted | committed `tedbench` header |
| `ted-replay-b.csv` | 17 | 100 | 1,472 | 16.280 | 205.223 | 507.793 (100) | 100 of 100 asserted | committed `tedbench` header |
| `ted-lb-b.csv` | 17 | 100 | 1,472 | 16.995 | 201.626 | 484.897 (100) | 100 of 100 asserted | committed `tedbench` header |
| `ted-map-c.csv` | 17 | 40 | 5,958 | 80.939 | 2,738.322 | 2,395.176 (17) | 40 of 40 asserted | committed `tedbench` header |
| `ted-replay-c.csv` | 17 | 40 | 5,958 | 78.326 | 2,415.929 | 2,099.841 (17) | 40 of 40 asserted | committed `tedbench` header |
| `ted-stats-a.csv` | 15 | 97 | 384 | 0.382 | 3.453 | 5.581 (97) | not recorded | header is the first 15 columns of the 17; a `tedbench` version not in the repo |
| `ted-j-a.csv` | 15 | 97 | 384 | 0.367 | 3.139 | 4.923 (97) | not recorded | same |
| `ted-stats-b.csv` | 15 | 100 | 1,472 | 17.262 | 216.659 | 467.454 (100) | not recorded | same |
| `ted-j-b.csv` | 15 | 100 | 1,472 | 15.284 | 207.383 | 483.090 (100) | not recorded | same |
| `ted-stats-c.csv` | 15 | 40 | 5,958 | 84.223 | 2,507.606 | 2,358.223 (17) | not recorded | same |
| `ted-j-c.csv` | 15 | 40 | 5,958 | 74.749 | 2,749.336 | 2,195.778 (17) | not recorded | same |
| `ted-small.csv` | 6 | 97 | 384 | 0.467 | 3.779 | none | not recorded | **unknown**: no program in the repo writes this header |
| `ted-mid.csv` | 6 | 150 | 1,489 | 18.794 | 192.652 | none | not recorded | unknown |
| `ted-mid2.csv` | 6 | 150 | 1,489 | 14.528 | 187.003 | none | not recorded | unknown |
| `ted-large.csv` | 6 | 40 | 5,958 | 72.253 | 2,512.636 | none | not recorded | unknown |
| `ted-java-a/b/c.csv` | 3, no header | 97 / 100 / 40 | | | | | | **unknown**: nothing in the repo names the tool |

Notes on the table:

- Times are the medians over pairs of each pair's median wall time, in milliseconds, in-process, with no
  machine, CPU, rustc version or build profile recorded next to these files. **All timing columns are
  historical/preliminary.**
- The a, b and c groups are the same cohorts measured repeatedly. The spread between files within a group
  (for example difffold 15.3 to 18.2 ms and APTED 201.6 to 217.6 ms across the seven group-b files) is the
  only variance information available; it is run to run on unknown conditions, not a confidence interval.
- The distance values in the 15-column and 6-column files equal the `dist` of the 17-column files on every
  pair the files share (97 of 97 for `ted-small`, `ted-j-a`, `ted-stats-a`, 100 of 100 for `ted-j-b`, `ted-stats-b`, and for `ted-mid` and `ted-mid2`
  against `ted-map-b`, which covers 100 of their 150 pairs, 40 of 40 for `ted-large`, `ted-j-c`, `ted-stats-c`). That is a consistency
  check on the recorded `dist` column, not evidence of how those files were produced; the 50 additional pairs
  in `ted-mid` and `ted-mid2` have no second record.
- The second column of `ted-java-a/b/c.csv` equals `dist` of `ted-map-a/b/c.csv` row for row (97 of 97, 100 of
  100 and 40 of 40 rows), and `notes/lanes/RESULTS.md` (Lane 2b) reports a run against the authors' Java APTED (commit
  193666b). No file ties the headerless CSVs to that run, so they are not used for any claim here.
- `notes/lanes/RESULTS.md` Lane 2b gives total and median speedup ratios for these cohorts. Those figures are
  narrative, not recomputed from a recorded machine, and are not repeated here.
- Earlier versions of this README presented `ted-small`, `ted-mid`, `ted-mid2` and `ted-large` as the
  **top-down** difffold against APTED. That is not supported by the repository: the pairs these files share
  with `tedbench` output have the general-TED distance, and the committed `tedbench` times `difffold::ted`.

**What is not covered.** No result file in the repository times the top-down `diff` engine against APTED. The
nearest records are: (1) OmniDiff, whose tool label in `harness/run_all.sh` is "heuristic matching + APTED on
residual", against the `diff` engine in `results/fixtures-java-go-c.csv` (a comparison with OmniDiff, not with
APTED); and (2) harness rows `zhang-shasha` (`dfold-cli --algo zs`) and `apted-omnidiff` (an external worker
using OmniDiff's rename-cost model), which `harness/run_all.sh` can run but which appear in none of the
recorded `cli-t*.csv` files.

**Reading the ratios.** The `ted` and APTED columns are two implementations of one objective, so the ratio is
an implementation comparison on these inputs. It says nothing about how `diff` (a different, restricted
objective) compares with APTED. Whether `ted` stays faster on inputs with a large normalised distance is not
established by these files (`notes/lanes/RESULTS.md` reports the speedup falling with normalised distance, but
that analysis is not recorded as a file).

### Delta sync and 3-way merge

`results/lines/sync.csv` has 800 fixture rows per tool. Every row is marked `verified = true`. Median times:
difffold line delta 88 µs, fast_rsync (block size 512) 40 µs, qbsdiff 1,508 µs. The file also records delta
and deflated sizes, which are not summarised here.

`results/lines/merge.csv` has 800 cases per tool, labelled with an outcome by the harness:

| tool | correct | conflict flagged | false conflict | silently wrong |
|---|---:|---:|---:|---:|
| difffold-merge3 | 392 | 400 | 7 | 1 |
| git merge-file | 392 | 400 | 6 | 2 |
| mergiraf | 379 | 400 | 4 | 17 |

The labels are those written by the harness. "Silently wrong" means not byte-equal to the after file;
mergiraf is syntax-aware and may produce equivalent but different text (`notes/lanes/RESULTS.md`, Lane 3).
This is a small, labelled set, and it does not establish merge quality on real conflicts. Machine and
toolchain are not recorded for either file: **historical/preliminary**.

### OmniDiff: cost and accuracy

OmniDiff is one baseline among these. It is the only one for which this repository holds hand-authored
ground truth, so it is the main one scored for accuracy.

**Speed (run `t4`, current).** 350 Java, Go and C fixtures from the OmniDiff corpus (the 50 largest inputs plus
300 drawn at random, seed 1), `harness/results/*-t4.*`; 120 of them timed fixture by fixture against OmniDiff in
`harness/results/paired-t4/`. Machine, toolchain and revisions: `harness/results/machine-t4.txt`. **The
machine was heavily loaded by other jobs (one-minute load average 20 to 70 on 4 vCPUs) and every timed process ran at
`nice` 10**, so absolute times are several times those of an idle machine; see the paper, section 7.

| view (OmniDiff over difffold, paired, 120 fixtures, 10 passes each) | OmniDiff total | difffold total | total ratio | median per-fixture ratio |
|---|---:|---:|---:|---:|
| **with the tree-sitter parse counted for both** (OmniDiff: parse + AST metadata + diff) | 29,045 ms | 5,345 ms | **5.4** | 8.8 |
| own work, parse removed on both sides | 24,859 ms | 1,225 ms | 20.3 | 67.7 |
| matching only (difffold: certified top-down diff with replay + refinement) | 17,405 ms | 119 ms | 146 | 347 |

- **Headline: about 5 times less total time with the parse counted (5.4 on medians of ten passes, 6.4 on minima, 3.6 in the
  unpaired 350-fixture run).** It is not an order of magnitude: parsing and arena building are 98% of difffold's own
  end-to-end time, and the matching and refinement are about 2%. Quote matching-only figures only as matching-only.
- The refinement costs 20 times the (tiny) top-down core's time on these fixtures (119 ms against 6 ms in total) and adds 3.6% to the cold
  wall time of the command (20.4 s against 19.7 s for 350 fixtures). Its cost is close to linear in tree size (log-log slope 0.88 to 0.91 from 9 to
  100,456 nodes).
- OmniDiff was timed in process through its library (not its command line), and the tree-sitter parse counts as OmniDiff's too. The "parse only"
  variant (without the AST metadata that `diff_code` needs) gives 4.0.
- Files: `harness/results/paired-t4/SUMMARY.md`, `unpaired-t4/SUMMARY.md`, `SUMMARY-t4.md`, `NOTES-t4.md` (protocol deviations), `machine-t4.txt`.

*Historical (previous corpus snapshot and machine, kept for the record).*

**Cost (top-down `diff` engine, earlier single run).** 997 Java, Go and C fixtures, `results/fixtures-java-go-c.csv`, the archived draft
(`notes/archive/paper-draft-0.2.md`, section 8.1). One run on a "4 vCPU cloud VM, release build" (paper wording). The CPU model, rustc version,
OmniDiff commit and OmniDiff build profile are **not recorded** with this file, so the figures are
**historical/preliminary**. OmniDiff's figure is its recorded `diff_code` time on already-parsed trees.
difffold's is interning plus `diff`. **Both exclude the tree-sitter parse.** The objectives differ, so this
compares cost, not quality.

| | OmniDiff | difffold (`diff`) |
|---|---:|---:|
| total | 16,735 ms | 1,239 ms |
| median | 9.6 ms | 0.89 ms |
| p90 | 33.5 ms | 2.3 ms |
| p99 | 126.7 ms | 4.3 ms |
| worst | 302.8 ms | 47.7 ms |

Per-fixture ratio: minimum 1.4, median 9.2, maximum 215 (archived draft, section 8.1). If difffold's time includes the
tree-sitter parse and OmniDiff's does not, the paper's total ratio drops to 4.1. That comparison is not
symmetric.

**Accuracy** (998 scorable fixtures in the eight supported languages of the public OmniDiff corpus at commit
`ee5ee5b`; 763 of 1,761 are unscorable, 758 because difffold has no parser for their language). Scorer:
`src/bin/score_accuracy/`. Outputs: `results/accuracy/` (refined run and OmniDiff), `results/accuracy/topdown/`,
`results/accuracy/ablation/`, `results/accuracy/split-dev/`, `results/accuracy/split-test/`,
`results/accuracy/ci.md` (bootstrap), `results/accuracy/sweeps/dev-sweep.tsv`. The OmniDiff column is
OmniDiff's own mapping (dumped by `tools/omni_dump`) scored by the same scorer. The earlier run on a private
OmniDiff fork (1,001 fixtures) is kept in `results/accuracy/previous-fork-run/` and is not mixed with these.

Micro averages over the 998 fixtures. The difffold columns are the top-down engine alone and the top-down engine
followed by the cross-level refinement (`refine`, `Options::FULL`; `DFOLD_REFINE=full`):

| metric (micro) | difffold `diff` (top-down) | difffold `diff` + `refine` | OmniDiff |
|---|---:|---:|---:|
| pair F1 | 0.998 | 1.000 | 1.000 |
| node-correspondence accuracy | 0.996 | 0.999 | 0.999 |
| changed-span precision / recall | 0.741 / 0.980 | 0.974 / 0.956 | 0.962 / 0.984 |
| **changed-span F1** | **0.844** | **0.965** | **0.973** |
| fixtures with zero visible mismatches | 56.8% | 75.3% | 82.1% |

- Bootstrap over fixtures (`results/accuracy/ci.md`): refined changed-span F1 minus OmniDiff's is -0.008
  with an interval that includes zero; the perfect-fixture difference (-6.8 points) does not.
- Decision accuracy in the classes a top-down matcher cannot decide: reorder 0.034 to 0.832 (OmniDiff 0.905),
  cross-parent move 0.186 to 0.860 (OmniDiff 0.809), wrap/unwrap 0.401 to 0.902 (OmniDiff 0.947). These
  are accuracies over the graded decisions attributed to each class, not move-operation recall.
- Partial hold-out: `anchor_below`, `hops` and the descend and retarget phases were chosen on one half
  (`DFOLD_SPLIT=dev`) and frozen; the other half gives changed-span F1 0.966 on dev, 0.964 on test (OmniDiff 0.974
  and 0.972). `dice`, `keep` and `min_exact` were inherited from earlier unrecorded runs over all fixtures.
- Ablation (`results/accuracy/ablation/`): the exact-subtree phase gives almost all of the gain
  (0.844 to 0.958); the validate and container phases change no aggregate on this corpus.
- The refined mapping is a heuristic repair, not an optimum of any objective, and is not a top-down mapping.
  Only the top-down core is certified (C2, C3).
- The scorer favours OmniDiff: the ground truth is OmniDiff's own, and OmniDiff was developed against this
  corpus. Treat OmniDiff's numbers as the upper end. Details and threats: `paper/paper.md`, sections 6 and 7.
- The `ted` engine's earlier accuracy (a mixed run on the previous corpus) is in
  `results/accuracy/previous-fork-run/` and is not comparable to the table above.

**GumTree 4.0.0-beta4** was run in process on the 515 Java fixtures and scored by the same scorer
(`results/accuracy/gumtree-4.0.0-beta4/`; `tools/gumtree_eval/`). Scoped scoring (judges only the nodes GumTree's JDT tree can
express, so it is lenient to GumTree): changed-span F1 0.958 (`gumtree-simple`, the default), 0.961 (`gumtree-hybrid-id`), 0.846 (`gumtree-classic`);
perfect fixtures 74.2%, 74.0%, 31.3%. On the same Java fixtures difffold (refined) scores 0.965 and 75.9%, OmniDiff 0.978 and 83.9%. No intervals were
computed for this comparison. **DiffBenchmark's Defects4J oracle** (996 files of 800 bugs, a second annotation of overlapping inputs; `results/diffbenchmark/rerun-refine/`): perfect files
(FP = FN = 0) RefactoringMiner 88.5%, GumTree 3.0 simple 65.2%, difffold refined 64.4%, difffold top-down 45.1%, GumTree 3.0 greedy 21.0%; the refined-vs-simple raw F1 difference
(+0.00011) has an interval that includes zero. The oracle was derived from RefactoringMiner's output. See the paper, section 6.3, for the duplicate-record caveat in the benchmark's own summary.
RefactoringMiner was not re-run on the OmniDiff corpus; its earlier indicative scoring is in
`notes/lanes/GUMTREE-RM.md` (a different GumTree snapshot and a different corpus snapshot).

### Provenance of the recorded results

| Files | Producer | Machine / toolchain / baseline recorded? | Status |
|---|---|---|---|
| `harness/results/*` | `harness/run_all.sh`, `dfold-cli`, `cli_bench` | Yes: `machine.txt` (CPU, kernel, rustc 1.97.0, tool versions, difftastic 0.72.0, GumTree 4.0.0-beta4, OmniDiff `src_head=ca43e07`). Source head `ed61c79` is not in this repo's history. The run's input paths are scratch directories | Recorded run, single recording |
| `results/lines/lines*.csv`, `git-default-vs-minimal.csv` | `linebench`; the xdiff rows of `lines-xdiff.csv` from `tools/xdiff-baseline` | No | Historical/preliminary |
| `results/lines/xdiff-direct.csv`, `xdiff-nodiscard.csv` | A C harness around libgit2's xdiff described in `notes/lanes/RESULTS.md`; its source is **not in the repo** | No | Historical/preliminary; producer unknown |
| `results/lines/sync.csv`, `merge.csv`, `merge-nomergiraf.csv`, `abi.csv` | `syncbench`, `mergebench` (abi: `src/bin/abi_cutoff.rs`) | No | Historical/preliminary |
| `results/lines/ted-*.csv` | `tedbench` for the 17-column files; unknown for the rest (see table above) | No | Historical/preliminary |
| `results/fixtures-java-go-c.csv` | `src/bin/bench_fixtures.rs` | Partly: "4 vCPU cloud VM" only; no CPU, rustc, or OmniDiff commit | Historical/preliminary |
| `results/accuracy/*` (except `previous-fork-run/`, `gumtree/`) | `harness/accuracy.sh` (`src/bin/score_accuracy/`, `tools/omni_dump`, `harness/bootstrap_ci.py`) | Yes: `results/accuracy/machine.txt` (CPU, kernel, rustc, difffold commit, OmniDiff commit `ee5ee5b`, tree-sitter crate versions). The scorer is deterministic and not timing-sensitive | Reproducible; regenerated at the recorded commit |
| `results/accuracy/previous-fork-run/` | The same scorer at an earlier commit, on a private OmniDiff fork | No machine or commit; `ted` configuration not recorded | Historical/superseded |
| `harness/results/*-t4.*`, `SUMMARY-t4.md`, `machine-t4.txt` | `harness/run_all.sh` rows, `cli_bench`, `harness/paired_speed.py`, `harness/stage_summary.py`, `tools/omni_dump` (`omni_time`) | Yes: `machine-t4.txt`, with the load average per run | Recorded run under load (see Limitations) |
| `notes/lanes/RESULTS.md` | Narrative summary of the lanes | "Shared cloud VM, single run unless stated" | Historical/preliminary; not a source for new claims |

### Measurement setup

- **Machine (harness runs):** Intel Xeon 2.10 GHz, 4 vCPUs, 16 GB RAM, Linux 6.18
  (`harness/results/machine.txt`). Single-threaded tools, except the JVM and difftastic's rayon pool.
- **Limits:** 60 s wall time per run, SIGKILL on timeout (`harness/results/SUMMARY.md`).
- **Versions:** difftastic 0.72.0; GumTree 4.0.0-beta4; rustc 1.97.0 for the harness build (the library's
  minimum supported version is 1.89.0, below).
- **Not done:** multi-machine runs and idle-machine timing. Run `t4` (see below) is paired and repeated but taken under load.

## Theory: all-pairs shortest paths and tree edit distance

The exact solvers for general tree edit distance are closely tied to the all-pairs shortest-path problem
(APSP). This is the context for why `diff` restricts its objective. It is background, not a result of this
repository.

- **APSP.** Given a weighted graph, APSP asks for the shortest path between every pair of vertices. The
  classic algorithm is cubic in the number of vertices. Williams (2018) gave a subcubic algorithm, with a
  running time of n³ / 2^Ω(√log n).
- **Unrestricted ordered-tree edit distance is APSP-hard.** Bringmann, Gawrychowski, Mozes and Weimann (SODA
  2018) showed that a strongly subcubic algorithm for unrestricted ordered-tree edit distance would give a
  strongly subcubic algorithm for APSP. That is a conditional lower bound.
- **Weighted TED is fine-grained equivalent to APSP.** Nogler, Polak, Saha, Vassilevska Williams, Xu and Ye
  (arXiv 2411.06502, v3, March 2025) show this, and give an unweighted bound of O~(n^((3+ω)/2)), which is at
  most O(n^2.6857) with the best known ω. The previous best was O(n^2.9148) (Duerr 2023). See
  `notes/lanes/TED-THEORY.md`.
- **Bounded TED is subcubic in the distance.** Kociumaka and Shahali (arXiv 2507.02701, ESA 2025) compute
  bounded TED in O(n + k⁶ log k), where k is the distance bound.

These are theoretical algorithms. Nothing in this repository implements them or measures them, and no claim
is made here about how they would perform on real ASTs.

**What this means for difffold.** `diff` restricts the objective to top-down distance, in which a node can be
matched only if its parent is (Selkow 1977). The lower bounds above apply to the unrestricted problem. The
archived draft (`notes/archive/paper-draft-0.2.md`, section 2.5) states that whether the top-down objective inherits such a barrier is **open**, because
it is a restricted recurrence and must be analysed as one. `ted` solves the unrestricted problem exactly;
its pruning (threshold doubling, bands, label bound) is an exact speed-up whose cost on a given pair depends
on the distance, and `ted.rs` states no worst-case bound. Running times on the measured fixtures are in the
tables above, not derived from a bound.

## Build and run

The minimum supported Rust version is **1.89.0** (`rust-version` in `Cargo.toml`).

```sh
cargo test --locked --workspace
cargo test --locked -p difffold --features ts          # tree-sitter parsers
cargo test --locked --manifest-path fuzz/Cargo.toml    # seeded fuzz-target contracts
cargo run --locked -p difffold --bin dfdiff -- -U3 OLD NEW
```

`dfdiff` prints a unified diff that `git apply` accepts. It can also be used as a git external diff helper:
`GIT_EXTERNAL_DIFF=dfdiff git diff`. Its line algorithm is `difffold::lines`. Round-trip tests run `git
apply` on the output (`tests/roundtrip.rs`).

The git xdiff baseline is not in the root workspace. It lives in `tools/xdiff-baseline`, which has its own
`Cargo.lock`, so the libgit2 dependency is not in the root lock file.

The benchmark harness and the accuracy scorer need an OmniDiff checkout. Their paths are
environment-overridable (`DIFFS`, `OMNI`, `OMNI_SRC` in `harness/run_all.sh`). See
[docs/REPRODUCING.md](docs/REPRODUCING.md).

## Proofs

Lean 4.31.0. The tree on disk has three kinds of Lean content, with different strength (details and the
status of each stage in [proof/README.md](proof/README.md)):

- `proof/Difffold/` (five modules): theorems about a **Lean model** of the top-down objective: admissibility
  of the size bound, soundness of pruning, correctness of the threshold decision and of the widening loop,
  and the strip lemma (archived draft section 8.9; `proof/README.md`). Not linked to the Rust.
- `proof/Kernel/`, `proof/Lines/`: theorems about the **Aeneas translation of Rust**: `src/kernel.rs`
  (the threshold DP) and some helpers of `src/lines.rs`, with the hypotheses stated in `proof/README.md`.
- `proof/Myers/`, `proof/Myers2/`, `proof/Ted/`: models and partial lemmas for the Myers search and for four
  functions of `src/ted.rs` (through a copy tied to the source by agreement tests). **No theorem states that
  `ted` returns the optimal distance.**

`proof/README.md` is a status document that has not been brought fully up to date with `proof/Ted/` and
`proof/Myers*/` (its TED row says no TED theorem exists). Lean was not run when this section was written, so
read the per-file statements in `proof/` for the current state. There is **no CI for `proof/`**: Lean is not
installed in the default CI environment.

## Repository layout

| Path | What it is |
|---|---|
| `src/` | The library: `intern`, `diff`, `kernel`, `ted`, `lines`, `unified`, `mapping`, `merge`, `frontier` (experimental) |
| `src/bin/` | `dfdiff` and research binaries (the latter need the `ts` feature) |
| `gitcompat/` | Git diff and patch helpers, tested against `git apply` |
| `harness/` | Benchmark harness and its recorded results |
| `linebench/` | Line, sync, merge and TED benchmarks against imara-diff, similar, fast_rsync, qbsdiff and APTED (not published) |
| `tools/xdiff-baseline/` | Git xdiff via libgit2, outside the root workspace with its own lock file |
| `corpus/` | Mutation-corpus generator. **Excluded from the build**; some sources are missing |
| `proof/` | Lean 4 models and extraction-based proofs. See the Proofs section |
| `paper/`, `notes/` | Draft paper and research notes |
| `results/` | Recorded measurements |
| `fuzz/` | libFuzzer targets for the tree and line contracts |
| `docs/` | [ARCHITECTURE.md](docs/ARCHITECTURE.md), [REPRODUCING.md](docs/REPRODUCING.md), release and supply-chain notes |

## Stability

This is a research build with no stable API and no crates.io release. Versions `0.0.x` may change any public
item. When a release is made, it will follow Semantic Versioning, and changes that alter valid output
(including the diff a given input produces) will be treated as breaking.

## Security

See [SECURITY.md](SECURITY.md) for private reporting and the supply-chain policy. The library forbids
`unsafe` code. Dependencies are checked with `cargo deny` and `cargo audit` (see
[docs/SUPPLY-CHAIN.md](docs/SUPPLY-CHAIN.md)). The audit runs with no advisory exceptions.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md), [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md), and
[CONTRIBUTORS.md](CONTRIBUTORS.md).

## Related work

- [imara-diff](https://github.com/pascalkuthe/imara-diff): a fast line diff with Myers and Histogram
  algorithms. Its README describes fuzzing with cargo-fuzz, and benchmarks against `similar` on git history
  diffs of Linux, Rust, VSCode and Helix.
- [difftastic](https://github.com/Wilfred/difftastic): a syntax-aware diff that computes a shortest path
  through a syntax graph, with a line-oriented fallback when parsing fails. Its README describes known issues
  with many changes and memory use. It supports over 30 languages.
- [GumTree](https://github.com/GumTreeDiff/gumtree): a syntax-aware tree differencing tool. It is run here
  with the `gumtree-simple` matcher, through its `textdiff` command.
- [APTED](https://github.com/DatabaseGroup/apted): exact general tree edit distance, with a node mapping
  output. Its decomposition strategy is discussed in the archived draft, section 2. The `apted` crate used by `tedbench` is
  a Rust port.
- OmniDiff: a structural diff tool and benchmark with hand-authored mapping ground truth. It is the main
  baseline in this repository with an accuracy ground truth.

## License

Apache-2.0. See [LICENSE](LICENSE).
