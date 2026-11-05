# difffold

> **Status: research build.** This code is not production-ready. It is being hardened toward a production release, and interfaces, formats and results may change without notice.

[![CI](https://github.com/webfold-ai/difffold/actions/workflows/ci.yml/badge.svg)](https://github.com/webfold-ai/difffold/actions/workflows/ci.yml)
[![CodeQL](https://github.com/webfold-ai/difffold/actions/workflows/codeql.yml/badge.svg)](https://github.com/webfold-ai/difffold/actions/workflows/codeql.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

difffold is an ordered-tree differ on an exact hash-consed arena, and a line differ with a
git-compatible unified-diff output. It is a **research prototype**. It is not a finished tool, and
it is not published to crates.io (`publish = false`).

- The tree differ solves one stated objective exactly: top-down ordered-tree edit distance.
- Node identity is exact by construction. Two nodes have equal ids if and only if their subtrees
  are structurally equal (SPEC contract I1). It uses no fold-hash comparison.
- The alignment is a threshold dynamic program. A result is accepted only when an admissible bound
  certifies it (C2). Every edit script is replayed on the before-tree and must rebuild the
  after-tree id for id (C3).

Read [SPEC.md](SPEC.md) for the contracts and [paper/paper.md](paper/paper.md) for the design,
measurements, and limits. The paper is a draft (version 0.2, marked "in progress").

## Limitations

Read these before using the numbers below.

- **The objective is not OmniDiff's.** difffold computes top-down ordered-tree distance. It does
  not match across levels, detect moves, or recover wrap/unwrap. Cross-parent moves, wrap/unwrap,
  and split/merge are outside the objective.
- **Accuracy has been measured against one ground truth only.** The only accuracy scoring in this
  repository is against OmniDiff's hand-authored mappings. Accuracy against difftastic, GumTree,
  diffsitter or imara-diff has **not been measured**. See [Testing against other tools](#testing-against-other-tools).
- **The Lean proofs are about a model.** The mechanised results in `proof/` are about a Lean model
  of the top-down objective. They are not extracted from or linked to the Rust code. The Rust
  replay contract (C3) is checked by tests and the fuzz targets, not by a proof.
- **Unit costs only.** Custom cost models are not supported, and the bounds are untested under them.
- **Languages.** The tree differ is measured on the eight languages with tree-sitter parsers wired
  in: C, Go, Java, JavaScript, Python, Rust, TSX and TypeScript.
- **Speed numbers are mostly one run.** Variance is not characterised, and the paired protocol in
  paper section 7.4 has not been run.

## Testing against other tools

difffold is compared against several baselines. They solve different problems, so the comparisons
below separate **what was measured** from **what was not**. Every number cites the file it came
from. Where a figure is a median computed from a CSV, the computation is described in the table
note; the CSVs are the source.

| Baseline | Problem it solves | What is measured here | Source | Not measured |
|---|---|---|---|---|
| similar (Myers) | line diff | time and edit cost, 2,302 fixtures | `results/lines/lines-xdiff.csv` | accuracy against a line-diff ground truth |
| imara-diff (Myers, Histogram, Myers-minimal) | line diff | time and edit cost, same fixtures | `results/lines/lines-xdiff.csv` | — |
| git xdiff (libgit2, default and minimal) | line diff | time and edit cost, same fixtures | `results/lines/lines-xdiff.csv` | — |
| fast_rsync and qbsdiff | delta encoding | time, delta size, round-trip check | `results/lines/sync.csv` | compression ratio against a reference encoder |
| git merge-file and mergiraf | 3-way merge | outcome labels, 800 cases per tool | `results/lines/merge.csv` | merge quality on real conflicts |
| difftastic 0.72.0 | syntax-graph diff | wall time, 80 fixtures | `harness/results/cli-t1.csv` | accuracy; its own syntax-tree objective |
| GumTree 4.0.0-beta4 | heuristic tree matching | wall time, 80 fixtures | `harness/results/cli-t1.csv` | accuracy |
| diffsitter | AST node diff | wall time, 80 fixtures | `harness/results/cli-t3.csv` | accuracy |
| APTED | general tree edit distance | time and distance, 40 to 150 fixtures per file | `results/lines/ted-*.csv` | accuracy; different objective |
| OmniDiff | structural diff with its own ground truth | cost and accuracy, 997 to 1001 fixtures | `results/fixtures-java-go-c.csv`, `results/accuracy/` | — |

### Line diff: similar, imara-diff, git xdiff

`results/lines/lines-xdiff.csv` runs every line algorithm on the same 2,302 before/after fixture
pairs. Each timed call includes that library's own input preparation, as `linebench` times it.
"Same cost as similar" counts fixtures where the reported edit cost equals similar's Myers cost on
that fixture. It is an agreement check between tools, not a correctness score: the algorithms
optimise different costs in some cases.

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

These are one run. The machine for this file is not recorded in `results/`. The imara-diff
README compares its Histogram and Myers algorithms only against `similar`, on git tag-to-tag
diffs of Linux, Rust, VSCode and Helix. It reports its Histogram speedup as self-measured. This
repository does not reproduce that benchmark, so no speedup claim against imara-diff is made here
beyond the table above.

Patch-stage timings (`patch-difffold`, `patch-similar-myers`, `patch-imara-myers`) are in the same
file and are not summarised here.

### Tree diff: difftastic, GumTree, diffsitter

The harness runs each tool as a command-line process on 80 fixtures and records wall time
(`harness/results/cli-t1.csv`, `cli-t3.csv`). The medians below are computed over the 80
per-fixture medians in `cli-t1.csv`, so they include process start-up for every tool.
`harness/results/SUMMARY.md` uses a different aggregation (for example, 9.5 ms for difffold where
this table gives 10.49 ms), so the two should not be mixed.

| tool | median wall ms | p90 wall ms |
|---|---:|---:|
| git-histogram | 3.39 | 4.04 |
| git-myers | 3.40 | 4.12 |
| git-minimal | 3.47 | 4.29 |
| git-patience | 3.53 | 4.13 |
| difffold (distance and diff) | 10.49 | 23.91 |
| difffold-distance | 10.73 | 24.41 |
| difftastic 0.72.0 | 46.14 | 155.72 |
| selkow-ref (plain DP oracle) | 319.20 | 2365.57 |
| GumTree 4.0.0-beta4 (`gumtree-simple`) | 1012.68 | 1184.41 |

`diffsitter` was run on the same fixtures in `cli-t3.csv`; its aggregate is in `SUMMARY.md`.

What these numbers do and do not show:

- **Objectives differ.** difftastic computes a shortest path through a syntax graph (with
  Dijkstra's algorithm, per its README). GumTree uses heuristic matching. difffold computes exact
  top-down edit distance. Speed is not a quality comparison.
- **difftastic was run with limits.** `harness/results/tools-t1.tsv` gives
  `--byte-limit 1000000 --graph-limit 3000000` and `DFT_UNSTABLE=yes`. Results on larger inputs
  may change with those limits.
- **Accuracy against difftastic and GumTree is not measured.** There is no ground truth for these
  fixtures in this repository, so no statement about which tool is more correct is made.
- **difffold's own oracle is in the table.** `selkow-ref` is the plain dynamic program that
  difffold's exact solver is checked against (SPEC contract C4).

### Tree edit distance: APTED

`results/lines/ted-large.csv`, `ted-mid.csv`, `ted-mid2.csv` and `ted-small.csv` record difffold's
time and APTED's time on the same tree pairs. Every APTED run completed in these files.

| file | fixtures | difffold median ms | APTED median ms |
|---|---:|---:|---:|
| `ted-small.csv` | 97 | 0.467 | 3.78 |
| `ted-mid.csv` | 150 | 18.79 | 192.65 |
| `ted-mid2.csv` | 150 | 14.53 | 187.00 |
| `ted-large.csv` | 40 | 72.25 | 2,512.64 |

APTED computes general tree edit distance, which allows child promotion (see paper section 2 and
the cross-objective comparison in section 7.2). difffold computes top-down distance. The two
times are the cost of two different problems, not of one problem solved two ways. The ratio shows
how much the restriction saves on these inputs. It does not show that difffold's distance equals
APTED's.

### Delta sync and 3-way merge

`results/lines/sync.csv` has 800 fixture rows per tool. Every row is marked `verified = true`.
Median times: difffold line delta 88 µs, fast_rsync (block size 512) 40 µs, qbsdiff 1,508 µs.
The file also records delta and deflated sizes, which are not summarised here.

`results/lines/merge.csv` has 800 cases per tool, labelled with an outcome by the harness:

| tool | correct | conflict flagged | false conflict | silently wrong |
|---|---:|---:|---:|---:|
| difffold-merge3 | 392 | 400 | 7 | 1 |
| git merge-file | 392 | 400 | 6 | 2 |
| mergiraf | 379 | 400 | 4 | 17 |

The labels are those written by the harness. This is a small, labelled set, and it does not
establish merge quality on real conflicts.

### OmniDiff: cost and accuracy

OmniDiff is one baseline among these. It is the only one for which this repository holds
hand-authored ground truth, so it is the only one scored for accuracy.

**Cost** (997 Java, Go and C fixtures, `results/fixtures-java-go-c.csv`, paper section 8.1). One run
on a 4 vCPU cloud VM, release build. OmniDiff's figure is its recorded `diff_code` time on
already-parsed trees. difffold's is interning plus diff. **Both exclude the tree-sitter parse.**
The objectives differ, so this compares cost, not quality.

| | OmniDiff | difffold |
|---|---:|---:|
| total | 16,735 ms | 1,239 ms |
| median | 9.6 ms | 0.89 ms |
| p90 | 33.5 ms | 2.3 ms |
| p99 | 126.7 ms | 4.3 ms |
| worst | 302.8 ms | 47.7 ms |

Per-fixture ratio: minimum 1.4, median 9.2, maximum 215. If difffold's time includes the tree-sitter
parse and OmniDiff's does not, the total ratio drops to 4.1. That comparison is not symmetric.

**Accuracy** (1001 scorable fixtures in the eight supported languages; 748 are unscorable because
difffold has no parser for their language). Source: `results/accuracy/HEAD-TO-HEAD.md`,
`results/accuracy/SUMMARY-difffold-only.md`.

| metric (micro) | difffold | OmniDiff |
|---|---:|---:|
| pair F1 | 0.998 | 1.000 |
| node-correspondence accuracy | 0.996 | 0.999 |
| changed-span F1 | 0.843 | 0.971 |
| fixtures with zero visible mismatches | 56.8% | 81.2% |

OmniDiff is ahead on every aggregate. Pair F1 is close because about 99.8% of ground-truth pairs are
unchanged context. Most of the gap is wrap/unwrap decisions, which a top-down matcher cannot make.
The scorer also favours OmniDiff: the ground truth is OmniDiff's own, and OmniDiff was tuned on this
corpus. Treat OmniDiff's numbers as the upper end.

The paper's section 8.5 still reads `PENDING`. The results above are the current source.

### Measurement setup

- **Machine (harness runs):** Intel Xeon 2.10 GHz, 4 vCPUs, 16 GB RAM, Linux 6.18
  (`harness/results/machine.txt`). Single-threaded tools, except the JVM and difftastic's rayon pool.
- **Limits:** 60 s wall time per run, SIGKILL on timeout (`harness/results/SUMMARY.md`).
- **Versions:** difftastic 0.72.0; GumTree 4.0.0-beta4; rustc 1.97.0 for the harness build (the
  library's minimum supported version is 1.89.0, below).
- **Not done:** the paired timing protocol (paper section 7.4), multi-machine runs, and variance
  estimates.

## Theory: all-pairs shortest paths and tree edit distance

The exact solvers for general tree edit distance are closely tied to the all-pairs shortest-path
problem (APSP). This is the context for why difffold restricts its objective.

- **APSP.** Given a weighted graph, APSP asks for the shortest path between every pair of vertices.
  The classic algorithm is cubic in the number of vertices. Williams (2018) gave a subcubic
  algorithm, with a running time of n³ / 2^Ω(√log n).
- **Unrestricted ordered-tree edit distance is APSP-hard.** Bringmann, Gawrychowski, Mozes and
  Weimann (SODA 2018) showed that a strongly subcubic algorithm for unrestricted ordered-tree edit
  distance would give a strongly subcubic algorithm for APSP. That is a conditional lower bound.
- **Weighted TED is fine-grained equivalent to APSP.** Nogler, Polak, Saha, Vassilevska Williams,
  Xu and Ye (arXiv 2411.06502, v3, March 2025) show this, and give an unweighted bound of
  O~(n^((3+ω)/2)), which is at most O(n^2.6857) with the best known ω. The previous best was
  O(n^2.9148) (Duerr 2023). See `notes/lanes/TED-THEORY.md`.
- **Bounded TED is subcubic in the distance.** Kociumaka and Shahali (arXiv 2507.02701, ESA 2025)
  compute bounded TED in O(n + k⁶ log k), where k is the distance bound.

These are theoretical algorithms. At the sizes of real ASTs (up to about 6,000 nodes, per the
notes), the constants in the fast matrix multiplication would dominate. No practical implementation
of these algorithms is claimed here.

**What this means for difffold.** difffold restricts the objective to top-down distance, in which
a node can be matched only if its parent is (Selkow 1977). The lower bounds above apply to the
unrestricted problem. The paper (section 2.5) states that whether the top-down objective inherits
such a barrier is **open**, because it is a restricted recurrence and must be analysed as one. The
threshold dynamic program is exact and certified for that restriction. Its running time on the
measured fixtures is in the tables above, not from a worst-case bound.

## Build and run

The minimum supported Rust version is **1.89.0** (`rust-version` in `Cargo.toml`).

```sh
cargo test --locked --workspace
cargo test --locked -p difffold --features ts          # tree-sitter parsers
cargo test --locked --manifest-path fuzz/Cargo.toml    # seeded fuzz-target contracts
cargo run --locked -p difffold --bin dfdiff -- -U3 OLD NEW
```

`dfdiff` prints a unified diff that `git apply` accepts. It can also be used as a git external diff
helper: `GIT_EXTERNAL_DIFF=dfdiff git diff`. Its line algorithm is `difffold::lines`. Round-trip
tests run `git apply` on the output (`tests/roundtrip.rs`).

The git xdiff baseline is not in the root workspace. It lives in `tools/xdiff-baseline`, which has
its own `Cargo.lock`, so the libgit2 dependency is not in the root lock file.

The benchmark harness needs an OmniDiff checkout. Its paths are environment-overridable
(`DIFFS`, `OMNI`, `OMNI_SRC` in `harness/run_all.sh`). See [docs/REPRODUCING.md](docs/REPRODUCING.md).

## Proofs

Lean 4.31.0, five modules, no `sorry`, standard axioms only (`proof/AXIOMS.txt`). The headline
theorems cover the admissibility of the size bound, the soundness of pruning, the correctness of
the threshold decision and of the widening loop, and the strip lemma (paper section 8.9). **There is
no CI for `proof/`.** Lean is not installed in the default CI environment.

## Repository layout

| Path | What it is |
|---|---|
| `src/` | The library: `intern`, `diff`, `kernel`, `ted`, `lines`, `unified`, `mapping`, `merge` |
| `src/bin/` | Research binaries (`ts` feature) and `dfdiff` |
| `gitcompat/` | Git diff and patch helpers, tested against `git apply` |
| `harness/` | Benchmark harness and its recorded results |
| `linebench/` | Line-differ benchmarks against imara-diff, similar, fast_rsync and qbsdiff (not published) |
| `tools/xdiff-baseline/` | Git xdiff via libgit2, outside the root workspace with its own lock file |
| `corpus/` | Mutation-corpus generator. **Excluded from the build**; some sources are missing |
| `proof/` | Lean 4 model of the objective. Not linked to the Rust |
| `paper/`, `notes/` | Draft paper and research notes |
| `results/` | Recorded measurements |
| `fuzz/` | libFuzzer targets for the tree and line contracts |

## Stability

This is a research prototype with no published API. Versions `0.0.x` may change any public item.
When a release is made, it will follow Semantic Versioning, and changes that alter valid output
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
  algorithms. Its README describes fuzzing with cargo-fuzz, and benchmarks against `similar` on git
  history diffs of Linux, Rust, VSCode and Helix.
- [difftastic](https://github.com/Wilfred/difftastic): a syntax-aware diff that computes a shortest
  path through a syntax graph, with a line-oriented fallback when parsing fails. Its README
  describes known issues with many changes and memory use. It supports over 30 languages.
- [GumTree](https://github.com/GumTreeDiff/gumtree): a syntax-aware tree differencing tool. It is
  run here with the `gumtree-simple` matcher, through its `textdiff` command.
- [APTED](https://github.com/DatabaseGroup/apted): exact general tree edit distance, with a node
  mapping output. Its decomposition strategy is discussed in paper section 2.
- OmniDiff: a structural diff tool and benchmark with hand-authored mapping ground truth. It is the
  only baseline in this repository with an accuracy ground truth.

## License

Apache-2.0. See [LICENSE](LICENSE).
