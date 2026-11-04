# difffold

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

Read [SPEC.md](SPEC.md) for the contracts and [paper/paper.md](paper/paper.md) for the
design, measurements, and limits. The paper is a draft (version 0.2, marked "in progress").

## Limitations

Read these before using the numbers below.

- **The objective is not OmniDiff's.** difffold computes top-down ordered-tree distance. It does
  not match across levels, detect moves, or recover wrap/unwrap. Cross-parent moves, wrap/unwrap,
  and split/merge are outside the objective.
- **Accuracy is behind OmniDiff on the same corpus.** See [Accuracy](#accuracy-against-ground-truth).
  On changed-span F1, OmniDiff scores 0.971 and difffold 0.843.
- **The Lean proofs are about a model.** The mechanised results in `proof/` are about a Lean model
  of the top-down objective. They are not extracted from or linked to the Rust code. The Rust
  replay contract (C3) is checked by tests and the fuzz targets, not by a proof.
- **Unit costs only.** Custom cost models are not supported, and the bounds are untested under them.
- **Languages.** The tree differ is measured on the eight languages with tree-sitter parsers wired
  in: C, Go, Java, JavaScript, Python, Rust, TSX and TypeScript.
- **Speed numbers are one run.** Variance is not characterised, and the paired protocol in paper
  section 7.4 has not been run.

## Measured results

### Cost against OmniDiff's recorded time

One run on a 4 vCPU cloud VM, release build, on 997 Java, Go and C fixtures from the OmniDiff
corpus. OmniDiff's figure is its recorded `diff_code` time on already-parsed trees. difffold's is
interning plus diff. **Both exclude the tree-sitter parse.** The objectives differ, so this compares
cost, not quality. Source: `results/fixtures-java-go-c.csv`, paper section 8.1.

| | OmniDiff | difffold |
|---|---:|---:|
| total | 16,735 ms | 1,239 ms |
| median | 9.6 ms | 0.89 ms |
| p90 | 33.5 ms | 2.3 ms |
| p99 | 126.7 ms | 4.3 ms |
| worst | 302.8 ms | 47.7 ms |

Per-fixture ratio: minimum 1.4, median 9.2, maximum 215. If difffold's time includes the tree-sitter
parse and OmniDiff's does not, the total ratio drops to 4.1. That comparison is not symmetric.

### Accuracy against ground truth

Scored against OmniDiff's hand-authored mapping ground truth on 1001 scorable fixtures in the eight
supported languages (748 fixtures are unscorable because difffold has no parser for their language).
Source: `results/accuracy/HEAD-TO-HEAD.md`, `results/accuracy/SUMMARY-difffold-only.md`.

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

### Proofs

Lean 4.31.0, five modules, no `sorry`, standard axioms only (`proof/AXIOMS.txt`). The headline
theorems cover the admissibility of the size bound, the soundness of pruning, the correctness of
the threshold decision and of the widening loop, and the strip lemma (paper section 8.9). **There is
no CI for `proof/`.** Lean is not installed in the default CI environment.

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

The benchmark harness needs an OmniDiff checkout. Its paths are environment-overridable
(`DIFFS`, `OMNI`, `OMNI_SRC` in `harness/run_all.sh`). See [docs/REPRODUCING.md](docs/REPRODUCING.md).

## Repository layout

| Path | What it is |
|---|---|
| `src/` | The library: `intern`, `diff`, `kernel`, `ted`, `lines`, `unified`, `mapping`, `merge` |
| `src/bin/` | Research binaries (`ts` feature) and `dfdiff` |
| `gitcompat/` | Git diff and patch helpers, tested against `git apply` |
| `harness/` | Benchmark harness and its recorded results |
| `linebench/` | Line-differ benchmarks against other libraries (not published) |
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
[docs/SUPPLY-CHAIN.md](docs/SUPPLY-CHAIN.md)).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md), [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md), and
[CONTRIBUTORS.md](CONTRIBUTORS.md).

## Related work

- [imara-diff](https://github.com/pascalkuthe/imara-diff): a fast line diff with Myers and
  Histogram algorithms.
- [difftastic](https://github.com/Wilfred/difftastic): a syntax-aware diff for display, with a
  line-diff fallback for unsupported languages.
- OmniDiff: a structural diff tool and benchmark with hand-authored mapping ground truth. It is the
  comparison corpus used here.

## License

Apache-2.0. See [LICENSE](LICENSE).
