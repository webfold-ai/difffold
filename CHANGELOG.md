# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The project uses
[Semantic Versioning](https://semver.org/) for its library API, which is still unstable.

## [Unreleased]

### Changed

- Cargo workspace: the root is the workspace root with `gitcompat`, `harness/rust` and `linebench`
  as members, sharing one `Cargo.lock`. `corpus/` is excluded (its sources are incomplete).
- `tree-sitter-language` is pinned to 0.1.7 to keep the declared MSRV of Rust 1.89.
- Formatting (rustfmt) and clippy fixes; `cargo clippy -- -D warnings` passes.

### Added

- Library forbids `unsafe_code`.
- `deny.toml` (cargo-deny policy) and `.cargo/audit.toml` (one documented exception, see the file).
- `fuzz/`: libFuzzer targets `fuzz_tree` (tree contracts C3, C5, C6) and `fuzz_lines` (line-diff
  replay), plus seeded tests of the same checks.
- Repository governance: README, CONTRIBUTING, CODE_OF_CONDUCT, SECURITY, CONTRIBUTORS, workflows
  (CI, CodeQL, fuzzing, Scorecard, dependency review, supply-chain, release), Dependabot.

## [0.0.1] - unreleased

Initial research import from `Ptyktos/research` (`difffold/`): the top-down ordered-tree differ,
the line differ, the `gitcompat` helper, the benchmark harness, and the draft paper and Lean proofs
under `paper/` and `proof/`.
