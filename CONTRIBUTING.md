# Contributing to difffold

Thank you for considering a contribution. difffold is a research prototype, so the most useful
contributions are ones that come with a test, a measurement, or a stated contract.

## Before you start

- Read [SPEC.md](SPEC.md). Each change should keep the contracts it lists (I1, C2, C3 and the rest),
  or say explicitly which one it changes and why.
- Read the [README](README.md) limitations and its "Choose an engine" table. The `diff` engine's
  objective is top-down ordered-tree distance: moves, wrap/unwrap and cross-level matches are not
  implemented there, and that is not a bug. The `ted` engine matches across levels by child promotion but
  has no move operation.
- For a security issue, follow [SECURITY.md](SECURITY.md) instead of opening a public issue.

## Development setup

The workspace pins its minimum supported Rust version to **1.89.0** (`rust-version` in
`Cargo.toml`). Use that toolchain or a newer one.

```sh
cargo build --locked --workspace --all-targets
cargo test --locked --workspace
cargo test --locked -p difffold --features ts      # tree-sitter parsers
cargo test --locked --manifest-path fuzz/Cargo.toml
```

`corpus/` is excluded from the workspace because some of its sources are missing from the
repository. See the workspace comments in `Cargo.toml`.

## Before you open a pull request

CI runs these; running them locally first saves a round trip:

```sh
cargo fmt --all -- --check
cargo clippy --locked --workspace --all-targets -- -D warnings
cargo deny check advisories bans licenses sources
cargo audit --deny warnings
```

- Keep changes focused. Separate mechanical changes (formatting, renames) into their own commit.
- Add a test for every behavioural change. A property that the fuzz targets check should also have
  a seeded test in the normal suite.
- Do not add a dependency without a reason in the commit message. New git dependencies must be
  pinned by `rev` and the source must be allowed in `deny.toml`.
- Do not add `unsafe` code to the library. The library crate has `#![forbid(unsafe_code)]`.

## Commit and pull request conventions

- Commit subjects use a short type prefix: `build:`, `fix:`, `feat:`, `docs:`, `style:`, `test:`,
  `security:`, `ci:`.
- Describe *why* in the body, and reference the SPEC contract or measurement the change relies on.
- Fill in the pull request template. A reviewer will check the contracts and the verification
  output.

## Benchmarks and results

Numbers in `results/`, `harness/results/` and the paper are measurements from a named run. If you
change the algorithm, re-run the relevant harness and update the table in the same pull request.
Paths in `harness/run_all.sh` and `proof/run1.sh` contain machine-specific defaults; override them
with environment variables instead of editing the scripts.

## Code of conduct

This project follows the [Code of Conduct](CODE_OF_CONDUCT.md).

## License

By contributing you agree that your contribution is licensed under the Apache License, Version 2.0
(see [LICENSE](LICENSE)).
