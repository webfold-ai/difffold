## Summary

<!-- What changes, and why. Name the SPEC contract (I1, C2, C3, ...) the change relies on or changes. -->

## Changes

-

## Verification

<!-- Paste the output lines for the commands you ran, for example: -->

- [ ] `cargo fmt --all -- --check`
- [ ] `cargo clippy --locked --workspace --all-targets -- -D warnings`
- [ ] `cargo test --locked --workspace`
- [ ] `cargo test --locked -p difffold --features ts` (if the change touches the tree-sitter parsers)
- [ ] `cargo test --locked --manifest-path fuzz/Cargo.toml` (if the change touches the library)
- [ ] `cargo deny check advisories bans licenses sources` (if dependencies changed)

## Measurements

<!-- If a result file or a number in the README changes, say which run produced it. Otherwise delete. -->

## Notes for reviewers

<!-- Anything that is not obvious from the diff. Mechanical changes belong in their own commit. -->
