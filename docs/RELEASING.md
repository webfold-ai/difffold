# Releasing

Releases are cut from a version tag. The `release.yml` workflow does the rest.

1. Update `version` in `Cargo.toml` and add a section to `CHANGELOG.md`.
2. Make sure `main` is green: `ci.yml`, `codeql.yml`, `supply-chain.yml` and `fuzz.yml`.
3. Tag the commit with `v<version>`, for example `v0.0.1`, and push the tag.
4. The release workflow checks that the tag matches `Cargo.toml`, builds
   `dfdiff` with `--locked` on Rust 1.89.0, packages it, signs it with cosign (keyless, bundle
   format), and creates a SLSA provenance attestation.
5. The workflow creates a **draft** GitHub release with the assets. A maintainer reviews the draft,
   checks the verification steps in [SUPPLY-CHAIN.md](SUPPLY-CHAIN.md), and publishes it.

The release is not published to crates.io (`publish = false` in `Cargo.toml`).

Only Linux x86_64 binaries are built. Other platforms need a separate job.
