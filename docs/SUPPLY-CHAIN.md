# Supply chain

This page describes how difffold's dependencies are controlled, how the build is checked, and how a
release can be verified. The checks run in `.github/workflows/supply-chain.yml`, `ci.yml` and
`release.yml`.

## Dependencies

- **Lock file.** `Cargo.lock` at the root covers the workspace. `fuzz/Cargo.lock` covers the fuzz
  crate. Every CI build uses `--locked`, so a change to dependencies must be committed.
- **Git dependency.** `apeiron` comes from `https://github.com/webfold-ai/apeiron`, pinned by
  `rev = "07ab506"` in `Cargo.toml`. It is the only git source allowed in `deny.toml`.
- **Registry.** crates.io only (`deny.toml` denies unknown registries and git sources).
- **Versions.** Wildcard version requirements are denied. Path dependencies between workspace
  members are exempt.
- **Licences.** An allow-list of permissive licences is in `deny.toml`. Anything else fails the
  `licenses` check.
- **Updates.** Dependabot proposes weekly updates for the root workspace, `fuzz/`, and GitHub
  Actions, with a 7-day cooldown.

## Automated checks

| Check | Command | Where |
|---|---|---|
| Advisories, bans, licences, sources | `cargo deny check advisories bans licenses sources` | `supply-chain.yml` (daily and on change) |
| RustSec advisories | `cargo audit --deny warnings` | `supply-chain.yml` |
| Dependency review on pull requests | `actions/dependency-review-action` | `dependency-review.yml` (needs GitHub Advanced Security on a private repository) |
| Static analysis | CodeQL, `security-extended` | `codeql.yml` |
| Fuzzing | `cargo fuzz run fuzz_tree`, `fuzz_lines` | `fuzz.yml` |
| SBOM | CycloneDX JSON, `difffold.sbom.json` | `supply-chain.yml` (artifact, 90 days) |
| Workflow security | `zizmor` (run locally; not yet in CI) | see below |

### Audited exceptions

None. `.cargo/audit.toml` has no ignores, and `cargo audit --deny warnings` passes on the root
workspace.

The earlier exceptions for **RUSTSEC-2026-0183** and **RUSTSEC-2026-0184** (unsound `git2` 0.20.4)
were removed by moving the git xdiff baseline out of the root workspace. It is now
`tools/xdiff-baseline`, which has its own `Cargo.lock` and is not part of the root lock file. That
lock file still pins `git2` 0.20.4, so `cargo audit -f tools/xdiff-baseline/Cargo.lock` reports
both advisories. CI does not audit that lock file. It is a benchmark tool, not part of the
published surface.

## Build integrity

- Actions are pinned by full commit SHA. The tag each SHA came from is in a comment on the same line.
- Every checkout uses `persist-credentials: false`. Workflows declare `permissions` at the top
  level, and `contents: read` unless a job needs more.
- The library has `#![forbid(unsafe_code)]`.
- The toolchain is pinned to 1.89.0 in the CI and release workflows.

## Verifying a release

Each release publishes, for the Linux x86_64 binary:

- `dfdiff-<tag>-linux-x86_64.tar.gz`, the archive;
- `dfdiff-<tag>-linux-x86_64.tar.gz.sigstore.json`, a cosign bundle (signature, certificate and
  transparency-log entry) for the archive;
- `dfdiff-<tag>-linux-x86_64.tar.gz.intoto.jsonl`, a SLSA build provenance attestation;
- `SHA256SUMS` and `SHA256SUMS.sigstore.json`.

Check the signature. The identity constraints are checked here, at verification time:

```sh
cosign verify-blob \
  --bundle dfdiff-v0.0.1-linux-x86_64.tar.gz.sigstore.json \
  --certificate-identity-regexp '^https://github.com/webfold-ai/difffold/\.github/workflows/release\.yml@refs/tags/v0\.0\.1$' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  dfdiff-v0.0.1-linux-x86_64.tar.gz
```

Check the provenance:

```sh
gh attestation verify dfdiff-v0.0.1-linux-x86_64.tar.gz --repo webfold-ai/difffold
```

Check the checksum:

```sh
sha256sum --check SHA256SUMS
```

Replace `v0.0.1` with the tag you are verifying. Releases are created as drafts and are published by
a maintainer after review.

## Workflow linting

`zizmor` checks workflow files for injection and permission problems. Run it before changing a
workflow:

```sh
pip install zizmor
zizmor --offline .github
```

It reported no findings on the current workflows.
