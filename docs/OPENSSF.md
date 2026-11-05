# OpenSSF and Scorecard

This page maps difffold to the OpenSSF Scorecard checks and the OpenSSF Best Practices criteria,
and says what is not yet met. Status values: **met** (the repository has it), **partial**, **open**
(needs a maintainer action or a decision), and **not applicable**.

## Maintainer decisions needed

- **Resolved: CODEOWNERS.** `.github/CODEOWNERS` lists `@twn-lloyd @yokoszn`. Both are human
  maintainers. The default-branch ruleset still needs to be applied by a repository owner.
- **TODO: branch protection / ruleset.** Protect `main`: require the `Rust checks` status check,
  require pull requests with two approvals and code-owner review, block force-push and deletion, and
  allow no admin bypass. Nothing in this repository changes these settings.
- **TODO: visibility.** Scorecard publishing, the badge and several checks need a public repository.
  The repository is currently private.
- **TODO: OpenSSF Best Practices badge.** Register the project at <https://www.bestpractices.dev/>. The
  badge ID is not in this repository, and this document does not invent one.

## Scorecard checks

| Check | Status | Notes |
|---|---|---|
| Binary-Artifacts | met | No binaries are committed. Test fixtures are text. |
| Branch-Protection | open | Needs the ruleset above. |
| CI-Tests | met | `ci.yml` runs on every pull request. |
| CII-Best-Practices | open | Badge registration above. |
| Code-Review | open | Needs branch protection with approvals. |
| Contributors | open | Needs contributors from more than one organisation. Not something to fabricate. |
| Dangerous-Workflow | met | No untrusted-input injection; `zizmor` reports no findings. |
| Dependency-Update-Tool | met | `dependabot.yml` (cargo, `fuzz/`, GitHub Actions). |
| Fuzzing | met | `fuzz/` with two libFuzzer targets, run by `fuzz.yml`. |
| License | met | Apache-2.0, `LICENSE` at the root. |
| Maintained | open | Time-gated. |
| Packaging | not applicable | `publish = false`. Release binaries are built by `release.yml`. |
| Pinned-Dependencies | met | All actions pinned by SHA; cargo uses a committed lock file and `--locked`. |
| SAST | met | CodeQL (`security-extended`) in `codeql.yml`. |
| Security-Policy | met | `SECURITY.md`. |
| Signed-Releases | met (on tag) | Cosign bundles and SLSA provenance in `release.yml`. Verified only on a real tag. |
| Token-Permissions | met | Top-level `permissions`; `persist-credentials: false`. |
| Vulnerabilities | met | `cargo audit` and `cargo deny` in `supply-chain.yml`; one documented exception. |
| Webhooks | not applicable | No webhooks configured by this repository. |

Scores are not measured here. The Scorecard run in `scorecard.yml` is the source of truth once the
repository is public and publishing is enabled.

## Best Practices criteria

- **Basics.** Public-facing description and documentation: `README.md`, `CONTRIBUTING.md`,
  `CODE_OF_CONDUCT.md`. Open-source licence: Apache-2.0. Met.
- **Change control.** Git, pull requests and an issue tracker. Met. Status checks are required only
  after the ruleset is applied (TODO above).
- **Reporting.** `SECURITY.md` uses GitHub private vulnerability reporting. Met.
- **Quality.** Build and test scripts in `CONTRIBUTING.md`. A linter (clippy with `-D warnings`) and
  a formatter (rustfmt) in CI. Met.
- **Security.** Memory-safe implementation with no `unsafe` in the library. Fuzzing. Dependency
  checks. Met for the library; the benchmark binaries use `unsafe` and are not part of the library.
- **Analysis.** CodeQL and fuzzing. Met.

## What a maintainer must do to close the gaps

1. Fill in the CODEOWNERS placeholders.
2. Apply the branch protection ruleset.
3. Make the repository public, then run the Scorecard workflow once with `publish_results: true`.
4. Register the project for the Best Practices badge.
