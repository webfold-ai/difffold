# Security Policy

## Supported versions

difffold is a research prototype. It is not published to crates.io (`publish = false`) and has no
released versions yet. Only the default branch (`main`) receives security fixes.

| Version | Supported |
|---------|-----------|
| `main`  | Yes       |
| 0.0.x   | Not yet released; no backports |

## Reporting a vulnerability

Please **do not** open a public issue for a security problem.

Report it privately through GitHub's private vulnerability reporting:

<https://github.com/webfold-ai/difffold/security/advisories/new>

Include, where you can:

- the affected commit or branch, and the toolchain used (`rustc --version`);
- a minimal input or script that reproduces the problem;
- the impact you expect (crash, wrong output, unbounded memory or time, incorrect `git apply`
  result, and so on).

We will acknowledge a report, discuss severity with you, and coordinate a fix and disclosure
through a GitHub Security Advisory. We aim to acknowledge within one week. This is a
best-effort target for a research project, not a service commitment.

## What counts as a security issue here

difffold parses and diffs arbitrary input bytes (the line differ, the tree decoder in the fuzz
targets, and the `dfdiff` and `gitcompat` tools). These are in scope:

- panics, aborts, or unbounded allocation or time on attacker-controlled input;
- a patch or script that `git apply` or `replay_ok` accepts but that does not rebuild the
  intended result;
- memory-safety problems (the library forbids `unsafe` code; `unsafe` appears only in two
  benchmark binaries, see `src/bin/`).

Out of scope: accuracy or quality of diff output (report those as regular issues), performance
regressions without a security impact, and the unpublished benchmark crate `linebench` and its
dependency on `git2` (see `.cargo/audit.toml` for the documented exception).

## Supply chain

Dependency policy, advisory checks, SBOM generation and release signing are described in
[docs/SUPPLY-CHAIN.md](docs/SUPPLY-CHAIN.md).
