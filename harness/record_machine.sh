#!/usr/bin/env bash
# Writes the machine, toolchain and source-revision record that sits next to a result set.
# usage: record_machine.sh OUT.txt [OMNIDIFF_CHECKOUT] [GUMTREE_ZIP]
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
OMNI=${2:-}
GT=${3:-}
{
  echo "date: $(date -u +%FT%TZ)"
  echo "cpu: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ //')"
  echo "nproc: $(nproc)"
  echo "mem_total_kb: $(awk '/MemTotal/{print $2}' /proc/meminfo)"
  echo "kernel: $(uname -srv)"
  echo "loadavg_at_record: $(cat /proc/loadavg)"
  echo "rustc: $(rustc -V)"
  echo "cargo: $(cargo -V)"
  echo "profile: release (opt-level 3, no LTO); OmniDiff tools: profile ci (release, lto off, 16 codegen units)"
  echo "java: $(java -version 2>&1 | grep -v 'Picked up' | head -1)"
  echo "git: $(git --version)"
  echo "difffold_commit: $(git -C "$here" rev-parse HEAD) ($(git -C "$here" status --porcelain | wc -l) uncommitted paths)"
  echo "tree-sitter crates: $(grep -A1 -E '^name = "tree-sitter(-[a-z]+)?"$' "$here/Cargo.lock" | grep -E 'name|version' | paste -sd' ' | sed 's/name = //g;s/version = //g')"
  echo "apeiron: $(grep -A2 'name = "apeiron"' "$here/Cargo.lock" | grep source)"
  if [[ -n $OMNI ]]; then
    echo "omnidiff_commit: $(git -C "$OMNI" rev-parse HEAD) (crate $(grep -m1 '^version' "$OMNI/Cargo.toml" | cut -d'"' -f2))"
  fi
  if [[ -n $GT ]]; then
    echo "gumtree: 4.0.0-beta4 release archive sha256 $(sha256sum "$GT" | cut -d' ' -f1)"
  fi
} > "$1"
