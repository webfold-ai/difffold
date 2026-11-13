#!/usr/bin/env python3
"""Sums the `REFINE <fixture> RefineStats { .. }` lines that score_accuracy prints to stderr when
DFOLD_DEBUG is set (to the empty string, which matches every fixture). Reads stdin, writes markdown."""
import re, sys, collections
tot = collections.Counter(); nz = collections.Counter(); n = 0
for line in sys.stdin:
    if not line.startswith("REFINE "):
        continue
    n += 1
    for k, v in re.findall(r"(\w+): (\d+)", line):
        tot[k] += int(v)
        nz[k] += int(v) > 0
desc = [("seed", "top-down pairs kept (kind-changing pairs removed)"), ("dropped", "top-down pairs dropped for changing kind"),
        ("exact", "nodes paired by the exact-subtree phase"), ("invalid", "tentative pairs dropped by validate"),
        ("containers", "container pairs made"), ("recovered", "nodes paired by recover"),
        ("descended", "leaves paired by descend and retarget"), ("orphans", "leaf pairs dropped by the orphan rule")]
print(f"Refinement counters summed over {n} fixtures (Options::FULL).\n")
print("| counter | total | fixtures where it is non-zero | meaning |\n|---|---:|---:|---|")
for k, d in desc:
    print(f"| {k} | {tot[k]} | {nz[k]} | {d} |")
