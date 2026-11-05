#!/usr/bin/env python3
"""Turns the run_matrix.sh TSV into winner tables for notes/lanes/STRING-BASELINES.md.

Usage: summarize.py <matrix.tsv>
Prints Markdown. Each cell shows the fastest supported tool and its median microseconds per
pair. Cells with no timed run show the status instead.
"""
import csv
import sys
from collections import defaultdict

TOOLS = ["edlib", "wfa", "rapidfuzz"]
SHORT = {"edlib": "Edlib", "wfa": "WFA2", "rapidfuzz": "RapidFuzz"}
ALPHS = ["2", "4", "256", "sparse-u32"]


def load(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def cell_key(r):
    return (r["job"], r["len"], r["alphabet"], r["regime"], r["k"], r["tool"])


def winner_text(rows_by_tool):
    timed = {t: float(r["med_us_per_pair"]) for t, r in rows_by_tool.items() if r["status"] == "ok"}
    if not timed:
        statuses = sorted({r["status"] for r in rows_by_tool.values()})
        return "/".join(statuses)
    best = min(timed, key=timed.get)
    others = sorted(v for t, v in timed.items() if t != best)
    text = f"**{SHORT[best]}** {timed[best]:.3g}"
    if others:
        text += f" ({others[0] / timed[best]:.3g}x)"
    return text


def main():
    rows = load(sys.argv[1])
    grid = defaultdict(dict)
    for r in rows:
        if r["job"] == "job":
            continue
        grid[(r["job"], r["regime"], r["len"], r["alphabet"], r["k"])][r["tool"]] = r

    print("## Exact distance (job a)\n")
    print("| regime | len | alphabet | winner (median us/pair, runner-up ratio) | Edlib | WFA2 | RapidFuzz |")
    print("|---|---|---|---|---|---|---|")
    exact_keys = sorted(
        {(k[1], k[2], k[3]) for k in grid if k[0] == "exact"},
        key=lambda x: (x[0], int(x[1]), x[2]),
    )
    for regime, length, alph in exact_keys:
        by_tool = grid[("exact", regime, length, alph, "-")]
        cols = []
        for t in TOOLS:
            r = by_tool.get(t)
            if r is None:
                cols.append("-")
            elif r["status"] == "ok":
                cols.append(f"{float(r['med_us_per_pair']):.4g}")
            else:
                cols.append(r["status"])
        print(f"| {regime} | {length} | {alph} | {winner_text(by_tool)} | " + " | ".join(cols) + " |")

    print("\n## Bounded threshold query (job b)\n")
    regimes = []
    for k_ in grid:
        if k_[0] == "bounded" and k_[1] not in regimes:
            regimes.append(k_[1])
    ks = ["1", "2", "4", "8", "32", "128"]
    for regime in regimes:
        print(f"### {regime}\n")
        print("| len | alphabet | " + " | ".join(f"k={k}" for k in ks) + " |")
        print("|---|---|" + "---|" * len(ks))
        lengths = sorted({k_[2] for k_ in grid if k_[0] == "bounded" and k_[1] == regime}, key=int)
        for length in lengths:
            for alph in ALPHS:
                cells = []
                any_row = False
                for k in ks:
                    by_tool = grid.get(("bounded", regime, length, alph, k))
                    if not by_tool:
                        cells.append("-")
                        continue
                    if all(r["status"] == "skip" for r in by_tool.values()):
                        cells.append(next(iter(by_tool.values()))["note"].split(":")[0] or "skip")
                        continue
                    any_row = True
                    cells.append(winner_text(by_tool))
                if any_row:
                    print(f"| {length} | {alph} | " + " | ".join(cells) + " |")
        print()


if __name__ == "__main__":
    main()
