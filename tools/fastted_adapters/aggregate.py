#!/usr/bin/env python3
"""Aggregates the raw fastted CSV into a per-cell summary and a markdown matrix.

usage: aggregate.py RAW.csv TREES_DIR SUMMARY.csv MATRIX.md

Per (pair, tool, mode) cell it reports the timed reps (warm-up excluded), min, median and max of the
preprocessing time (`build` plus `index` for the C++ tools, `index` for difffold) and of the distance time,
and the median total. Every tool's distance must equal difffold's unknown-mode distance on the same pair,
otherwise the cell is marked DISAGREE and excluded from timing.

Threshold-mode cells charge the cost of obtaining tau. tau is difffold's exact distance, so its acquisition
cost is difffold's unknown-mode total for the same pair (median of its reps). charged_total_us = tool total
+ that cost.
"""
import csv
import os
import statistics
import sys
from collections import defaultdict

PREP_PHASES = {"build", "index", "prep"}
TOOL_LABELS = {
    ("difffold", "unknown"): "difffold ted",
    ("difffold", "threshold"): "difffold ted_within",
    ("apted", "unknown"): "APTED (C++)",
    ("touzet_baseline", "unknown"): "Touzet baseline ted() (TopDiff path)",
    ("touzet_baseline", "threshold"): "Touzet baseline ted_k",
    ("touzet_krset", "unknown"): "Touzet KR-set ted()",
    ("touzet_krset", "threshold"): "Touzet KR-set ted_k",
    ("touzet_dp", "unknown"): "Touzet depth-pruning ted()",
    ("touzet_dp", "threshold"): "Touzet depth-pruning ted_k",
    ("xted-t1", "unknown"): "X-TED CPU (1 thread)",
    ("xted-t4", "unknown"): "X-TED CPU (4 threads)",
}
COLUMNS = [
    "pair", "regime", "shape", "nodes_a", "nodes_b", "reference_distance", "tool", "mode",
    "status", "n_timed", "prep_min_us", "prep_med_us", "prep_max_us",
    "dist_min_us", "dist_med_us", "dist_max_us", "total_med_us", "charged_total_med_us", "note",
]


def load_tree_sizes(trees_dir):
    sizes = {}
    for kind in ("real", "syn"):
        base = os.path.join(trees_dir, kind)
        if not os.path.isdir(base):
            continue
        for pair in os.listdir(base):
            with open(os.path.join(base, pair, "a.tree")) as fa, open(os.path.join(base, pair, "b.tree")) as fb:
                sizes[pair] = (int(fa.readline()), int(fb.readline()))
    return sizes


def describe(pair):
    if pair.startswith("syn-"):
        _, regime, shape, _n = pair.split("-")
        return ("mutation" if regime == "mut" else "unrelated"), shape
    return "real AST", "java-ast"


def main():
    raw_path, trees_dir, summary_path, md_path = sys.argv[1:5]
    sizes = load_tree_sizes(trees_dir)

    cells = defaultdict(lambda: defaultdict(dict))  # (pair, tool, mode) -> rep -> phase -> row
    for row in csv.DictReader(open(raw_path)):
        key = (row["pair"], row["tool"], row["mode"])
        cells[key][int(row["rep"])][row["phase"]] = row

    def reps_of(key):
        return cells.get(key, {})

    results = []
    pairs = sorted({k[0] for k in cells}, key=lambda p: (describe(p)[0], describe(p)[1], sizes.get(p, (0,))[0]))
    for pair in pairs:
        ref_key = ("difffold", "unknown")
        ref_rows = [r for rep, ph in reps_of((pair, *ref_key)).items() if rep > 0 for r in [ph.get("dist")] if r and r["status"] == "ok"]
        ref_distances = {r["distance"] for r in ref_rows}
        if len(ref_distances) != 1:
            print(f"reference distances for {pair} are not unique or missing: {ref_distances}", file=sys.stderr)
            continue
        D = ref_distances.pop()
        ref_totals = []
        for rep, ph in reps_of((pair, *ref_key)).items():
            if rep > 0 and "dist" in ph and ph["dist"]["status"] == "ok":
                ref_totals.append(sum(int(ph[p]["us"]) for p in ph if p in ("prep", "dist")))
        bound_cost = statistics.median(ref_totals) if ref_totals else None

        for (tool, mode), label in TOOL_LABELS.items():
            key = (pair, tool, mode)
            reps = reps_of(key)
            na, nb = sizes.get(pair, (None, None))
            regime, shape = describe(pair)
            base = {
                "pair": pair, "regime": regime, "shape": shape, "nodes_a": na, "nodes_b": nb,
                "reference_distance": D, "tool": label, "mode": mode,
            }
            if not reps:
                results.append({**base, "status": "not run", "note": "no output row: the first run did not finish within the 75 s cap, or the cell was interrupted by a runner restart"})
                continue
            if any("dist" in ph and ph["dist"]["status"] == "gt60s" for ph in reps.values()):
                results.append({**base, "status": "skipped", "note": "a run exceeded 60 s"})
                continue
            ok_reps = [rep for rep, ph in reps.items() if rep > 0 and "dist" in ph and ph["dist"]["status"] in ("ok", "above_tau")]
            if any(rep > 0 and "dist" in ph and ph["dist"]["status"] == "above_tau" for rep, ph in reps.items()):
                results.append({**base, "status": "above_tau", "note": "tool reported distance above tau"})
                continue
            if not ok_reps:
                results.append({**base, "status": "skipped", "note": "no completed timed run (killed or error)"})
                continue
            distances = {reps[rep]["dist"]["distance"] for rep in ok_reps}
            if distances != {D}:
                results.append({**base, "status": "DISAGREE", "note": f"distances {sorted(distances)} vs difffold {D}; excluded from timing"})
                continue
            prep = [sum(int(reps[rep][p]["us"]) for p in reps[rep] if p in PREP_PHASES) for rep in ok_reps]
            dist = [int(reps[rep]["dist"]["us"]) for rep in ok_reps]
            total = [p + d for p, d in zip(prep, dist)]
            total_med = statistics.median(total)
            charged = None
            note = ""
            if mode == "threshold":
                charged = total_med + bound_cost if bound_cost is not None else None
                note = "tau = difffold distance; bound cost charged"
            if len(ok_reps) < 7:
                note = (note + "; " if note else "") + f"only {len(ok_reps)} timed reps"
            results.append({
                **base, "status": "ok", "n_timed": len(ok_reps),
                "prep_min_us": min(prep), "prep_med_us": statistics.median(prep), "prep_max_us": max(prep),
                "dist_min_us": min(dist), "dist_med_us": statistics.median(dist), "dist_max_us": max(dist),
                "total_med_us": total_med,
                "charged_total_med_us": charged if charged is not None else "",
                "note": note,
            })

    with open(summary_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS, extrasaction="ignore")
        w.writeheader()
        for r in results:
            w.writerow(r)

    # Markdown matrix: one row per pair, one column per tool and mode, median total in ms.
    order = list(TOOL_LABELS.values())
    by_pair = defaultdict(dict)
    meta = {}
    for r in results:
        meta[r["pair"]] = (r["regime"], r["shape"], r["nodes_a"], r["nodes_b"], r["reference_distance"])
        by_pair[r["pair"]][r["tool"]] = r
    thr_labels = {"difffold ted_within", "Touzet baseline ted_k", "Touzet KR-set ted_k", "Touzet depth-pruning ted_k"}
    header_cells = [t + (" (charged)" if t in thr_labels else "") for t in order]
    lines = [
        "| regime | shape | nodes A/B | D | " + " | ".join(header_cells) + " |",
        "|---|---|---|---|" + "---|" * len(order),
    ]
    for pair in sorted(by_pair, key=lambda p: (meta[p][0], meta[p][1], meta[p][2] or 0)):
        regime, shape, na, nb, D = meta[pair]
        cols = []
        for t in order:
            r = by_pair[pair].get(t)
            if r is None or r["status"] == "not run":
                cols.append("n/a")
            elif r["status"] == "ok":
                val = r["charged_total_med_us"] if t in thr_labels else r["total_med_us"]
                cols.append(f"{float(val) / 1000:.2f} ms")
            elif r["status"] == "DISAGREE":
                cols.append("DISAGREE")
            else:
                cols.append(r["status"] + (f" ({r['note']})" if r.get("note") else ""))
        lines.append(f"| {regime} | {shape} | {na} / {nb} | {D} | " + " | ".join(cols) + " |")
    with open(md_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {len(results)} cells to {summary_path} and {md_path}")


if __name__ == "__main__":
    main()
