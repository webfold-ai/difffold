#!/usr/bin/env python3
"""Per-stage speed summary: difffold (dfold-cli --reps N, hot in-process view) against OmniDiff
(`tools/omni_dump` `omni_time`), on the fixtures both ran.

usage: stage_summary.py (--paired paired.csv | --cli cli.csv --omni omni_time.csv) --out DIR

  --paired   written by harness/paired_speed.py: the three measurements of each fixture run back to back in
             shuffled order. This is the primary input: both tools saw the same load.
  --cli/--omni  the cold-process harness rows (`difffold-hot`, `difffold-refine-hot` via cli_bench) joined
             with a separate omni_time run. The two were taken in different load windows, so ratios from
             this mode are secondary.

Inputs
  cli.csv        written by cli_bench; rows for the tools `difffold-hot` (top-down) and
                 `difffold-refine-hot` (top-down + refinement) carry dfold-cli's key=value line in
                 `stdout_line`: parse_*, convert_*, match_*, prod_* (and refine_* for refine) as med/min/max
                 over the in-process repetitions, in milliseconds. `prod` is the production path (certified
                 top-down diff with replay; for the refined tool also correspondence, flatten and refine),
                 timed first in each pass; `match` omits the replay and runs second on a warm cache, so
                 this script reports `prod`.
  omni_time.csv  parse_*, load_* (parse + AST metadata), diff_* as med/min/max over repetitions.
Views (milliseconds, per fixture, then summarised over fixtures)
  matching only      difffold `prod` (top-down: diff_checked; refined: diff_checked + correspondence +
                     flatten + refine) against OmniDiff `diff`.
  own work           each tool's preparation and matching with the shared tree-sitter parse taken out
                     (difffold convert + prod; OmniDiff load - parse + diff).
  with parse         difffold parse + convert + prod against OmniDiff load + diff (`load` includes the
                     AST metadata `diff_code` needs) and against OmniDiff parse + diff (tree-sitter only,
                     which omits the metadata and understates OmniDiff).
Each view is given for the per-fixture median and for the per-fixture minimum over repetitions (the
minimum is the least disturbed by other load on the machine). Ratios are OmniDiff / difffold per fixture.
"""
import argparse, csv, os, statistics as st

ap = argparse.ArgumentParser()
ap.add_argument("--cli")
ap.add_argument("--omni")
ap.add_argument("--paired")
ap.add_argument("--out", required=True)
a = ap.parse_args()

def kv(line):
    d = {}
    for tok in line.split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            d[k] = v
    return d

def f(d, k):
    return float(d[k])

rows = []
if a.paired:
    for r in csv.DictReader(open(a.paired)):
        row = {"fixture": r["fixture"], "nodes_before": int(r["nodes_before"]), "nodes_after": int(r["nodes_after"]), "reps": int(r["reps"])}
        for stat in ("med", "min"):
            row[f"parse_{stat}"] = f(r, f"td_parse_{stat}")
            row[f"convert_{stat}"] = f(r, f"td_convert_{stat}")
            row[f"td_match_{stat}"] = f(r, f"td_prod_{stat}")
            row[f"rf_match_{stat}"] = f(r, f"rf_prod_{stat}")
            row[f"rf_refine_{stat}"] = f(r, f"rf_refine_{stat}")
            row[f"omni_diff_{stat}"] = f(r, f"omni_diff_{stat}")
            row[f"omni_load_{stat}"] = f(r, f"omni_load_{stat}")
            row[f"omni_parse_{stat}"] = f(r, f"omni_parse_{stat}")
        row["loadavg1_cli"] = r["loadavg1"]
        rows.append(row)
else:
    hot = {"difffold-hot": {}, "difffold-refine-hot": {}}
    for r in csv.DictReader(open(a.cli)):
        if r["tool"] in hot and r["status"] == "ok":
            hot[r["tool"]][r["dataset"] + "/" + r["fixture"]] = (kv(r["stdout_line"]), r)
    omni = {r["dataset"] + "/" + r["fixture"]: r for r in csv.DictReader(open(a.omni))}
    for k in sorted(set(omni) & set(hot["difffold-hot"]) & set(hot["difffold-refine-hot"])):
        td, _ = hot["difffold-hot"][k]
        rf, rr = hot["difffold-refine-hot"][k]
        o = omni[k]
        row = {"fixture": k, "nodes_before": int(td["nodes_b"]), "nodes_after": int(td["nodes_a"]), "reps": int(td["reps"])}
        for stat in ("med", "min"):
            row[f"parse_{stat}"] = f(td, f"parse_{stat}")
            row[f"convert_{stat}"] = f(td, f"convert_{stat}")
            row[f"td_match_{stat}"] = f(td, f"prod_{stat}")
            row[f"rf_match_{stat}"] = f(rf, f"prod_{stat}")
            row[f"rf_refine_{stat}"] = f(rf, f"refine_{stat}")
            row[f"omni_diff_{stat}"] = float(o[f"diff_{stat}_ms"])
            row[f"omni_load_{stat}"] = float(o[f"load_{stat}_ms"])
            row[f"omni_parse_{stat}"] = float(o[f"parse_{stat}_ms"])
        row["loadavg1_cli"] = rr["loadavg1"]
        rows.append(row)
for row in rows:
    for stat in ("med", "min"):
        row[f"td_total_{stat}"] = row[f"parse_{stat}"] + row[f"convert_{stat}"] + row[f"td_match_{stat}"]
        row[f"rf_total_{stat}"] = row[f"parse_{stat}"] + row[f"convert_{stat}"] + row[f"rf_match_{stat}"]
        row[f"omni_total_{stat}"] = row[f"omni_load_{stat}"] + row[f"omni_diff_{stat}"]
        row[f"omni_total_parseonly_{stat}"] = row[f"omni_parse_{stat}"] + row[f"omni_diff_{stat}"]
        # Each tool's own work with the tree-sitter parse taken out of both: OmniDiff's AST metadata
        # (load minus parse) plus its diff; difffold's arena build plus matching.
        row[f"omni_own_{stat}"] = max(row[f"omni_load_{stat}"] - row[f"omni_parse_{stat}"], 0.0) + row[f"omni_diff_{stat}"]
        row[f"td_own_{stat}"] = row[f"convert_{stat}"] + row[f"td_match_{stat}"]
        row[f"rf_own_{stat}"] = row[f"convert_{stat}"] + row[f"rf_match_{stat}"]

def pct(v, p):
    v = sorted(v); i = (len(v) - 1) * p; lo = int(i); hi = min(lo + 1, len(v) - 1)
    return v[lo] + (v[hi] - v[lo]) * (i - lo)

os.makedirs(a.out, exist_ok=True)
with open(os.path.join(a.out, "stages.csv"), "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

def summ(name, num, den, stat):
    n = [r[num.format(stat)] for r in rows]; d = [r[den.format(stat)] for r in rows]
    ratios = [x / y for x, y in zip(n, d) if y > 0]
    return (f"| {name} | {sum(n):.0f} | {st.median(n):.3f} | {pct(n, .9):.3f} | {pct(n, .99):.3f} | "
            f"{sum(d):.0f} | {st.median(d):.3f} | {pct(d, .9):.3f} | {pct(d, .99):.3f} | "
            f"{sum(n) / sum(d):.1f} | {st.median(ratios):.1f} | {pct(ratios, .1):.1f} to {pct(ratios, .9):.1f} |")

out = [f"{len(rows)} fixtures (Java, Go, C), each timed {rows[0]['reps']} passes in process by both tools.",
       "OmniDiff / difffold ratios; 'total' columns are sums over fixtures in ms; quantiles are over fixtures.", ""]
for stat, title in (("med", "per-fixture median over the passes"), ("min", "per-fixture minimum over the passes")):
    out += [f"### {title}", "",
            "| view | OmniDiff total ms | median | p90 | p99 | difffold total ms | median | p90 | p99 | total ratio | median ratio | ratio p10 to p90 |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for name, num, den in (
        ("matching only, top-down core", "omni_diff_{}", "td_match_{}"),
        ("matching only, with refinement", "omni_diff_{}", "rf_match_{}"),
        ("with parse, top-down core (OmniDiff load incl. metadata)", "omni_total_{}", "td_total_{}"),
        ("with parse, with refinement (OmniDiff load incl. metadata)", "omni_total_{}", "rf_total_{}"),
        ("with parse, with refinement (OmniDiff tree-sitter parse only)", "omni_total_parseonly_{}", "rf_total_{}"),
        ("own work without the parse on either side, top-down core", "omni_own_{}", "td_own_{}"),
        ("own work without the parse on either side, with refinement", "omni_own_{}", "rf_own_{}"),
    ):
        out.append(summ(name, num, den, stat))
    out.append("")
rf = [r["rf_match_med"] / r["td_match_med"] for r in rows if r["td_match_med"] > 0]
out += ["### Refinement against the top-down core (matching only, medians)", "",
        f"refined / top-down per fixture: median {st.median(rf):.2f}, p90 {pct(rf, .9):.2f}, max {max(rf):.2f}; "
        f"totals {sum(r['rf_match_med'] for r in rows):.0f} ms against {sum(r['td_match_med'] for r in rows):.0f} ms.", ""]
# size buckets
out += ["### By tree size (nodes in the before tree), medians over fixtures, ms", "",
        "| nodes | fixtures | parse | convert | top-down | refined (total matching) | OmniDiff load | OmniDiff diff |", "|---|---|---|---|---|---|---|---|"]
for lo, hi in ((0, 1000), (1000, 5000), (5000, 20000), (20000, 10**9)):
    b = [r for r in rows if lo <= r["nodes_before"] < hi]
    if b:
        m = lambda k: st.median(r[k] for r in b)
        out.append(f"| {lo} to {hi if hi < 10**9 else 'max'} | {len(b)} | {m('parse_med'):.3f} | {m('convert_med'):.3f} | {m('td_match_med'):.3f} | {m('rf_match_med'):.3f} | {m('omni_load_med'):.3f} | {m('omni_diff_med'):.3f} |")
import math
def slope(key):
    pts = [(math.log(r["nodes_before"]), math.log(r[key])) for r in rows if r[key] > 0 and r["nodes_before"] > 1]
    mx = sum(x for x, _ in pts) / len(pts); my = sum(y for _, y in pts) / len(pts)
    return sum((x - mx) * (y - my) for x, y in pts) / sum((x - mx) ** 2 for x, _ in pts)
out += ["", "### Scaling: least-squares slope of log(time) against log(nodes in the before tree), per-fixture minima over the passes", "",
        "| stage | slope | meaning |", "|---|---|---|"]
for key, name in (("parse_min", "tree-sitter parse"), ("convert_min", "arena build"), ("td_match_min", "top-down (certified)"), ("rf_match_min", "top-down + refinement"), ("rf_refine_min", "refinement alone (paired/cli rows that report it)")):
    if key in rows[0]:
        out.append(f"| {name} | {slope(key):.2f} | 1.0 is linear |")
big = max(rows, key=lambda r: r["nodes_before"])
out += ["", f"Largest fixture: {big['fixture']} ({big['nodes_before']} / {big['nodes_after']} nodes): parse {big['parse_med']:.1f} ms, convert {big['convert_med']:.1f} ms, top-down {big['td_match_med']:.1f} ms, refined matching {big['rf_match_med']:.1f} ms, OmniDiff load {big['omni_load_med']:.1f} ms, OmniDiff diff {big['omni_diff_med']:.1f} ms."]
open(os.path.join(a.out, "SUMMARY.md"), "w").write("\n".join(out) + "\n")
print("\n".join(out))
