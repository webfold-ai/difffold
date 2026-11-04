#!/usr/bin/env python3
"""Summarise a cli_bench CSV: per-tool wall time, tail latency, failures, pairwise ratios vs difffold.

usage: summarize.py --cli cli.csv --manifest m.tsv --machine machine.txt --out SUMMARY.md
         [--ratios ratios.csv] [--views views.csv]

Only fixtures on which a tool finished with status ok are counted for that tool. The ratio table uses
the intersection of fixtures that both tools completed, so a tool that times out is not rewarded
or punished by dropping its slow cases silently: its failure count is reported next to it.
"""
import argparse, csv, statistics as st, collections

p = argparse.ArgumentParser()
for k in ("cli", "manifest", "machine", "out", "ratios", "views"):
    p.add_argument("--" + k, default=None)
a = p.parse_args()

rows = list(csv.DictReader(open(a.cli)))
by = collections.defaultdict(dict)
obj = {}
fails = collections.Counter()
fb = collections.Counter()
for r in rows:
    t, f = r["tool"], r["dataset"] + "/" + r["fixture"]
    obj[t] = r["objective"]
    if r["status"] == "ok":
        by[t][f] = float(r["wall_ms_med"])
        if r["fallback"] in ("1", "true", "True"):
            fb[t] += 1
    else:
        fails[t] += 1


def pct(v, q):
    v = sorted(v)
    return v[min(len(v) - 1, int(q * len(v)))]


out = ["# Comparison summary", "", "```", open(a.machine).read().strip(), "```", ""]
out += ["## Wall time per tool (ms, median of reps, process start to exit)", "",
        "| tool | objective | ok | failed | fallback | total | median | p90 | p99 | max |", "|---|---|---|---|---|---|---|---|---|---|"]
for t in sorted(obj):
    v = list(by[t].values())
    if not v:
        out.append(f"| {t} | {obj[t]} | 0 | {fails[t]} | {fb[t]} | n/a | n/a | n/a | n/a | n/a |")
        continue
    out.append(f"| {t} | {obj[t]} | {len(v)} | {fails[t]} | {fb[t]} | {sum(v):.0f} | {st.median(v):.1f} | {pct(v,.9):.1f} | {pct(v,.99):.1f} | {max(v):.1f} |")

base = "difffold"
ratio_rows = []
if base in by:
    out += ["", f"## Ratio to {base} (tool time / {base} time, fixtures both completed)", "",
            "| tool | n | median | min | max | total tool / total difffold |", "|---|---|---|---|---|---|"]
    for t in sorted(by):
        if t == base:
            continue
        com = [f for f in by[t] if f in by[base]]
        if not com:
            continue
        rs = [by[t][f] / max(by[base][f], 1e-3) for f in com]
        tot = sum(by[t][f] for f in com) / sum(by[base][f] for f in com)
        out.append(f"| {t} | {len(com)} | {st.median(rs):.1f} | {min(rs):.2f} | {max(rs):.1f} | {tot:.1f} |")
        ratio_rows += [(t, f, by[t][f], by[base][f]) for f in com]
open(a.out, "w").write("\n".join(out) + "\n")
if a.ratios:
    with open(a.ratios, "w") as g:
        g.write("tool,fixture,tool_ms,difffold_ms\n")
        for r in ratio_rows:
            g.write("%s,%s,%.3f,%.3f\n" % r)
