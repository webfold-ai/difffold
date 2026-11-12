#!/usr/bin/env python3
"""Summarises a DiffBenchmark Defects4J run (tools/diffbenchmark_adapter) from its records-NO_FILTER.csv.

usage: dfb_summary.py records-NO_FILTER.csv [--n 10000] [--seed 1] [--out SUMMARY.md]

Per tool, over the files every listed tool completed: raw true positives, false positives and false
negatives (abstract mappings plus program elements, no adjustment for the mappings all tools share),
raw precision, recall and F1, and the files with FP = FN = 0 ("perfect"). A percentile bootstrap over
files (paired: the same resample for every tool) gives intervals for F1 and for the F1 difference of
each tool to the last tool in the file order given by --ref (default DFT_RF). The adjusted figures the
benchmark itself prints depend on which tools are in the run and are not recomputed here.
"""
import argparse, csv, random

ap = argparse.ArgumentParser()
ap.add_argument("records")
ap.add_argument("--n", type=int, default=10000)
ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--ref", default="DFT_RF")
ap.add_argument("--out", default="")
a = ap.parse_args()

by = {}
for r in csv.DictReader(open(a.records)):
    by.setdefault(r["tool"], {})[(r["bug"], r["file"])] = r
tools = [t for t in ("RMD", "GTG", "GTS", "DFT_TD", "DFT_TED", "DFT_RF") if t in by]
keys = sorted(set.intersection(*[set(by[t]) for t in tools]))

def counts(t, ks):
    tp = fp = fn = perf = 0
    for k in ks:
        r = by[t][k]
        tp += int(r["mapping_TP_raw"]) + int(r["element_TP_raw"])
        f1_ = int(r["mapping_FP"]) + int(r["element_FP"]); f2_ = int(r["mapping_FN"]) + int(r["element_FN"])
        fp += f1_; fn += f2_
        perf += (f1_ == 0 and f2_ == 0)
    return tp, fp, fn, perf

def f1(tp, fp, fn):
    return 2 * tp / (2 * tp + fp + fn) if tp + fp + fn else 1.0

def pct(v, p):
    v = sorted(v); i = (len(v) - 1) * p; lo = int(i); hi = min(lo + 1, len(v) - 1)
    return v[lo] + (v[hi] - v[lo]) * (i - lo)

rng = random.Random(a.seed)
point = {t: counts(t, keys) for t in tools}
samples = {t: [] for t in tools}
for _ in range(a.n):
    ks = [keys[rng.randrange(len(keys))] for _ in keys]
    for t in tools:
        c = counts(t, ks)
        samples[t].append(f1(*c[:3]))
out = [f"{len(keys)} oracle files completed by all of {', '.join(tools)}; percentile bootstrap over files, {a.n} resamples, seed {a.seed}.", "",
       "| tool | TP raw | FP | FN | precision (raw) | recall (raw) | F1 (raw) [95% interval] | perfect files |", "|---|---|---|---|---|---|---|---|"]
for t in tools:
    tp, fp, fn, perf = point[t]
    out.append(f"| {t} | {tp} | {fp} | {fn} | {tp / (tp + fp):.4f} | {tp / (tp + fn):.4f} | {f1(tp, fp, fn):.4f} [{pct(samples[t], .025):.4f}, {pct(samples[t], .975):.4f}] | {perf} ({perf / len(keys):.1%}) |")
if a.ref in tools:
    out += ["", f"Paired F1 difference of {a.ref} to each other tool (same resamples):", "", "| tool | difference | 95% interval |", "|---|---|---|"]
    for t in tools:
        if t != a.ref:
            d = [x - y for x, y in zip(samples[a.ref], samples[t])]
            diff = f1(*point[a.ref][:3]) - f1(*point[t][:3])
            out.append(f"| {t} | {diff:+.5f} | [{pct(d, .025):+.5f}, {pct(d, .975):+.5f}] |")
txt = "\n".join(out) + "\n"
if a.out:
    open(a.out, "w").write(txt)
print(txt)
