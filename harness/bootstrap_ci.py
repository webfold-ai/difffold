#!/usr/bin/env python3
"""Percentile bootstrap over fixtures for the accuracy tables.

usage: bootstrap_ci.py FIXTURES.csv [--tools difffold,omnidiff] [--n 10000] [--seed 1] [--out ci.md]
       [--baseline OTHER_FIXTURES.csv]   # a second fixtures.csv, compared with the first for the 'difffold' tool

FIXTURES.csv is the `fixtures.csv` written by `score_accuracy` (one row per fixture and tool).
Each replicate resamples fixtures with replacement and recomputes the micro pair F1, the micro
changed-span F1 and the fraction of perfect fixtures; the 2.5th and 97.5th percentiles are the interval.
With two tools present the paired difference (same resample) is reported as well. Fixtures, not
decisions, are the resampling unit because decisions within a fixture are not independent.
"""
import argparse, csv, random, sys

ap = argparse.ArgumentParser()
ap.add_argument("fixtures")
ap.add_argument("--tools", default="difffold,omnidiff")
ap.add_argument("--n", type=int, default=10000)
ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--out", default="")
ap.add_argument("--baseline", default="")
a = ap.parse_args()

def load(path):
    by = {}
    for r in csv.DictReader(open(path)):
        by.setdefault(r["tool"], {})[(r["dataset"], r["fixture"])] = r
    return by

def f1(tp, fp, fn):
    d = 2 * tp + fp + fn
    return 1.0 if d == 0 else 2 * tp / d

def stats(rows):
    pt = sum(int(r["pair_tp"]) for r in rows); pf = sum(int(r["pair_fp"]) for r in rows); pn = sum(int(r["pair_fn"]) for r in rows)
    st = sum(int(r["span_tp"]) for r in rows); sf = sum(int(r["span_fp"]) for r in rows); sn = sum(int(r["span_fn"]) for r in rows)
    perf = sum(int(r["perfect"]) for r in rows) / len(rows)
    return f1(pt, pf, pn), f1(st, sf, sn), perf

def pct(v, p):
    v = sorted(v); k = (len(v) - 1) * p; lo = int(k); hi = min(lo + 1, len(v) - 1)
    return v[lo] + (v[hi] - v[lo]) * (k - lo)

by = load(a.fixtures)
sets = {t: by[t] for t in a.tools.split(",") if t in by}
if a.baseline:
    sets["difffold-baseline"] = load(a.baseline)["difffold"]
keys = sorted(set.intersection(*[set(s) for s in sets.values()]))
names = list(sets)
rng = random.Random(a.seed)
point = {t: stats([sets[t][k] for k in keys]) for t in names}
reps = {t: [] for t in names}
diff = []
for _ in range(a.n):
    idx = [keys[rng.randrange(len(keys))] for _ in keys]
    cur = {t: stats([sets[t][k] for k in idx]) for t in names}
    for t in names:
        reps[t].append(cur[t])
    if len(names) >= 2:
        diff.append(tuple(cur[names[0]][i] - cur[names[1]][i] for i in range(3)))
lines = [f"Percentile bootstrap, {a.n} resamples of {len(keys)} fixtures, seed {a.seed}. 95% interval.", "",
         "| tool | micro pair F1 | micro changed-span F1 | perfect fixtures |", "|---|---|---|---|"]
for t in names:
    cells = []
    for i in range(3):
        v = [r[i] for r in reps[t]]
        cells.append(f"{point[t][i]:.4f} [{pct(v, .025):.4f}, {pct(v, .975):.4f}]")
    lines.append(f"| {t} | " + " | ".join(cells) + " |")
if diff:
    lines += ["", f"Paired difference {names[0]} minus {names[1]} (same resamples):", "", "| metric | difference |", "|---|---|"]
    for i, m in enumerate(["micro pair F1", "micro changed-span F1", "perfect fixtures"]):
        v = [d[i] for d in diff]
        lines.append(f"| {m} | {point[names[0]][i] - point[names[1]][i]:+.4f} [{pct(v, .025):+.4f}, {pct(v, .975):+.4f}] |")
out = "\n".join(lines) + "\n"
if a.out:
    open(a.out, "w").write(out)
print(out)
