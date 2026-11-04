#!/usr/bin/env python3
"""Independent minimality oracle: rapidfuzz's bit-parallel Indel distance on line sequences.

usage: oracle_rapidfuzz.py <diffs-dir> <lines.csv> [max_lines]
Indel distance = minimum inserted + deleted elements, exactly our objective. Test code only.
"""
import csv, os, sys
from rapidfuzz.distance import Indel

diffs, csv_path = sys.argv[1], sys.argv[2]
cap = int(sys.argv[3]) if len(sys.argv) > 3 else 30000
ours = {}
for r in csv.DictReader(open(csv_path)):
    if r["algo"] == "difffold-lines":
        ours[(r["dataset"], r["fixture"])] = int(r["cost"])
checked = bad = skipped = 0
for (ds, fx), cost in sorted(ours.items()):
    d = os.path.join(diffs, ds, fx)
    try:
        b = next(f for f in os.listdir(d) if f.startswith("before."))
        a = next(f for f in os.listdir(d) if f.startswith("after."))
    except StopIteration:
        continue
    tb = open(os.path.join(d, b), "rb").read().splitlines(keepends=True)
    ta = open(os.path.join(d, a), "rb").read().splitlines(keepends=True)
    # bytes.splitlines splits on more than \n; keep only \n-terminated splitting to match ours.
    def split(t):
        out, s = [], 0
        for i, c in enumerate(t):
            if c == 10:
                out.append(t[s:i + 1]); s = i + 1
        if s < len(t): out.append(t[s:])
        return out
    tb = split(open(os.path.join(d, b), "rb").read()); ta = split(open(os.path.join(d, a), "rb").read())
    if len(tb) + len(ta) > cap:
        skipped += 1; continue
    ref = Indel.distance(tb, ta)
    checked += 1
    if ref != cost:
        bad += 1; print("MISMATCH", ds, fx, "ours", cost, "rapidfuzz", ref)
print(f"checked {checked}, mismatches {bad}, skipped (too large) {skipped}")
