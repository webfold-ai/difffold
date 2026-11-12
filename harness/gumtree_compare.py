#!/usr/bin/env python3
"""GumTree (scored through tools/gumtree_eval) against difffold and OmniDiff on the same Java fixtures.

usage: gumtree_compare.py SCORED_DIR FIXTURES.csv OUT.md [--matchers a,b,c] [--generator java-jdt]

SCORED_DIR is the `scored/` directory written by tools/gumtree_eval/run_scoring.sh (it holds, per generator and matcher, a `raw`
and a `scoped` run of score_accuracy in which the `omnidiff` rows are GumTree's mapping). FIXTURES.csv is
results/accuracy/fixtures.csv (difffold and OmniDiff rows). Only fixtures GumTree parsed and all three tools scored are
compared. `raw` charges GumTree for every tree-sitter node its JDT tree does not contain (and is therefore not meaningful for
perfect-fixture rates); `scoped` judges only the nodes GumTree's tree can express and is lenient to GumTree.
"""
import argparse, csv, os

ap = argparse.ArgumentParser()
ap.add_argument("scored"); ap.add_argument("fixtures"); ap.add_argument("out")
ap.add_argument("--matchers", default="gumtree-simple,gumtree-classic,gumtree-hybrid-id")
ap.add_argument("--generator", default="java-jdt")
a = ap.parse_args()

def f1(tp, fp, fn):
    d = 2 * tp + fp + fn
    return 1.0 if d == 0 else 2 * tp / d

def stats(rows):
    pt = sum(int(r["pair_tp"]) for r in rows); pf = sum(int(r["pair_fp"]) for r in rows); pn = sum(int(r["pair_fn"]) for r in rows)
    st = sum(int(r["span_tp"]) for r in rows); sf = sum(int(r["span_fp"]) for r in rows); sn = sum(int(r["span_fn"]) for r in rows)
    perf = sum(r["perfect"] in ("1", "true", "True") for r in rows) / len(rows)
    return f1(pt, pf, pn), f1(st, sf, sn), perf

ours = {}
for r in csv.DictReader(open(a.fixtures)):
    ours.setdefault(r["tool"], {})[(r["dataset"], r["fixture"])] = r
out = []
for m in a.matchers.split(","):
    gt = {}
    p = os.path.join(a.scored, a.generator, m, "scoped", "fixtures.csv")
    if not os.path.exists(p):
        continue
    for r in csv.DictReader(open(p)):
        if r["tool"] == "omnidiff":
            gt[(r["dataset"], r["fixture"])] = r
    keys = sorted(set(gt) & set(ours["difffold"]) & set(ours["omnidiff"]))
    rows = [("GumTree " + m + " (scoped, lenient)", [gt[k] for k in keys]), ("difffold", [ours["difffold"][k] for k in keys]), ("OmniDiff", [ours["omnidiff"][k] for k in keys])]
    out += [f"### {m}: {len(keys)} Java fixtures scored by all three", "", "| tool | micro pair F1 | micro changed-span F1 | perfect fixtures |", "|---|---:|---:|---:|"]
    for name, rs in rows:
        pf, sf, perf = stats(rs)
        out.append(f"| {name} | {pf:.4f} | {sf:.4f} | {perf:.1%} |")
    out.append("")
txt = "\n".join(out)
open(a.out, "w").write(txt + "\n")
print(txt)
