#!/usr/bin/env python3
"""Interleaved, paired in-process timing of difffold and OmniDiff, fixture by fixture.

usage: paired_speed.py --manifest M.tsv --diffs DIFFS --dfold-cli BIN --omni-time BIN --out out.csv
                       [--n 100] [--reps 10] [--seed 1]

For each of `n` fixtures drawn (seeded) from the manifest, the three measurements
  dfold-cli --algo difffold        --reps R   (top-down)
  dfold-cli --algo difffold-refine --reps R   (top-down + refinement)
  omni_time  DIFFS out R fixture.txt          (OmniDiff parse, load, diff)
run back to back in a shuffled order, so the machine load seen by one is, to first order, the load seen
by the others. Each measurement reports per-stage median/min/max over R in-process passes. The 1-minute
load average is recorded before every fixture. This replaces nothing in the cold-process harness; it
answers the question the cold-process timings cannot, which is how the three compare on the same
fixture under the same load.
"""
import argparse, csv, os, random, subprocess, sys, tempfile

ap = argparse.ArgumentParser()
ap.add_argument("--manifest", required=True); ap.add_argument("--diffs", required=True)
ap.add_argument("--dfold-cli", required=True); ap.add_argument("--omni-time", required=True)
ap.add_argument("--out", required=True); ap.add_argument("--n", type=int, default=100)
ap.add_argument("--reps", type=int, default=10); ap.add_argument("--seed", type=int, default=1)
a = ap.parse_args()

rows = list(csv.DictReader(open(a.manifest), delimiter="\t"))
rng = random.Random(a.seed)
rng.shuffle(rows)
rows = rows[: a.n]

def kv(line):
    return dict(t.split("=", 1) for t in line.split() if "=" in t)

fields = ["fixture", "order", "loadavg1", "nodes_before", "nodes_after", "reps"]
for pre in ("td", "rf"):
    for st in ("parse", "convert", "match", "prod", "refine"):
        for k in ("med", "min", "max"):
            fields.append(f"{pre}_{st}_{k}")
for st in ("parse", "load", "diff"):
    for k in ("med", "min", "max"):
        fields.append(f"omni_{st}_{k}")
with open(a.out, "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=fields); w.writeheader()
    for i, r in enumerate(rows):
        key = f"{r['dataset']}/{r['fixture']}"
        order = ["td", "rf", "omni"]; rng.shuffle(order)
        out = {"fixture": key, "order": "".join(o[0] for o in order), "loadavg1": open("/proc/loadavg").read().split()[0], "reps": a.reps}
        for tool in order:
            if tool in ("td", "rf"):
                algo = "difffold" if tool == "td" else "difffold-refine"
                p = subprocess.run(["nice", "-n", "10", a.dfold_cli, "--algo", algo, "--reps", str(a.reps), r["before"], r["after"]], capture_output=True, text=True)
                d = kv(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else {}
                if d.get("status") != "ok":
                    out = None; break
                out["nodes_before"], out["nodes_after"] = d["nodes_b"], d["nodes_a"]
                for st in ("parse", "convert", "match", "prod", "refine"):
                    for k in ("med", "min", "max"):
                        if f"{st}_{k}" in d:
                            out[f"{tool}_{st}_{k}"] = d[f"{st}_{k}"]
            else:
                with tempfile.TemporaryDirectory() as t:
                    lst = os.path.join(t, "f.txt"); open(lst, "w").write(key + "\n")
                    csvp = os.path.join(t, "o.csv")
                    subprocess.run(["nice", "-n", "10", a.omni_time, a.diffs, csvp, str(a.reps), lst], capture_output=True, text=True)
                    rr = list(csv.DictReader(open(csvp))) if os.path.exists(csvp) else []
                if not rr:
                    out = None; break
                for st in ("parse", "load", "diff"):
                    for k in ("med", "min", "max"):
                        out[f"omni_{st}_{k}"] = rr[0][f"{st}_{k}_ms"]
        if out:
            w.writerow({k: out.get(k, "") for k in fields}); fh.flush()
        print(f"{i + 1}/{len(rows)} {key}", file=sys.stderr)
