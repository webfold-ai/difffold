#!/usr/bin/env python3
"""Select fixture pairs and stage them with real extensions (the corpus files end in `.test`).

usage: select_fixtures.py --diffs DIR --baseline baseline.csv --work DIR --out manifest.tsv
         [--langs java,go,c | --all-langs] [--sample N] [--slowest N] [--seed S]
         [--include-skipped] [--datasets a,b]

--slowest N takes the N fixtures with the largest recorded OmniDiff `elapsed_ms`.
--sample N takes N more drawn at random (seeded) from the rest. With neither, all are taken.
Exclusions are written to <out>.exclusions.csv with a reason; nothing is dropped silently.
"""
import argparse, csv, os, random, shutil, sys

p = argparse.ArgumentParser()
p.add_argument("--diffs", required=True)
p.add_argument("--baseline", required=True)
p.add_argument("--work", required=True)
p.add_argument("--out", required=True)
p.add_argument("--langs", default="java,go,c")
p.add_argument("--all-langs", action="store_true")
p.add_argument("--sample", type=int, default=0)
p.add_argument("--slowest", type=int, default=0)
p.add_argument("--seed", type=int, default=1)
p.add_argument("--include-skipped", action="store_true")
p.add_argument("--datasets", default="")
a = p.parse_args()

langs = None if a.all_langs else set(a.langs.split(","))
dsets = set(a.datasets.split(",")) - {""}
rows, excl = [], []
for r in csv.DictReader(open(a.baseline)):
    lang = r["language"].lower()
    fid = f'{r["repository"]}/{r["path"]}'
    if langs is not None and lang not in langs:
        continue  # out of scope by language, not an exclusion of a requested fixture
    if dsets and r["repository"] not in dsets:
        continue
    if r["status"] != "ok" and not (a.include_skipped and r["status"] == "skipped_too_large"):
        excl.append((fid, lang, "omnidiff_status_" + r["status"]))
        continue
    d = os.path.join(a.diffs, r["repository"], r["path"])
    try:
        names = os.listdir(d)
    except OSError:
        excl.append((fid, lang, "missing_dir")); continue
    b = next((n for n in names if n.startswith("before.")), None)
    af = next((n for n in names if n.startswith("after.")), None)
    if not b or not af:
        excl.append((fid, lang, "missing_before_or_after")); continue
    ext = b.split(".")[1]
    rows.append(dict(dataset=r["repository"], fixture=r["path"], lang=lang, ext=ext,
                     src_b=os.path.join(d, b), src_a=os.path.join(d, af),
                     bytes_b=r["bytes_before"], bytes_a=r["bytes_after"], omni_ms=r["elapsed_ms"]))
rows.sort(key=lambda x: (x["dataset"], x["fixture"]))
if a.slowest or a.sample:
    key = lambda x: float(x["omni_ms"]) if x["omni_ms"] else -1.0
    slow = sorted(rows, key=key, reverse=True)[: a.slowest]
    ids = {id(x) for x in slow}
    rest = [x for x in rows if id(x) not in ids]
    pick = random.Random(a.seed).sample(rest, min(a.sample, len(rest)))
    chosen = slow + pick
    chosen_ids = {id(x) for x in chosen}
    for x in rows:
        if id(x) not in chosen_ids:
            excl.append((f'{x["dataset"]}/{x["fixture"]}', x["lang"], "not_sampled"))
    rows = sorted(chosen, key=lambda x: (x["dataset"], x["fixture"]))

os.makedirs(a.work, exist_ok=True)
with open(a.out, "w") as f:
    f.write("id\tdataset\tfixture\tlang\text\tbefore\tafter\tbytes_b\tbytes_a\tomni_ms\n")
    for x in rows:
        i = f'{x["dataset"]}__{x["fixture"]}'
        d = os.path.join(a.work, i)
        os.makedirs(d, exist_ok=True)
        pb, pa = os.path.join(d, "before." + x["ext"]), os.path.join(d, "after." + x["ext"])
        shutil.copyfile(x["src_b"], pb); shutil.copyfile(x["src_a"], pa)
        f.write("\t".join([i, x["dataset"], x["fixture"], x["lang"], x["ext"], pb, pa,
                           x["bytes_b"], x["bytes_a"], x["omni_ms"]]) + "\n")
with open(a.out + ".exclusions.csv", "w") as f:
    w = csv.writer(f); w.writerow(["fixture", "lang", "reason"]); w.writerows(excl)
print(f"selected {len(rows)} fixtures, {len(excl)} excluded -> {a.out}", file=sys.stderr)
