#!/usr/bin/env python3
"""Aggregates score_accuracy fixtures.csv (the 'omnidiff' rows hold the externally supplied mapping, here
GumTree/RefactoringMiner) and Eval times.tsv into per-(generator, matcher) summaries.
usage: aggregate.py <work-dir> <eval-out-dir> <results-dir> <fixture-subset.tsv|-> """
import csv, os, sys, statistics as st

W, O, R, SUBSET = sys.argv[1:5]
subset = None
if SUBSET != '-':
    subset = {l.split('\t')[0] for l in open(SUBSET) if l.strip()}

def f1(p, r):
    return 0.0 if p + r == 0 else 2 * p * r / (p + r)

def prf(tp, fp, fn):
    p = 1.0 if tp + fp == 0 else tp / (tp + fp)
    r = 1.0 if tp + fn == 0 else tp / (tp + fn)
    return p, r, f1(p, r)

NONTRIVIAL = None
def nontrivial(gen, m):
    # A fixture is non-trivial when the ground truth records at least one changed pair, deletion, insertion or group.
    global NONTRIVIAL
    if NONTRIVIAL is None:
        NONTRIVIAL = {}
        p = f'{W}/scored/{gen}/{m}/raw/taxonomy.csv'
        if os.path.exists(p):
            for r in csv.DictReader(open(p)):
                NONTRIVIAL[f"{r['dataset']}__{r['fixture']}"] = int(r['gt_changed']) + int(r['gt_deleted']) + int(r['gt_inserted']) + int(r['groups']) > 0
    return NONTRIVIAL

def load(gen, m, variant):
    d = f'{W}/scored/{gen}/{m}/{variant}'
    fc = f'{d}/fixtures.csv'
    if not os.path.exists(fc):
        return {}
    granted = {}
    if variant == 'scoped':
        for r in csv.DictReader(open(f'{W}/scored/{gen}/{m}/raw-maps/_stats.tsv'), delimiter='\t'):
            granted[r['key']] = int(r['granted_pairs'])
    rows = {}
    for r in csv.DictReader(open(fc)):
        if r['tool'] != 'omnidiff':
            continue
        key = f"{r['dataset']}__{r['fixture']}"
        if subset is not None and key not in subset:
            continue
        g = granted.get(key, 0)
        dec = int(r['decisions']) - g
        rows[key] = dict(
            dec=dec, fails=int(r['mismatches']), vfails=int(r['visible_mismatches']),
            tp=int(r['pair_tp']) - g, fp=int(r['pair_fp']), fn=int(r['pair_fn']),
            stp=int(r['span_tp']), sfp=int(r['span_fp']), sfn=int(r['span_fn']),
            perfect=r['perfect'] in ('1', 'true', 'True'), strict=r['strict_perfect'] in ('1', 'true', 'True'),
            near=r['near_perfect'] in ('1', 'true', 'True'), nontriv=nontrivial(gen, m).get(key, True), nb=int(r['nodes_before']), na=int(r['nodes_after']), granted=g)
    return rows

def summarize(rows):
    n = len(rows)
    if n == 0:
        return None
    tp = sum(r['tp'] for r in rows.values()); fp = sum(r['fp'] for r in rows.values()); fn = sum(r['fn'] for r in rows.values())
    p, r, f = prf(tp, fp, fn)
    dec = sum(r['dec'] for r in rows.values()); fl = sum(r['fails'] for r in rows.values())
    stp = sum(r['stp'] for r in rows.values()); sfp = sum(r['sfp'] for r in rows.values()); sfn = sum(r['sfn'] for r in rows.values())
    sp, sr, sf = prf(stp, sfp, sfn)
    mp = [prf(x['tp'], x['fp'], x['fn']) for x in rows.values()]
    msp = [prf(x['stp'], x['sfp'], x['sfn']) for x in rows.values()]
    nt = [x for x in rows.values() if x['nontriv']]
    return dict(n=n, n_nontrivial=len(nt), perfect_nontrivial=(sum(x['perfect'] for x in nt) / len(nt)) if nt else float('nan'), perfect=sum(x['perfect'] for x in rows.values()) / n, near=sum(x['near'] for x in rows.values()) / n,
                strict=sum(x['strict'] for x in rows.values()) / n,
                acc=1 - fl / dec if dec else 1.0, P=p, R=r, F1=f,
                mP=st.mean(x[0] for x in mp), mR=st.mean(x[1] for x in mp), mF1=st.mean(x[2] for x in mp),
                sP=sp, sR=sr, sF1=sf, msF1=st.mean(x[2] for x in msp))

def times(gen):
    t = {}
    p = f'{O}/{gen}/times.tsv'
    if not os.path.exists(p):
        return t
    for r in csv.DictReader(open(p), delimiter='\t'):
        t[(r['key'], r['matcher'])] = r
    return t

os.makedirs(R, exist_ok=True)
out_rows = []
per_fx = []
for gen in sorted(os.listdir(f'{W}/scored')) if os.path.isdir(f'{W}/scored') else []:
    tt = times(gen)
    for m in sorted(os.listdir(f'{W}/scored/{gen}')):
        for variant in ('raw', 'scoped'):
            rows = load(gen, m, variant)
            s = summarize(rows)
            if s is None:
                continue
            # runtimes over the scored fixtures (microseconds -> ms)
            ms_ = [int(tt[(k, m)]['match_us']) / 1000 for k in rows if (k, m) in tt and tt[(k, m)]['status'] == 'ok']
            ps_ = [(int(tt[(k, m)]['parse_src_us']) + int(tt[(k, m)]['parse_dst_us'])) / 1000 for k in rows if (k, m) in tt and tt[(k, m)]['status'] == 'ok']
            nt = sum(1 for k in rows if (k, m) in tt and tt[(k, m)]['status'] != 'ok')
            s.update(gen=gen, matcher=m, variant=variant,
                     match_ms_median=st.median(ms_) if ms_ else float('nan'), match_ms_mean=st.mean(ms_) if ms_ else float('nan'),
                     match_ms_p90=sorted(ms_)[int(0.9 * (len(ms_) - 1))] if ms_ else float('nan'), match_ms_max=max(ms_) if ms_ else float('nan'),
                     match_s_total=sum(ms_) / 1000 if ms_ else float('nan'), parse_ms_median=st.median(ps_) if ps_ else float('nan'),
                     not_ok=nt)
            out_rows.append(s)
            if variant == 'scoped':
                for k, x in rows.items():
                    tm = tt.get((k, m), {})
                    p, r, f = prf(x['tp'], x['fp'], x['fn'])
                    per_fx.append(dict(gen=gen, matcher=m, key=k, nb=x['nb'], na=x['na'], perfect=int(x['perfect']), pair_P=round(p, 4), pair_R=round(r, 4), pair_F1=round(f, 4),
                                       decisions_judged=x['dec'], mismatches=x['fails'], match_us=tm.get('match_us', ''), parse_us=(int(tm['parse_src_us']) + int(tm['parse_dst_us'])) if tm else ''))
cols = ['gen', 'matcher', 'variant', 'n', 'n_nontrivial', 'perfect_nontrivial', 'perfect', 'near', 'strict', 'acc', 'P', 'R', 'F1', 'mP', 'mR', 'mF1', 'sP', 'sR', 'sF1', 'msF1',
        'match_ms_median', 'match_ms_mean', 'match_ms_p90', 'match_ms_max', 'match_s_total', 'parse_ms_median', 'not_ok']
tag = 'all' if subset is None else 'subset'
with open(f'{R}/gumtree-summary-{tag}.csv', 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=cols); w.writeheader()
    for s in out_rows:
        w.writerow({c: (round(s[c], 4) if isinstance(s[c], float) else s[c]) for c in cols})
if subset is None:
    with open(f'{R}/gumtree-per-fixture.csv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=list(per_fx[0].keys()) if per_fx else ['gen']); w.writeheader(); [w.writerow(x) for x in per_fx]
print(f'{len(out_rows)} summary rows -> {R}/gumtree-summary-{tag}.csv')
