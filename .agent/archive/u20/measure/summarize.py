"""U20 M2/M3/r2 summaries: python3 -I summarize.py <measure dir> → stdout tables.

M2 (m2.tsv, r2-m2.tsv): per arm, Σ of module medians and Σ of module minima (contention-robust)
over runs 1–3 (run 0 = warm-up), the run-total
spread (min–max of Σ per run), the slowest module median, max RSS; rc ≠ 0 rows counted.
M3 (m3.tsv, r2.tsv): export bytes − baseline, export time; per tag × checker the replay median,
min–max, max RSS, rc set.
"""
import csv
import statistics as st
import sys
from collections import defaultdict
from pathlib import Path

d = Path(sys.argv[1])


def rows(name):
    p = d / name
    if not p.exists():
        return []
    with p.open() as f:
        return list(csv.DictReader(f, delimiter="\t"))


def m2(name):
    r = rows(name)
    if not r:
        return
    print(f"## {name}")
    per = defaultdict(list)  # (arm, module) -> walls of runs 1..3
    runsum = defaultdict(float)  # (arm, run) -> Σ wall
    rss = defaultdict(int)
    bad = defaultdict(int)
    for x in r:
        a, run, w = x["arm"], int(x["run"]), x["wall_s"]
        if x["rc"] != "0" or not w:
            bad[a] += 1
            continue
        w = float(w)
        rss[a] = max(rss[a], int(x["maxrss_kib"]))
        if run >= 1:
            per[(a, x["module"])].append(w)
            runsum[(a, run)] += w
    for a in sorted({k[0] for k in per}):
        meds = {m: st.median(v) for (aa, m), v in per.items() if aa == a}
        mins = {m: min(v) for (aa, m), v in per.items() if aa == a}
        n = {len(v) for (aa, _), v in per.items() if aa == a}
        sums = [runsum[(a, k)] for k in (1, 2, 3) if (a, k) in runsum]
        top = max(meds, key=lambda m: meds[m])
        print(f"{a}: modules={len(meds)} runs/module={sorted(n)} Σmedian={sum(meds.values()):.1f}s "
              f"Σmin={sum(mins.values()):.1f}s Σrun min–max={min(sums):.1f}–{max(sums):.1f}s "
              f"slowest={top.split('.')[-1]} "
              f"{meds[top]:.1f}s maxRSS={rss[a] / 1048576:.2f}GiB bad={bad[a]}")


def m3(name):
    r = rows(name)
    if not r:
        return
    print(f"## {name}")
    base = None
    for x in r:
        if x["tag"] == "baseline" and x["checker"] == "export":
            base = int(x["bytes"])
    rep = defaultdict(list)
    rss = defaultdict(int)
    rcs = defaultdict(set)
    for x in r:
        if x["checker"] == "export":
            b = int(x["bytes"])
            delta = f" Δbaseline={b - base:,}" if base is not None and x["tag"] != "baseline" else ""
            print(f"export {x['tag']}: {b:,} B{delta} {x['wall_s']}s rc={x['rc']}")
            continue
        k = (x["tag"], x["checker"])
        rcs[k].add(x["rc"])
        if x["wall_s"]:
            rep[k].append(float(x["wall_s"]))
        if x["maxrss_kib"]:
            rss[k] = max(rss[k], int(x["maxrss_kib"]))
    for k in sorted(rep):
        v = rep[k]
        print(f"replay {k[0]} {k[1]}: median={st.median(v):.1f}s min–max={min(v):.1f}–{max(v):.1f}s "
              f"n={len(v)} maxRSS={rss[k] / 1048576:.2f}GiB rc={sorted(rcs[k])}")


m2("m2.tsv")
m2("r2-m2.tsv")
m3("m3.tsv")
m3("r2.tsv")
