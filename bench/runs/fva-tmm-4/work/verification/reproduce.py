"""Supplemental NumPy transcription, not a proof about the Python interpreter.

SciPy/sklearn are unavailable here. rankdata's default average-rank rule is
implemented directly; the equations and expression order follow the vendored TMM.
No artifact is overwritten.
"""
from pathlib import Path
import numpy as np


def rankdata(xs):
    return np.array([1 + np.count_nonzero(xs < x)
                     + (np.count_nonzero(xs == x) - 1) / 2 for x in xs])


x = np.loadtxt("counts.tsv", delimiter="\t", ndmin=2).T
x = x[:, x.sum(axis=0) > 0]
lib = x.sum(axis=1)
uq = np.quantile(x, .75, axis=1) / lib
ref_idx = np.argmin(np.abs(uq - uq.mean()))
ref = x[ref_idx].copy()
lib_ref = ref.sum()
x[x == 0] = np.nan
ref[ref == 0] = np.nan
r = x / lib[:, np.newaxis]
r_ref = ref / lib_ref
m = np.log2(r / r_ref)
a = np.log2(r * r_ref) / 2
w = (1 - r) / x + (1 - r_ref) / ref
f, sizes = [], []
for mm, aa, ww in zip(m, a, w):
    finite = np.isfinite(mm) & np.isfinite(aa)
    mm, aa, ww = mm[finite], aa[finite], ww[finite]
    n = len(mm)
    ml, al = np.floor(n * .3) + 1, np.floor(n * .05) + 1
    rm, ra = rankdata(mm), rankdata(aa)
    keep = (rm >= ml) & (rm <= n - ml + 1) & (ra >= al) & (ra <= n - al + 1)
    sizes.append(int(keep.sum()))
    f.append(np.nansum(keep * mm / ww) / np.nansum(keep / ww))
raw = np.power(2, np.array(f))
result = raw / np.exp(np.mean(np.log(raw)))
shipped = np.loadtxt("rnanorm-factors.txt")
assert np.max(np.abs(result - shipped)) < 1e-14
print("RNAnorm NumPy transcription: all errors < 1e-14")
print("reference (one based):", ref_idx + 1)
print("retained genes:", sizes)
print("maximum error:", np.max(np.abs(result - shipped)))
