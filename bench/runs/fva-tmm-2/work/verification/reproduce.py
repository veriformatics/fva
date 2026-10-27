#!/usr/bin/env python3
"""Diagnostic NumPy transcription, NOT part of the formal proof or trust base.

Preserves the two source files' orders of evaluation for M and A. It does not
execute R, scipy, sklearn or the RNAnorm package and must not be reported as such.
"""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np

root = Path(__file__).resolve().parent.parent
x = np.loadtxt(root / 'counts.tsv', dtype=np.float64)
x = x[np.any(x != 0, axis=1)]
libs = x.sum(axis=0)
uq = np.quantile(x, 0.75, axis=0) / libs
ref = int(np.argmin(abs(uq - uq.mean())))


def ranks(values):
    return np.array([1 + np.sum(values < v) + (np.sum(values == v) - 1) / 2
                     for v in values])


results = {'numpy': np.__version__, 'reference_1based': ref + 1}
for mode, filename in [('edge_order', 'edger-factors.txt'),
                       ('rna_order', 'rnanorm-factors.txt')]:
    raw, kept_counts = [], []
    for j in range(7):
        z = x[(x[:, j] > 0) & (x[:, ref] > 0)]
        o, r = z[:, j], z[:, ref]
        po, pr = o / libs[j], r / libs[ref]
        m = np.log2(po / pr)
        if mode == 'edge_order':
            a = (np.log2(po) + np.log2(pr)) / 2
            w = (libs[j] - o) / libs[j] / o + (libs[ref] - r) / libs[ref] / r
        else:
            a = np.log2(po * pr) / 2
            w = (1 - po) / o + (1 - pr) / r
        n = len(m)
        rm, ra = ranks(m), ranks(a)
        keep = ((rm >= np.floor(n * .3) + 1) & (rm <= n - np.floor(n * .3)) &
                (ra >= np.floor(n * .05) + 1) & (ra <= n - np.floor(n * .05)))
        kept_counts.append(int(keep.sum()))
        raw.append(2 ** (np.sum(m[keep] / w[keep]) / np.sum(1 / w[keep])))
    raw = np.array(raw)
    actual = raw / np.exp(np.log(raw).mean())
    shipped = np.loadtxt(root / filename)
    error = float(max(abs(actual - shipped)))
    results[mode] = {'kept': kept_counts, 'factors': actual.tolist(),
                     'max_absolute_error_from_artifact': error}
    assert error < 1e-14, (mode, error)

# The exact rational comparison is independent of NumPy.
edge = list(map(Fraction, (root / 'edger-factors.txt').read_text().splitlines()))
rna = list(map(Fraction, (root / 'rnanorm-factors.txt').read_text().splitlines()))
assert len(edge) == len(rna) == 7
assert all(abs(a - b) > Fraction(1, 10**10) for a, b in zip(edge, rna))
results['decimal_gaps'] = [str(a - b) for a, b in zip(edge, rna)]
print(json.dumps(results, indent=2))
