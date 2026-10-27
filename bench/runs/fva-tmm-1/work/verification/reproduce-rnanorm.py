"""Supplemental NumPy reconstruction of the supplied TMM methods.
SciPy/sklearn are unavailable. Average ranks and gmean are implemented here.
This checks a transcription, not execution of the complete RNAnorm package.
"""
from pathlib import Path
import numpy as np

def ranks(values):
    return np.array([1 + np.count_nonzero(values < z) +
                     (np.count_nonzero(values == z)-1)/2 for z in values])

X = np.loadtxt('counts.tsv', delimiter='\t', ndmin=2).T
X = X[:, X.sum(axis=0) > 0]
lib = X.sum(axis=1)
f75 = np.percentile(X, 75, axis=1) / lib
# Normalizing all f75 by the same positive geometric mean leaves argmin unchanged.
ref_index = np.argmin(np.abs(f75 - f75.mean()))
ref = X[ref_index].copy()
lib_ref = ref.sum()
X[X == 0] = np.nan
ref[ref == 0] = np.nan
r = X / lib[:, None]
r_ref = ref / lib_ref
m = np.log2(r / r_ref)
a = np.log2(r * r_ref) / 2
w = (1-r) / X + (1-r_ref) / ref
f = []
print('reference sample:', ref_index+1)
for j in range(X.shape[0]):
    finite = np.isfinite(m[j]) & np.isfinite(a[j])
    mm, aa, ww = m[j, finite], a[j, finite], w[j, finite]
    n = len(mm)
    rm, ra = ranks(mm), ranks(aa)
    keep = ((rm >= np.floor(n*.3)+1) & (rm <= n-np.floor(n*.3)) &
            (ra >= np.floor(n*.05)+1) & (ra <= n-np.floor(n*.05)))
    f.append(2 ** (np.nansum(keep*mm/ww) / np.nansum(keep/ww)))
    print('sample', j+1, 'positive pairs', n, 'kept', np.count_nonzero(keep))
f = np.asarray(f)
f /= np.exp(np.log(f).mean())
actual = ''.join(f'{float(v)!r}\n' for v in f).encode()
assert actual == Path('rnanorm-factors.txt').read_bytes(), (actual, Path('rnanorm-factors.txt').read_bytes())
print('RNAnorm NumPy reconstruction: exact byte reproduction PASS')
