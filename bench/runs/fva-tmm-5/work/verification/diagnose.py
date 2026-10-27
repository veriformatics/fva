"""Supplementary floating-point diagnosis; NOT used by the Lean proofs.
Requires the installed NumPy. Implements average ranks directly (no SciPy/R).
"""
from pathlib import Path
from fractions import Fraction
import numpy as np

x = np.loadtxt('counts.tsv', dtype=np.int64)
x = x[np.any(x > 0, axis=1)]
lib = x.sum(axis=0)
q = np.quantile(x, .75, axis=0) / lib
ref = int(np.argmin(abs(q - q.mean())))

def rank2(xs, v):
    return 2 * sum(u < v for u in xs) + sum(u == v for u in xs) + 1

def keep(ms, aas):
    n = len(ms)
    return np.array([
        2*(3*n//10+1) <= rank2(ms, m) <= 2*(n-3*n//10)
        and 2*(n//20+1) <= rank2(aas, a) <= 2*(n-n//20)
        for m, a in zip(ms, aas)])

means = {mode: [] for mode in ('exact-ranks', 'edgeR-formulas', 'RNAnorm-formulas')}
print('Libraries:', lib.tolist(), '; reference (one based):', ref + 1)
for j in range(7):
    rows = np.flatnonzero((x[:,j] > 0) & (x[:,ref] > 0))
    a, b = x[rows,j].astype(float), x[rows,ref].astype(float)
    exact_m = [Fraction(int(v),int(w)) for v,w in zip(a,b)]
    exact_a = [int(v)*int(w) for v,w in zip(a,b)]
    masks = {'exact-ranks': keep(exact_m, exact_a)}
    m = np.log2((a/lib[j])/(b/lib[ref]))
    masks['edgeR-formulas'] = keep(m, (np.log2(a/lib[j])+np.log2(b/lib[ref]))/2)
    masks['RNAnorm-formulas'] = keep(m, np.log2((a/lib[j])*(b/lib[ref]))/2)
    w = (1-a/lib[j])/a + (1-b/lib[ref])/b
    for mode, mask in masks.items():
        means[mode].append(float(np.sum(m[mask]/w[mask])/np.sum(1/w[mask])))
        if mode != 'exact-ranks':
            for k in np.flatnonzero(mask != masks['exact-ranks']):
                print(f'Sample {j+1}, {mode}, gene {rows[k]+1}, pair '
                      f'{(int(a[k]),int(b[k]))}: exact keep={masks["exact-ranks"][k]}, '
                      f'float keep={mask[k]}, exact doubled M rank={rank2(exact_m,exact_m[k])}, '
                      f'float doubled M rank={rank2(m,m[k])}')
for mode, values in means.items():
    values = np.array(values)
    factors = np.exp2(values-values.mean())
    print(mode, [f'{v:.17g}' for v in factors])
print('Shipped first-factor difference:',
      abs(Fraction(Path('edger-factors.txt').read_text().splitlines()[0]) -
          Fraction(Path('rnanorm-factors.txt').read_text().splitlines()[0])))
