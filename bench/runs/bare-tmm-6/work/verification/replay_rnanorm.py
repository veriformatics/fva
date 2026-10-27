"""Replay the shipped numerical method with small local dependency substitutes.

This is supplementary execution evidence, not a theorem about SciPy/sklearn.
The method body and remove_zero_genes are extracted from shipped source by AST.
"""
import ast
from contextlib import nullcontext
from pathlib import Path
from types import SimpleNamespace
import numpy as np


def rankdata(x):
    # scipy.stats.rankdata's default average-rank semantics, on finite 1-D input.
    order = np.argsort(x)
    out = np.empty(len(x), dtype=float)
    start = 0
    while start < len(x):
        end = start + 1
        while end < len(x) and x[order[end]] == x[order[start]]:
            end += 1
        out[order[start:end]] = (start + 1 + end) / 2
        start = end
    return out


class LibrarySize:
    def fit_transform(self, x):
        return np.nansum(x, axis=1)


tree = ast.parse(Path('rnanorm/between_sample.py').read_text())
remove = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'remove_zero_genes')
cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'TMM')
method = next(n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == '_get_norm_factors')
module = ast.Module(body=[remove, method], type_ignores=[])
ns = dict(np=np, Numeric1D=np.ndarray, Numeric2D=np.ndarray, LibrarySize=LibrarySize,
          rankdata=rankdata, config_context=lambda **_: nullcontext())
exec(compile(module, 'rnanorm/between_sample.py (extracted AST)', 'exec'), ns)
x = np.loadtxt('counts.tsv', delimiter='\t').T
uq = np.quantile(x, .75, axis=1) / x.sum(axis=1)
ref = int(np.argmin(np.abs(uq / np.exp(np.mean(np.log(uq))) - np.mean(uq / np.exp(np.mean(np.log(uq)))))))
assert ref == 3
obj = SimpleNamespace(m_trim=.3, a_trim=.05, ref_=x[ref].copy())
f = ns['_get_norm_factors'](obj, x.copy())
f /= np.exp(np.mean(np.log(f)))
expected = np.loadtxt('rnanorm-factors.txt')
error = np.max(np.abs(f - expected))
assert error < 1e-14, (f, error)
print(f'RNAnorm extracted-method replay with dependency substitutes: PASS (max abs error {error:.3g})')
print('Reference sample (1-based):', ref+1)
