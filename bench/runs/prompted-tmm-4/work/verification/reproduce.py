"""Diagnostic only: execute the shipped numerical method, supplying absent wrappers."""
import ast
import contextlib
from pathlib import Path
from types import SimpleNamespace
import numpy as np

source = ast.parse(Path('rnanorm/between_sample.py').read_text())
remove = next(n for n in source.body if isinstance(n, ast.FunctionDef) and n.name == 'remove_zero_genes')
tmm = next(n for n in source.body if isinstance(n, ast.ClassDef) and n.name == 'TMM')
method = next(n for n in tmm.body if isinstance(n, ast.FunctionDef) and n.name == '_get_norm_factors')
class LibrarySize:
    def fit_transform(self, x):
        return np.nansum(x, axis=1)
def rankdata(x):
    _, inverse, counts = np.unique(x, return_inverse=True, return_counts=True)
    return (np.cumsum(counts) - (counts - 1) / 2)[inverse]
ns = dict(np=np, Numeric1D=object, Numeric2D=object, LibrarySize=LibrarySize,
          rankdata=rankdata, config_context=lambda **_: contextlib.nullcontext())
exec(compile(ast.Module(body=[remove, method], type_ignores=[]), '<shipped AST>', 'exec'), ns)
x = np.loadtxt('counts.tsv').T
uq = np.quantile(x, .75, axis=1) / x.sum(axis=1)
reference = np.argmin(abs(uq - uq.mean()))
assert reference == 3
self = SimpleNamespace(ref_=x[reference].copy(), m_trim=.3, a_trim=.05)
f = ns['_get_norm_factors'](self, x.copy())
f /= np.exp(np.log(f).mean())
error = np.max(abs(f - np.loadtxt('rnanorm-factors.txt')))
assert error < 1e-14
print(f'RNAnorm shipped method diagnostic: max difference {error:.3g}')
