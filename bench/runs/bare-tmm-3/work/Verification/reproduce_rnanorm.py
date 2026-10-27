"""Execute the shipped numerical TMM method with small, disclosed dependency adapters.

This is a reproduction check, not a verified replacement for scipy/sklearn.
The installed environment has NumPy but not scipy, sklearn, or the full package.
"""
import ast
from contextlib import nullcontext
from pathlib import Path
from types import SimpleNamespace
import numpy as np


def rankdata(a):
    # scipy.stats.rankdata default: one-based average ranks of ties.
    return np.array([np.sum(a < t) + (np.sum(a == t) + 1) / 2 for t in a])


class LibrarySize:
    def fit_transform(self, x):
        return np.nansum(x, axis=1)


source = Path('rnanorm/between_sample.py').read_text()
module = ast.parse(source)
tmm = next(n for n in module.body if isinstance(n, ast.ClassDef) and n.name == 'TMM')
method = next(n for n in tmm.body
              if isinstance(n, ast.FunctionDef) and n.name == '_get_norm_factors')
# Remove only unavailable type annotations; execute the unchanged method body.
method.returns = None
for arg in method.args.args:
    arg.annotation = None
executable = ast.fix_missing_locations(ast.Module(body=[method], type_ignores=[]))
namespace = dict(np=np, rankdata=rankdata, LibrarySize=LibrarySize,
                 config_context=lambda **kw: nullcontext(),
                 remove_zero_genes=lambda x: np.asarray(x)[:, np.sum(x, axis=0) > 0])
exec(compile(executable, 'rnanorm/between_sample.py', 'exec'), namespace)

x = np.loadtxt('counts.tsv', delimiter='\t', ndmin=2).T
x = x[:, np.sum(x, axis=0) > 0]
# UQ._get_norm_factors uses scipy scoreatpercentile's default interpolation.
# For this matrix the two adjacent upper-quartile counts are equal in every column.
ordered = np.sort(x, axis=1)
assert np.array_equal(ordered[:, 339], ordered[:, 340])
q = ordered[:, 339] / np.nansum(x, axis=1)
q /= np.exp(np.log(q).mean())
reference = int(np.argmin(np.abs(q - q.mean())))
assert reference == 3
obj = SimpleNamespace(ref_=x[reference].copy(), m_trim=0.3, a_trim=0.05)
f = namespace['_get_norm_factors'](obj, x.copy())
f /= np.exp(np.log(f).mean())
actual = ''.join(f'{float(v)!r}\n' for v in f).encode()
assert actual == Path('rnanorm-factors.txt').read_bytes(), (actual, 'different bytes')
print('PASS: shipped RNAnorm numerical method, with disclosed adapters, reproduces its file byte for byte')
