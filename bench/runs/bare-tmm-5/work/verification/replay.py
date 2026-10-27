"""Execute shipped UQ/TMM class ASTs with explicitly listed dependency shims.

This is a replay aid, not a proof of the unshipped scipy/sklearn/pandas runtimes.
The original methods, branches, and numpy expressions are executed unchanged.
"""
import ast
import contextlib
from pathlib import Path
from typing import Any, Optional
import numpy as np


def rankdata(a):
    a = np.asarray(a)
    return np.array([1 + np.sum(a < v) + (np.sum(a == v) - 1) / 2 for v in a])


class Estimator:
    def set_output(self, **kwargs):
        return self


class Mixin1:
    pass


class Mixin2:
    pass


class LibrarySize(Estimator):
    def fit_transform(self, x):
        return np.nansum(x, axis=1)


def load_classes():
    tree = ast.parse(Path('rnanorm/between_sample.py').read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.ClassDef, ast.FunctionDef))
                 and n.name in ('TMM', 'UQ', 'remove_zero_genes')]
    env = dict(np=np, Any=Any, Optional=Optional, Numeric1D=Any, Numeric2D=Any,
               Self=Any, BaseEstimator=Estimator, OneToOneFeatureMixin=Mixin1,
               TransformerMixin=Mixin2, LibrarySize=LibrarySize,
               rankdata=rankdata, gmean=lambda x: np.exp(np.mean(np.log(x))),
               scoreatpercentile=lambda a, per: np.percentile(a, per, method='linear'),
               validate_data=lambda self, x, **kw: np.asarray(x, dtype=kw.get('dtype')),
               check_is_fitted=lambda self: None,
               config_context=lambda **kw: contextlib.nullcontext(),
               _get_output_config=lambda *args: {})
    exec(compile(tree, 'rnanorm/between_sample.py', 'exec'), env)
    return env['TMM'], env['UQ']


def replay():
    TMM, _ = load_classes()
    x = np.loadtxt('counts.tsv').T
    tmm = TMM().fit(x)
    f = tmm.get_norm_factors(x)
    expected = np.loadtxt('rnanorm-factors.txt')
    assert np.max(np.abs(f-expected)) < 2e-15, (f, expected)
    assert np.array_equal(tmm.ref_, x[3])
    lib = x.sum(axis=1)
    masks = []
    for i in range(7):
        ok = (x[i]>0) & (x[3]>0)
        o, r = x[i,ok], x[3,ok]
        m = np.log2((o/lib[i])/(r/lib[3]))
        a = np.log2((o/lib[i])*(r/lib[3]))/2
        n = len(m)
        keep = ((rankdata(m)>=np.floor(n*.3)+1) & (rankdata(m)<=n-np.floor(n*.3)) &
                (rankdata(a)>=np.floor(n*.05)+1) & (rankdata(a)<=n-np.floor(n*.05)))
        masks.append(np.where(ok)[0][keep].tolist())
    return f, masks


if __name__ == '__main__':
    f, masks = replay()
    print('RNAnorm source replay passed (dependency shims; max absolute error < 2e-15).')
    print('selected gene counts:', [len(m) for m in masks])
    print('factors:', [float(v) for v in f])
