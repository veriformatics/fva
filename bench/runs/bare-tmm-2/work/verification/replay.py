#!/usr/bin/env python3
"""Read-only operational replay and tie diagnostics. See VERIFICATION.md for limits.

The R replay executes bundled functions. For Python, execute the bundled AST of
UQ, TMM, LibrarySize and remove_zero_genes with small dependency adapters: SciPy,
pandas and sklearn are absent. The AST bodies are not rewritten.
"""
import ast
import contextlib
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import sys
import types
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
assert Path.cwd() == ROOT, "Run from the project directory"


def ranks(a):
    """SciPy rankdata default: increasing order, average rank of equal doubles."""
    a = np.asarray(a)
    order = np.argsort(a, kind="mergesort")
    ans = np.empty(len(a), dtype=float)
    i = 0
    while i < len(a):
        j = i + 1
        while j < len(a) and a[order[j]] == a[order[i]]:
            j += 1
        ans[order[i:j]] = (i + 1 + j) / 2
        i = j
    return ans


class BaseEstimator:
    def set_output(self, **kw):
        return self


class OneToOneFeatureMixin:
    pass


class TransformerMixin:
    pass


class FunctionTransformer(BaseEstimator):
    def __init__(self, func, kw_args, **kw):
        self.func, self.kw_args = func, kw_args

    def fit_transform(self, X):
        X = self._check_input(X, reset=True)
        return self.func(X, **self.kw_args)


def validate_data(estimator, X, **kw):
    a = np.asarray(X, dtype=kw.get("dtype", None))
    assert a.ndim == 2 and np.isfinite(a).all()
    return a


def check_is_fitted(obj):
    assert hasattr(obj, "geometric_mean_")


class DataFrame:
    pass


class Series:
    pass


ns = dict(np=np, BaseEstimator=BaseEstimator,
          OneToOneFeatureMixin=OneToOneFeatureMixin,
          TransformerMixin=TransformerMixin, FunctionTransformer=FunctionTransformer,
          validate_data=validate_data, check_is_fitted=check_is_fitted,
          config_context=lambda **kw: contextlib.nullcontext(),
          _get_output_config=lambda *args: {"dense": "default"},
          pd=types.SimpleNamespace(DataFrame=DataFrame, Series=Series),
          rankdata=ranks, gmean=lambda a: np.exp(np.mean(np.log(a))),
          scoreatpercentile=lambda a, per: np.percentile(a, per))


def execute_definitions(path, wanted):
    original = ast.parse(Path(path).read_text())
    selected = [n for n in original.body
                if isinstance(n, (ast.ClassDef, ast.FunctionDef)) and n.name in wanted]
    assert {n.name for n in selected} == set(wanted)
    future = ast.ImportFrom(module="__future__",
                            names=[ast.alias(name="annotations")], level=0)
    tree = ast.fix_missing_locations(ast.Module(body=[future] + selected, type_ignores=[]))
    exec(compile(tree, str(path), "exec"), ns)


execute_definitions("rnanorm/utils.py", ["LibrarySize"])
execute_definitions("rnanorm/between_sample.py", ["remove_zero_genes", "UQ", "TMM"])

m = np.loadtxt("counts.tsv", delimiter="\t", dtype=float, ndmin=2)
assert m.shape == (454, 7) and (m >= 0).all() and (m == np.floor(m)).all()
python_masks = {}
python_ties = {}


def observe(frame, event, arg):
    # Observe the original function just before f.append consumes the final mask.
    if (event == "line" and frame.f_code.co_name == "_get_norm_factors"
            and "keep" in frame.f_locals):
        d = frame.f_locals
        if "i" in d and "finite" in d and frame.f_lineno == APPEND_LINE:
            rows = np.flatnonzero(d["finite"])[d["keep"]] + 1
            python_masks[int(d["i"])] = list(map(int, rows))
            if d["i"] == 0:
                ids = list(np.flatnonzero(d["finite"]) + 1)
                for row in [163, 355]:
                    j = ids.index(row)
                    python_ties[row] = (d["aa"][j], ranks(d["aa"])[j])
    return observe


src = ast.parse(Path("rnanorm/between_sample.py").read_text())
tmm = next(n for n in src.body if isinstance(n, ast.ClassDef) and n.name == "TMM")
APPEND_LINE = next(n.lineno for n in ast.walk(tmm) if isinstance(n, ast.Call)
                   and isinstance(n.func, ast.Attribute) and n.func.attr == "append")
sys.settrace(observe)
try:
    model = ns["TMM"]().fit(m.T)
    python_factors = model.get_norm_factors(m.T)
finally:
    sys.settrace(None)
assert len(python_masks) == 7
reference = next(i for i in range(7) if np.array_equal(model.ref_, m[:, i]))
assert reference == 3

r = subprocess.run(["Rscript", "verification/replay.R"], text=True,
                   capture_output=True, check=True)
r_masks, r_factors = {}, {}
for line in r.stdout.splitlines():
    if line.startswith("MASK "):
        _, i, *rows = line.split()
        r_masks[int(i)-1] = list(map(int, rows))
    elif line.startswith("FACTOR "):
        _, i, val = line.split()
        r_factors[int(i)-1] = val
assert len(r_factors) == len(r_masks) == 7
# Byte equality verifies the observed R formatting, including final newlines.
assert "".join(r_factors[i] + "\n" for i in range(7)).encode() == Path("edger-factors.txt").read_bytes()
# The RNAnorm dependency adapters can vary at the last bit; use stated tolerance.
rna = [Q(v) for v in Path("rnanorm-factors.txt").read_text().splitlines()]
edge = [Q(v) for v in Path("edger-factors.txt").read_text().splitlines()]
assert all(abs(Q(float(f)) - v) < Q(1, 10**10) for f, v in zip(python_factors, rna))
assert all(abs(e-n) > Q(1, 10**10) for e, n in zip(edge, rna))
print("PASS: bundled R replay reproduces edger-factors.txt byte for byte")
print("PASS: bundled Python AST with dependency adapters reproduces RNAnorm factors within 1e-10")
print("PASS: all seven artifact differences exceed 1e-10")
print("reference (1-based):", reference + 1)
print("source keep counts: R", [len(r_masks[i]) for i in range(7)],
      "Python", [len(python_masks[i]) for i in range(7)])
assert [len(r_masks[i]) for i in range(7)] == [65,79,77,300,89,95,81]
assert [len(python_masks[i]) for i in range(7)] == [64,79,77,283,89,95,81]
print("R early-returns unity for the reference; its 300 retained positive rows are diagnostic only.")
print("sample 1 differing rows (1-based): R-only", sorted(set(r_masks[0])-set(python_masks[0])),
      "Python-only", sorted(set(python_masks[0])-set(r_masks[0])))
for line in r.stdout.splitlines():
    if line.startswith("TIE "):
        print(line)
for row, (a, rank) in python_ties.items():
    print(f"TIE row {row}: A_Python={a:.17g} rank_Python={rank:g}")
print("first artifact difference (exact):", edge[0]-rna[0])
