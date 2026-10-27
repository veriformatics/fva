"""Run original RNAnorm function ASTs with explicit local dependency adapters.
This is numerical reproduction, not a formal semantics for Python/SciPy/sklearn.
"""
import __future__
import ast
import contextlib
from pathlib import Path
import numpy as np

# These adapters cover only the finite, dense numeric path used by this input.
class LibrarySize:
    def set_output(self, **kwargs):
        return self

    def fit_transform(self, x):
        return np.nansum(x, axis=1)


def validate_data(self, x, **kwargs):
    a = np.array(x, dtype=float, copy=True)
    assert a.ndim == 2 and np.isfinite(a).all() and (a >= 0).all()
    return a


rank_calls = []


def rankdata(a):
    assert a.ndim == 1 and np.isfinite(a).all()
    _, inv, counts = np.unique(a, return_inverse=True, return_counts=True)
    ends = np.cumsum(counts)
    ranks = ((ends-counts+1 + ends)/2)[inv]
    rank_calls.append((a.copy(), ranks.copy()))
    return ranks


def gmean(a):
    assert np.isfinite(a).all() and (a > 0).all()
    return np.exp(np.mean(np.log(a)))


def scoreatpercentile(a, per):
    return np.percentile(a, per, method="linear")


def check_is_fitted(self):
    assert hasattr(self, "geometric_mean_")


source = Path("rnanorm/between_sample.py").read_text()
tree = ast.parse(source)
ns = dict(np=np, LibrarySize=LibrarySize, validate_data=validate_data,
          rankdata=rankdata, gmean=gmean, scoreatpercentile=scoreatpercentile,
          config_context=lambda **kw: contextlib.nullcontext(),
          check_is_fitted=check_is_fitted, _get_output_config=lambda *args: {})


def original_function(nodes, name):
    node, = [n for n in nodes if isinstance(n, ast.FunctionDef) and n.name == name]
    # The function AST, including its body and defaults, is used unchanged.
    code = compile(ast.Module(body=[node], type_ignores=[]),
                   "rnanorm/between_sample.py", "exec",
                   flags=__future__.annotations.compiler_flag)
    exec(code, ns)
    return ns[name]


ns["remove_zero_genes"] = original_function(tree.body, "remove_zero_genes")
for class_name in ("UQ", "TMM"):
    cls, = [n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == class_name]
    names = ["_get_norm_factors", "get_norm_factors", "_reset", "fit"]
    if class_name == "TMM":
        names += ["__init__", "_get_ref"]
    methods = {name: original_function(cls.body, name) for name in names}
    ns[class_name] = type(class_name, (), methods)

matrix = np.loadtxt("counts.tsv", delimiter="\t", ndmin=2)
assert matrix.shape == (454, 7) and np.isfinite(matrix).all()
assert (matrix >= 0).all() and (matrix == np.floor(matrix)).all()
x = matrix.T.copy()
tmm = ns["TMM"]().fit(x)
f = tmm.get_norm_factors(x)
expected = np.loadtxt("rnanorm-factors.txt")
assert f.shape == expected.shape == (7,) and np.isfinite(f).all()
assert np.max(np.abs(f-expected)) <= 1e-12
formatted = "".join(f"{float(v)!r}\n" for v in f).encode("ascii")
assert formatted == Path("rnanorm-factors.txt").read_bytes()
assert np.array_equal(tmm.ref_, matrix[:, 3])
print(f"R2 numerical-body reproduction with adapters: 7/7, max absolute error {np.max(np.abs(f-expected)):.17g}, exact file bytes")
# rankdata is called twice on M and twice on A for each sample.
mm, aa = rank_calls[0][1], rank_calls[2][1]
ids = np.flatnonzero((matrix[:, 0] > 0) & (matrix[:, 3] > 0))
n = len(ids)
keep = ((mm >= np.floor(n*.3)+1) & (mm <= n-np.floor(n*.3)) &
        (aa >= np.floor(n*.05)+1) & (aa <= n-np.floor(n*.05)))
retained = set((ids[keep]+1).tolist())
edge_retained = set(map(int, Path(".verification-build/edge-retained.txt").read_text().split()))
assert edge_retained - retained == {355} and not retained - edge_retained
print("Actual sample 1 trimming difference: edgeR alone retains gene 355")
print("R1 and R2 documentation conformance remains formally UNPROVED")
