"""Execute the shipped RNAnorm numerical kernel with explicit dependency adapters.

This is a source-level replay, not an installation of RNAnorm or a proof of the
SciPy/sklearn adapters. The untouched _get_norm_factors AST is compiled below.
"""
import ast
from contextlib import nullcontext
from pathlib import Path
import sys
import numpy as np


def rankdata(values):
    # scipy.stats.rankdata's default: average, one-based ranks.
    return np.array([(1 + np.sum(values < x) + np.sum(values <= x)) / 2
                     for x in values], dtype=float)


class LibrarySize:
    def fit_transform(self, x):
        # utils.py: FunctionTransformer(func=np.nansum, kw_args=dict(axis=1)).
        return np.nansum(x, axis=1)


def run():
    path = Path("rnanorm/between_sample.py")
    tree = ast.parse(path.read_text(), filename=str(path))
    remove = next(x for x in tree.body if isinstance(x, ast.FunctionDef)
                  and x.name == "remove_zero_genes")
    cls = next(x for x in tree.body if isinstance(x, ast.ClassDef) and x.name == "TMM")
    method = next(x for x in cls.body if isinstance(x, ast.FunctionDef)
                  and x.name == "_get_norm_factors")
    # Remove type annotations only; every executable statement is unchanged.
    method.returns = None
    for a in method.args.args:
        a.annotation = None
    remove.returns = None
    for a in remove.args.args:
        a.annotation = None
    env = dict(np=np, config_context=lambda **kw: nullcontext(),
               LibrarySize=LibrarySize, rankdata=rankdata)
    exec(compile(ast.Module(body=[remove, method], type_ignores=[]), str(path), "exec"), env)
    x = np.loadtxt("counts.tsv", delimiter="\t", ndmin=2).T
    assert x.shape == (7, 454)
    x = env["remove_zero_genes"](x)
    # UQ().fit(X).get_norm_factors(X) uses this 75th percentile, divided by
    # library size and then its geometric mean. This is _get_ref's input.
    uq = np.percentile(x, 75, axis=1) / np.nansum(x, axis=1)
    uq = uq / np.exp(np.mean(np.log(uq)))
    reference = int(np.argmin(np.abs(uq - np.mean(uq))))
    assert reference == 3
    obj = type("KernelInput", (), {})()
    obj.ref_ = x[reference, :]
    obj.m_trim, obj.a_trim = 0.3, 0.05
    selected = []
    diagnostics = []
    append_line = next(n.lineno for n in ast.walk(method)
                       if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
                       and isinstance(n.value.func, ast.Attribute)
                       and n.value.func.attr == "append")

    def trace(frame, event, arg):
        if (frame.f_code.co_name == "_get_norm_factors" and event == "line"
                and frame.f_lineno == append_line):
            loc = frame.f_locals
            selected.append((np.flatnonzero(loc["finite"])[loc["keep"]] + 1).tolist())
            if loc["i"] == 0:
                j = np.flatnonzero(np.flatnonzero(loc["finite"]) == 354)[0]
                diagnostics.append((float(rankdata(loc["aa"])[j]), float(loc["a_high"]),
                                    355 in selected[-1]))
        return trace

    sys.settrace(trace)
    try:
        # fit computes the geometric mean of the unnormalized factors;
        # get_norm_factors repeats the same kernel on the same training input.
        raw = env["_get_norm_factors"](obj, x.copy())
        geometric_mean = np.exp(np.mean(np.log(raw)))
        raw2 = env["_get_norm_factors"](obj, x.copy())
    finally:
        sys.settrace(None)
    assert selected[:7] == selected[7:]
    assert np.array_equal(raw, raw2)
    factors = raw2 / geometric_mean
    output = "".join(f"{float(f)!r}\n" for f in factors).encode()
    assert output == Path("rnanorm-factors.txt").read_bytes()
    assert diagnostics == [(232.5, 232.0, False)] * 2
    print("RNAnorm sample 1, gene 355: A-rank 232.5 upper cutoff 232 retained False")
    print("RNAnorm kernel + adapters: exact output bytes reproduced; retained genes:",
          [len(s) for s in selected[:7]])
    return selected[:7]


if __name__ == "__main__":
    run()
