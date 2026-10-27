#!/usr/bin/env python3
"""Supplementary floating-point replay; not part of the Lean proof.

R executes the shipped edgeR functions. Python executes the shipped TMM
_get_norm_factors body, supplying small NumPy substitutes for unavailable
SciPy/sklearn utilities. No shipped files are modified.
"""
import ast
import contextlib
from fractions import Fraction
from pathlib import Path
import subprocess
import numpy as np


def rankdata(a):
    """SciPy's default average rank, with exact equality of float values."""
    s = np.sort(a)
    return (np.searchsorted(s, a, side="left") +
            np.searchsorted(s, a, side="right") + 1) / 2


class LibrarySize:
    def fit_transform(self, X):
        return np.nansum(X, axis=1)


def replay_python(m):
    tree = ast.parse(Path("rnanorm/between_sample.py").read_text())
    remove = next(n for n in tree.body if isinstance(n, ast.FunctionDef)
                  and n.name == "remove_zero_genes")
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "TMM")
    body = next(n for n in cls.body if isinstance(n, ast.FunctionDef)
                and n.name == "_get_norm_factors")
    body.name = "calculate"
    env = dict(np=np, Numeric2D=np.ndarray, Numeric1D=np.ndarray,
               LibrarySize=LibrarySize, rankdata=rankdata,
               config_context=lambda **kw: contextlib.nullcontext())
    exec(compile(ast.Module(body=[remove, body], type_ignores=[]),
                 "rnanorm/between_sample.py (extracted)", "exec"), env)
    x = m.T.copy()
    f75 = np.percentile(x, 75, axis=1) / x.sum(axis=1)
    ref = int(np.argmin(np.abs(f75 - f75.mean())))
    state = type("State", (), dict(ref_=x[ref].copy(), m_trim=.3, a_trim=.05))()
    f = env["calculate"](state, x)
    return ref, f / np.exp(np.log(f).mean())


def main():
    m = np.loadtxt("counts.tsv", dtype=float, delimiter="\t")
    assert m.shape == (454, 7)
    rcode = r'''
source("edgeR/R/normLibSizes.R")
source("edgeR/R/calcNormFactors.R")
m <- as.matrix(read.table("counts.tsv", sep="\t"))
cat(sprintf("%.17g\n", normLibSizes(m)), sep="")
'''
    actual_r = np.array([float(s) for s in subprocess.check_output(
        ["Rscript", "--vanilla", "-e", rcode], text=True).splitlines()])
    ref, actual_py = replay_python(m)
    stored_r = np.loadtxt("edger-factors.txt")
    stored_py = np.loadtxt("rnanorm-factors.txt")
    er = np.max(np.abs(actual_r - stored_r))
    ep = np.max(np.abs(actual_py - stored_py))
    assert ref == 3
    assert er <= 1e-14 and ep <= 1e-14, (er, ep)
    print(f"edgeR source replay maximum absolute error: {er:.3g}")
    print(f"RNAnorm extracted-body replay maximum absolute error: {ep:.3g}")
    print("Reference sample: 4 (one-based)")
    print("PASS: both floating-point replays match artifacts within 1e-14")
    # Explain one unstable M-rank tie without using it as a proof premise.
    pairs = [(int(r[2]), int(r[3])) for r in m if r[2] > 0 and r[3] > 0]
    key = Fraction(5, 10)
    exact_rank = sum(Fraction(a, b) < key for a, b in pairs) + (
        sum(Fraction(a, b) == key for a, b in pairs) + 1) / 2
    x, y = np.array(pairs, dtype=float).T
    mm = np.log2((x / 755) / (y / 1097))
    # gene 451 has the unique (5,10) pair on this matrix.
    loc = pairs.index((5, 10))
    float_rank = rankdata(mm)[loc]
    assert (int(m[450, 2]), int(m[450, 3])) == (5, 10)
    assert exact_rank == 57 and float_rank == 67
    print(f"Gene 451 M rank: exact {exact_rank:g}, float {float_rank:g}; lower cutoff 62")
    print("This replay does not prove agreement with exact-real TMM.")


if __name__ == "__main__":
    main()
