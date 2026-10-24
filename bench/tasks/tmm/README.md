# TMM normalization factors: edgeR (R) and RNAnorm (Python)

TMM (trimmed mean of M-values, Robinson and Oshlack 2010) computes one normalization factor for each sample of an RNA-seq count matrix. This directory holds a count matrix, the factors that two implementations compute for it, and the source of both implementations:

- `counts.tsv`: 454 genes × 7 samples, tab-separated integer counts, one row per gene.
- `edger-factors.txt`: the factors from edgeR 4.99.10 (`normLibSizes(m, method = "TMM")`, produced by `edger-factors.R`), one per line, in sample order.
- `rnanorm-factors.txt`: the factors from RNAnorm 2.2.0 (`TMM().fit(...).get_norm_factors(...)`, produced by `rnanorm-factors.py`), one per line, in sample order.
- `edgeR/`: `R/normLibSizes.R` and `R/calcNormFactors.R` (the implementation; `.calcFactorTMM` computes one factor) and `man/calcNormFactors.Rd` (the documentation).
- `rnanorm/`: `between_sample.py` (the class `TMM` and its documentation) and `utils.py`.

The two output files are the artifacts to verify, byte for byte.

## Requirements

- R1: Each value in `edger-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as edgeR documents TMM in `edgeR/man/calcNormFactors.Rd` (default arguments).
- R2: Each value in `rnanorm-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as RNAnorm documents TMM in the docstring of its class `TMM` (default arguments).
- R3: RNAnorm's documented claim holds for this matrix: its factors are "identical to [edgeR's] to at least 10 decimal places".
