# Draft report: RNAnorm TMM factors differ from edgeR beyond the documented 10 decimal places

Status: draft for the user to post after the benchmark runs (`bench/rubric.md`). Target: https://github.com/genialis/RNAnorm (issue).

## Summary

The docstring of `rnanorm.TMM` (RNAnorm 2.2.0, `src/rnanorm/methods/between_sample.py`) states: "This implementation is based on edgeR's and is validated to be identical to it to at least 10 decimal places." For some count matrices the factors differ from edgeR's in the second or third decimal place.

## Reproduce

1. Use the count matrix in `bench/tasks/tmm/counts.tsv` (454 genes × 7 samples, integer counts; attach it to the issue).
2. Compute the factors with edgeR 4.99.10: `normLibSizes(m, method = "TMM")` (`bench/tasks/tmm/edger-factors.R`).
3. Compute the factors with RNAnorm 2.2.0: `TMM().fit(X).get_norm_factors(X)` with `X` = the matrix with one row per sample (`bench/tasks/tmm/rnanorm-factors.py`).

| sample | edgeR 4.99.10 | RNAnorm 2.2.0 |
|---:|---:|---:|
| 1 | 0.99099942459293067 | 0.9816880015656044 |
| 2 | 1.2772984068792248 | 1.2793096928626835 |
| 3 | 1.1253076397204775 | 1.1270795948647565 |
| 4 | 0.95358597286325431 | 0.9550875280917844 |
| 5 | 0.81337534218434382 | 0.8146561160553638 |
| 6 | 0.92968280356711641 | 0.9311467198937998 |
| 7 | 0.97359269251916547 | 0.9751257511415794 |

The largest relative difference is 9.4 × 10⁻³ (sample 1). In 150 simulated matrices (negative-binomial, low-count and sparse scenarios), 18 gave factors that differ by more than 10⁻⁶.

## Cause

The two implementations compute the A-values (average log expression) with formulas that are equal in exact arithmetic but round differently:

- edgeR (`.calcFactorTMM` in `R/calcNormFactors.R`): `absE <- (log2(obs/nO) + log2(ref/nR))/2`
- RNAnorm: `a = np.log2(r * r_ref) / 2`, with the comment "Order matters: do not change from log(x*y) to log(x)+log(y)"

In matrices with many low counts, many genes have tied A-values. The 5 % trim on the A-values then puts the trim boundary inside a group of tied genes, and the different rounding makes different genes fall inside the boundary. The trimmed set changes, so the weighted mean of the M-values changes. Both implementations rank ties the same way (average ranks: R's `rank`, SciPy's `rankdata`). With RNAnorm's A-value formula in place of its own, edgeR gives RNAnorm's factors on all 18 matrices, and a reimplementation with edgeR's formula gives edgeR's factors on all 150.

## Suggested fix

Compute the A-values as edgeR does, `(np.log2(r) + np.log2(r_ref)) / 2`. Alternatively, weaken the documented claim.
