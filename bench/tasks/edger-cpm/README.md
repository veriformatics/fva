# edgeR: counts per million and expression filtering

edgeR is a Bioconductor package for RNA-seq analysis. `edgeR.so` is the shipped compiled C code of edgeR 4.99.10 for WebAssembly (from R-universe, built with Emscripten; 96,558 bytes, sha256 `e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb`). `src/` holds the C sources of the functions below, `R/` the R code of `cpm` and `filterByExpr`, `man/` their documentation. `edgeR.so` is the artifact to verify for the C function; the R code runs as written.

## Interface

- `calc_cpm_raw` (exported by `edgeR.so`, source `src/compute_cpm.c`): computes counts per million for a matrix of counts and the library sizes of its columns, as R's `edgeR::cpm` uses it.
- `filterByExpr` (R, `R/filterByExpr.R`): decides which genes (rows) to keep.

## Requirements

- R1: For every count `c` and library size `L > 0`, the counts-per-million value that `calc_cpm_raw` computes is `c / L × 10⁶`, rounded as double-precision arithmetic allows; state the rounding error you prove.
- R2: `filterByExpr` keeps a gene exactly when, in at least the required number of samples, its count reaches the minimum count `min.count` that its documentation states (with the documented scaling to counts per million at the median library size).
