# PFlog normalization (Rust, WebAssembly build) and the CLR uniqueness theorem

`runorm-pflog.wasm` is the WebAssembly build (125,423 bytes, sha256 `ab1fc4edf899dc1afbbeec8871e35b5041e04c854f34831cc8cf393f497c2900`) of the Rust crate runorm (commit `9429aa0`, in `shim/vendor/runorm/`, unmodified). The crate in `shim/` exports runorm's `pflog` function, and `build.sh` records how the module was built. The module is the artifact to verify.

`Invariance.lean` and `Invariance/` are the Pachter lab's Lean formalization of the CLR invariance characterization (repository BHGP_2022, commit `ddb3602`, directory `lean/`), ported to Lean 4.35 and Mathlib v4.35.0. The port removes four tactic lines that the newer Mathlib makes redundant; `invariance-port.diff` is the whole change. This directory is a Lake project with the library `Invariance`, so `import Invariance` works. In particular:

- `Invariance.clr_uniqueness_theorem`: a transform of log-coordinates that is rank-monotone, additive, equivariant under relabeling of coordinates, zero on constant vectors and calibrated is exactly `Invariance.clr`.
- `Invariance.shifted_domain_pullback_clr`: the same characterization carried to `Invariance.shiftedCLR τ`, the CLR of `log(u + τ)`.

## Interface

The module exports its memory and three functions. All values are `i32`; the buffers hold `f64` values and are addresses in the exported memory.

- `pflog_counts()` returns the address of the input buffer (131,072 values).
- `pflog_output()` returns the address of the output buffer (131,072 values).
- `pflog(n_cells, n_genes)` reads the first `n_cells · n_genes` values of the input buffer as a count matrix (row-major, one row per cell) and normalizes it with runorm's `pflog`: the overdispersion `α` is estimated from the matrix, and each cell's row becomes `log1p(4α·x) − mean`, as `shim/vendor/runorm/src/lib.rs` documents. It writes the result in the same layout to the output buffer and returns 0. It returns −1 when the matrix has more than 131,072 entries or runorm rejects the matrix.

## Requirements

In each requirement, the input is a matrix of non-negative integer counts with at least one cell and at least two genes, and `pflog` returns 0 for it.

- R1: Let `α` be the overdispersion that runorm documents for the matrix, computed exactly: the least-squares fit of `Var_g = μ_g + α·μ_g²` over the genes, `α = Σ_g (Var_g − μ_g)·μ_g² / Σ_g μ_g⁴`, where `μ_g` and `Var_g` are the mean and the population variance of gene `g` over the cells (`estimate_overdispersion`). Let `τ = 1/(4α)`. Then every output value differs by at most a tolerance `ε` from the value of `Invariance.shiftedCLR τ`, applied to its cell's counts, at that gene. State `ε` and the matrices that it covers. With R1, `Invariance.shifted_domain_pullback_clr` applies to the output up to `ε`: the module computes, within `ε`, the only transform that has the five properties above.
- R2: Within each cell, a gene with a larger count never gets a smaller output value.
- R3: When the genes of the input are relabeled (its columns permuted), the output columns are permuted in the same way, within the tolerance of R1.
