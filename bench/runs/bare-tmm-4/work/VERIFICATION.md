# Verification of the shipped TMM factors

The artifacts fail **R3**. Both files can be reproduced byte for byte here, and Lean proves absolute error bounds of **10^-12** against explicit TMM models for R1 and R2. Those models use the gene selections observed in the source replays. **The selection computations and full R/Python/dependency semantics are not formally verified. R1 and R2 therefore have model-relative proofs, not unconditional end-to-end proofs.**

All indices in Lean are zero-based; sample and gene numbers in this report are one-based. Neither shipped output file was changed.

## R1

`Proofs/Results.lean`, namespace `Verification`, contains this exact statement:

```lean
theorem R1_selected_TMM : ∀ i : Fin 7,
    |selectedTMM counts edgeMasks i - (edgeValues i : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ)
```

This proves the bound for every output, using exact rational counts, exact inverse-variance weights, real logarithms and exponentiation, and the retained genes from the edgeR replay. The tolerance is absolute, per sample. The auxiliary `R1_model` proves the same bound using `factor edgeRaw i` in place of `selectedTMM counts edgeMasks i`; `edgeRaw_from_counts` formally connects these representations.

`verification/replay.R` sources the shipped `calcNormFactors.R` and `normLibSizes.R` and executes `normLibSizes(m, method="TMM")` with all remaining arguments at their defaults. Its machine-checked output assertion is:

```r
identical(
  charToRaw(paste0(paste(sprintf("%.17g", f), collapse="\n"), "\n")),
  readBin("edger-factors.txt", "raw", file.info("edger-factors.txt")$size)
)
```

It also records `.calcFactorTMM`'s selected genes by inspecting its local variables at function exit. The retained counts are `65, 79, 77, 300, 89, 95, 81`. Sample 4 takes edgeR's early return of 1; the recorded 300 finite genes all have expression ratio 1, so the model's weighted log mean is also zero.

What remains unproved: that execution of the R source, including its floating-point logarithms and rank calculations, implements an independently formalized reading of the prose documentation. The replay is execution evidence, not a proof of R or libm semantics. In particular, the Lean model takes the trimming mask as input; it does not derive that mask by ideal-real rank comparisons.

## R2

`Proofs/Results.lean` contains this exact statement:

```lean
theorem R2_selected_TMM : ∀ i : Fin 7,
    |selectedTMM counts rnaMasks i - (rnaValues i : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ)
```

The absolute tolerance is again 10^-12 per sample. The auxiliary `R2_model` uses `factor rnaRaw i`; `rnaRaw_from_counts` connects it to the matrix and retained genes. These are numerical-model correctness theorems, independent of trusting a floating-point recomputation of the weighted logarithmic mean.

SciPy, scikit-learn, and a complete importable RNAnorm package are absent. `verification/replay.py` therefore compiles and executes the shipped `TMM._get_norm_factors` AST, preserving every executable statement. It also executes the shipped `remove_zero_genes` function. Explicit adapters supply average one-based ranks, library sums, and the configuration context. Reference selection and fit/get normalization are modeled using NumPy's linear 75th percentile and `exp(mean(log(...)))`. The script computes the kernel twice, as fit/get do, and checks that both selections and raw factors agree. Its final assertion is exact byte equality:

```python
"".join(f"{float(f)!r}\n" for f in factors).encode() == Path("rnanorm-factors.txt").read_bytes()
```

The retained counts are `64, 79, 77, 283, 89, 95, 81`. The formal model uses defaults `m_trim=0.3`, `a_trim=0.05`, as specified by the constructor and parameter descriptions. The procedure bullet mentioning `m_trim` for A-values is inconsistent with the separate `a_trim` parameter and implementation; it is not silently treated as an additional default of 0.3 for A-trimming.

What remains unproved: source-language and NumPy semantics, equivalence of these adapters to every detail of the missing SciPy/scikit-learn dependencies, and correctness of the floating-point trimming mask against an independent documentation specification. This is explicitly a kernel replay with adapters, not a claim that the complete RNAnorm installation was executed. R2's documentation also includes the identity claim separately required by R3, which fails below.

## R3: counterexample and exact proof

The counterexample input is the entire shipped `counts.tsv`. Sample 1 alone suffices:

| Artifact | Exact line 1 |
|---|---|
| edgeR | `0.99099942459293067` |
| RNAnorm | `0.9816880015656044` |

Their exact decimal difference is `0.00931142302732627`. Rounded to ten places they are `0.9909994246` and `0.9816880016`.

`Proofs/Artifacts.lean` proves the stronger, exact rational statements:

```lean
theorem R3_gap : ∀ i : Fin 7,
    (1/1000 : ℚ) < |edgeValues i - rnaValues i|

def round10 (q : ℚ) : ℤ := ⌊q * 10^10 + 1/2⌋

theorem R3_rounding : ∀ i : Fin 7,
    round10 (edgeValues i) ≠ round10 (rnaValues i)
```

Thus every sample differs by more than 0.001, and every sample rounds differently at ten decimal places. This refutes both an absolute-error interpretation of “at least 10 decimal places” and ordinary rounding to ten places. This proof needs neither TMM modeling nor trust in either implementation.

The same file proves that the embedded output text parses to the rational values used above:

```lean
theorem edge_parses : parseFactors edgeBytes = some (List.ofFn edgeValues)
theorem rna_parses : parseFactors rnaBytes = some (List.ofFn rnaValues)
```

`parseFactors`, in `Proofs/Parsing.lean`, requires a final LF and nonempty unsigned decimal integer/fractional parts. These are exact decimal rationals, not conversions through binary floating point.

The replays diagnose the discrepancy at sample 1, gene 355: edgeR gives its A-value rank 232 and retains it; RNAnorm gives rank 232.5 and excludes it; the upper cutoff is 232. Genes 163 and 355 have count pairs `(8,13)` and `(13,8)`, with identical exact products 104. edgeR computes A using a sum of logs; RNAnorm uses the log of a product. Rounding splits the mathematical tie in the R calculation. Apart from the reference sample's zero-log early return, the recorded masks differ only by gene 355 in sample 1. Geometric normalization then changes every final factor.

## Formal model and connection to the bytes

`verification/inputs.json` contains the **complete bytes as hexadecimal**, not just hashes, of the matrix, both outputs, both producer scripts, both implementations and their documentation, and README. `generate.py --check` first compares those exact bytes, then repeats both source replays and compares the regenerated Lean files and trimming masks with those delivered here. It never rewrites the shipped artifacts.

For convenient identification:

| File | Bytes | SHA-256 |
|---|---:|---|
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

`Proofs/InputData.lean` embeds the matrix's individual lines and its integer matrix. `counts_parses` proves the row-by-row parsing relation. `counts_shape`, `no_zero_rows`, `library_sizes`, `upper_quartiles`, and `reference_closest` prove the shape, preprocessing facts, library sizes, exact type-7 quartiles, and unique nearest-quartile reference (sample 4). Library sizes are `[1261, 621, 755, 1097, 1916, 1136, 1219]`. The masks are also explicit there; their validity theorems check distinct in-range indices and positive weights/ratios. `verification/masks.json` is the replay-readable version.

`Proofs/Model.lean` defines, for a retained gene with sample count o, reference count r, and library sizes N_i, N_4:

```
w = 1 / (1/o - 1/N_i + 1/r - 1/N_4)
q = o*N_4 / (r*N_i)
z_i = sum over retained genes of (w / sum(weights)) * log(q)
F_i = exp(z_i - sum_j(z_j)/7)
```

`selectedTMM` is exactly this function of the integer matrix and supplied masks. Weight and ratio arithmetic is rational; log and exp are mathematical real functions. The masks preserve the actual execution's rounding-sensitive selection decisions. No assumption is made that recomputing ranks over exact-real logarithms would give those same masks.

For every sample, `Proofs/Certificates.lean` proves `*Input*_from_counts`, `*Weight*`, and `*Terms*_from_counts`, connecting all generated coefficients and ratios back to the matrix, masks, and `selectedTerms` definition. `edgeRaw_from_counts` and `rnaRaw_from_counts` connect the weighted real logarithms to `selectedRaw`. These are kernel-checked equalities, not just generator assertions.

`Proofs/TMM.lean` proves `raw_base_two` (equivalence to exponentiating weighted base-2 M-values), `factor_geometric_mean` (division by the geometric mean), and `product_factors` (the exact-real normalized factors multiply to 1). The model's normalized coefficients encode a weighted **mean**, resolving the docstring's informal “weighted sum” terminology through the source formula.

`Proofs/Intervals.lean` proves soundness of rational logarithm intervals from Mathlib's atanh-series remainder theorem, propagates intervals through the weighted sums and centering, and inverts logarithm bounds to bound the final exponentials. Each numerical log certificate uses 24 series terms. Python Decimal only proposes bounds: Lean checks the rational series inequalities and resulting error bounds. A mistaken Decimal answer would cause a failed proof, rather than becoming an assumption.

## Rechecking

Run from this directory, without Python optimization flags:

```sh
python3 verification/generate.py --check
lake clean proofs
lake build
```

`lake clean proofs` clears only this project's build directory, retaining the already built shared dependencies. No network is needed. The checked environment uses Lean 4.35.0, Mathlib v4.35.0, R 4.6.1, Python 3.14.8, and NumPy 2.5.4. The Lake library uses two Lean worker threads to bound simultaneous certificate checking. A clean build may take several minutes.

Success requires all three commands to exit zero. The Python command prints:

```
edgeR sample 1, gene 355: A-rank 232 upper cutoff 232 retained TRUE
edgeR: exact output bytes reproduced; retained genes: 65 79 77 300 89 95 81
RNAnorm sample 1, gene 355: A-rank 232.5 upper cutoff 232 retained False
RNAnorm kernel + adapters: exact output bytes reproduced; retained genes: [64, 79, 77, 283, 89, 95, 81]
PASS: exact input bytes, source replays, masks, and generated Lean models agree.
```

Whitespace in the R diagnostic may differ. `lake build` ends with `Build completed successfully` and prints the axiom dependencies of the main theorems. They contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, `Lean.ofReduceBool`, custom axioms, or native-decision axioms are used. All computational proof certificates use kernel reduction (`decide +kernel`) or proof-producing tactics.

## Review and trust boundary

For **R3**, read the decimal parser and artifact statements, and trust Lean's kernel, standard axioms, the installed Lean/Mathlib dependencies, and the file-byte comparison connecting the literal strings to the two shipped files. Neither R nor NumPy is needed for the logical arithmetic counterexample.

For **R1/R2's model theorems**, additionally read the TMM definitions, interval soundness proof, matrix/mask definitions, and the mathematical interpretation above. Lean checks the large generated rational certificates and their matrix connections. The certificate proposer is not trusted for arithmetic correctness. The external byte checker and source replays remain the bridge to the filesystem and actual selection computations.

To extend those model theorems to unconditional R1/R2, a reviewer would additionally have to establish the missing specification/implementation relation for trimming and source-language/dependency semantics. That relation has **not** been proved here. For the replay evidence, trust R's standard functions and libm, Python, NumPy, the AST extraction, and the explicitly listed RNAnorm adapters. Byte reproduction is an observation on this environment, not a theorem for all platforms or library versions.

The following sizes describe the delivered sources/data a reviewer may need to inspect; generated certificate numbers are checked by Lean rather than assumed:

| File | Lines | Bytes |
|---|---:|---:|
| `Proofs.lean` | 2 | 40 |
| `Proofs/Parsing.lean` | 39 | 1415 |
| `Proofs/Intervals.lean` | 135 | 5798 |
| `Proofs/Model.lean` | 44 | 1994 |
| `Proofs/TMM.lean` | 36 | 1492 |
| `Proofs/Artifacts.lean` | 20 | 1643 |
| `Proofs/InputData.lean` | 564 | 34359 |
| `Proofs/Certificates.lean` | 4450 | 186875 |
| `Proofs/Results.lean` | 68 | 3672 |
| `verification/generate.py` | 247 | 14041 |
| `verification/replay.R` | 24 | 1219 |
| `verification/replay.py` | 95 | 4045 |
| `verification/inputs.json` | 13 | 95061 |
| `verification/masks.json` | 1588 | 16905 |
| `lakefile.toml` | 13 | 287 |
| `lake-manifest.json` | 117 | 3536 |
| `lean-toolchain` | 1 | 25 |
| `CHECK.md` | 8 | 784 |

The original implementation and documentation files are frozen by `inputs.json`; their sizes are listed below:

| File | Lines | Bytes |
|---|---:|---:|
| `edgeR/R/normLibSizes.R` | 99 | 3950 |
| `edgeR/R/calcNormFactors.R` | 253 | 8216 |
| `edgeR/man/calcNormFactors.Rd` | 122 | 7033 |
| `rnanorm/between_sample.py` | 441 | 17490 |
| `rnanorm/utils.py` | 54 | 1670 |
| `edger-factors.R` | 5 | 259 |
| `rnanorm-factors.py` | 8 | 323 |
| `README.md` | 17 | 1642 |
