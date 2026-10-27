# Verification of the shipped TMM factor files

The decisive result is **R3 fails for every sample**. This is a statement about the exact decimal values in the two shipped files, independent of any model of TMM.

For R1 and R2, the absolute tolerance used below is **10⁻¹²**. Lean proves bounds at that tolerance for mathematical models using the trimming selections observed in each implementation. Executable replay connects those selections to the shipped sources. **Equivalence to the complete floating-point R/Python runtimes is not formally proved.** An exact-real model with exact average ranks gives different factors and supplies counterexamples to that interpretation of R1 and R2. These distinctions matter on this input; replacing floating-point operations with real operations changes the selected genes.

All sample and gene indices in Lean and the mask data are zero-based. Tables here use one-based sample numbers.

## R1: edgeR factors

The exact statement proved in `Proofs/Requirements.lean`, namespace `TMM`, is:

```lean
theorem r1_source_mask_model : ∀ i ∈ List.range 7,
    |(edgeFactors[i]! : ℝ) - factor edgeMasks i| ≤ ((1:ℚ)/10^12 : ℝ)
```

`edgeFactors` contains the exact decimal rationals from `edger-factors.txt`. `factor edgeMasks i` evaluates inverse-variance-weighted natural-log ratios for the selected count pairs, subtracts the mean of the seven weighted means, and exponentiates. The natural-log formulation cancels the base-2 logarithm/exponentiation in TMM. The weights and counts are exact rationals; logarithms and exponentials are Mathlib real functions. `Proofs/EdgeCertificates.lean` proves each factor enclosure using rational interval bounds, rather than treating a floating-point answer as a real-number oracle.

`verification/replay.R` sources the two shipped R implementation files and calls `normLibSizes` on `counts.tsv`. Its formatted output is compared to the raw bytes of `edger-factors.txt`. The replay passes byte for byte. The replay also checks that its selected gene indices agree with `edgeMasks` in the Lean model, through `verification/check.py`.

This establishes a tight bound for the source-selection model plus a direct execution check. It is **not** a formal proof of the R interpreter, its arithmetic/logarithm library, its rank routine, or the correspondence of the replay's mask extraction to all runtime semantics.

The exact-rank interpretation instead fails even a much looser tolerance:

```lean
theorem r1_exact_rank_counterexample :
    ((1:ℚ)/1000 : ℝ) < |(edgeFactors[0]! : ℝ) - factor idealMasks 0|
```

The input is the shipped `counts.tsv`, with default trims and reference sample 4. The exact-rank model puts its first factor in `[0.975527, 0.975528]`; the shipped first edgeR value is `0.99099942459293067`. Thus a proof for exact-real TMM cannot simply be substituted for a proof about the executed edgeR algorithm.

**Status:** the stated source-selection model bound is proved; execution reproduces the artifact; unconditional R1 conformance from the documentation and full runtime semantics remains unproved. Under the exact-rank interpretation specified below, R1 fails at tolerance 10⁻¹².

## R2: RNAnorm factors

The exact statement in `Proofs/Requirements.lean` is:

```lean
theorem r2_source_mask_model : ∀ i ∈ List.range 7,
    |(rnaFactors[i]! : ℝ) - factor rnaMasks i| ≤ ((1:ℚ)/10^12 : ℝ)
```

The model is the same weighted-log calculation, using RNAnorm's observed trimming selections. `rnaFactors` contains the exact decimal rationals from `rnanorm-factors.txt`.

The full RNAnorm package and its SciPy/pandas/scikit-learn dependencies are not shipped here. `verification/replay.py` executes the **unchanged ASTs** of the shipped `UQ`, `TMM`, and `remove_zero_genes` definitions with NumPy and explicit dependency shims. The shims use average ranks, linear percentiles, `exp(mean(log(x)))` for the geometric mean, and NumPy library-size sums. Validation, output configuration, and estimator mixins are reduced to the behavior needed for this valid array input. This replay reproduces all seven shipped factors with absolute error below `2e-15` (exactly equal on the tested environment), and its masks match `rnaMasks`.

The replay is a check of the source with those shims, **not** execution or verification of the original unshipped dependency stack. The shim definitions and source-to-model correspondence must be reviewed.

The exact-rank interpretation again fails:

```lean
theorem r2_exact_rank_counterexample :
    ((1:ℚ)/1000 : ℝ) < |(rnaFactors[0]! : ℝ) - factor idealMasks 0|
```

The same input gives exact-rank factor 1 in `[0.975527, 0.975528]`; the shipped RNAnorm value is `0.9816880015656044`.

**Status:** the source-selection model bound is proved and the shimmed source replay passes. Unconditional R2 conformance to the documentation and original Python dependency stack remains unproved. Under the exact-rank interpretation below, R2 fails at tolerance 10⁻¹².

## R3: agreement to ten decimal places

`Proofs/Counterexample.lean` proves, in namespace `TMM`:

```lean
theorem r3_all_samples_fail_rational : ∀ i ∈ List.range 7,
    (1:ℚ)/10^10 < |edgeFactors[i]! - rnaFactors[i]!|

theorem r3_all_samples_fail : ∀ i ∈ List.range 7,
    ((1:ℚ)/10^10 :ℝ) < |(edgeFactors[i]! : ℝ) - (rnaFactors[i]! : ℝ)|

theorem r3_rounded_decimals_fail : ∀ i ∈ List.range 7,
    ⌊edgeFactors[i]! * 10^10 + 1/2⌋ ≠ ⌊rnaFactors[i]! * 10^10 + 1/2⌋

theorem sample_one_difference : edgeFactors[0]! - rnaFactors[0]! =
    (931142302732627:ℚ)/10^17
```

These cover both absolute agreement within `10⁻¹⁰` and equality after rounding positive values to ten decimal places. The counterexample input is the supplied matrix itself. Sample 1 already disproves the claim:

| Sample | edgeR | RNAnorm | Absolute difference (approximate) |
|---|---|---|---|
| 1 | 0.99099942459293067 | 0.9816880015656044 | 0.00931142302732627 |
| 2 | 1.2772984068792248 | 1.2793096928626835 | 0.0020112859834587 |
| 3 | 1.1253076397204775 | 1.1270795948647565 | 0.001771955144279 |
| 4 | 0.95358597286325431 | 0.9550875280917844 | 0.00150155522853009 |
| 5 | 0.81337534218434382 | 0.8146561160553638 | 0.00128077387101998 |
| 6 | 0.92968280356711641 | 0.9311467198937998 | 0.00146391632668339 |
| 7 | 0.97359269251916547 | 0.9751257511415794 | 0.00153305862241393 |

**Status: refuted for the exact shipped artifacts.** No assumption about the TMM implementation is required for this comparison.

## Models, artifact binding, and the trimming discrepancy

`Proofs/Data.lean` uses `include_str` to read the three shipped data files. `counts_bytes` proves that the literal integer matrix in Lean renders to exactly `counts.tsv`. `edge_bytes` and `rna_bytes` pin the complete factor-file strings, including final newlines. `edge_decimals_checked` and `rna_decimals_checked` in `Proofs/Parsing.lean` prove, by kernel reduction, that the rational factor lists equal a total character-by-character decimal parser applied to those strings. Their exact statements are `edgeFactors = decimalLines edgeText` and `rnaFactors = decimalLines rnaText`. Decimal text denotes an exact rational; it is not silently rounded to a binary float.

`matrix_shape` checks 454 rows, seven columns, and no all-zero row. `library_sizes` checks `[1261, 621, 755, 1097, 1916, 1136, 1219]`. `default_reference` checks the unique closest-to-mean upper quartile is sample 4, using type-7 quartiles. `quartile_fallback_inactive` checks the quartiles exceed `10⁻²⁰`. `cutoff_inactive` proves every positive pair's exact-real A-value exceeds `-10¹⁰`. These facts support the matrix-specific model; they are not a general correctness theorem for arbitrary matrices.

`Proofs/Model.lean` defines the exact-rank interpretation. Positive count pairs are eligible. M-order compares `obs/ref` exactly; A-order compares `obs*ref` exactly. Twice the average rank is `2*(number strictly smaller) + (number equal) + 1`. The retained ranks are inclusively between `floor(0.3*n)+1` and `n-floor(0.3*n)` for M, and analogously with `0.05` for A. `exact_trimming` proves that the supplied `idealMasks` are precisely this calculation on the supplied matrix. The RNAnorm docstring's A-trimming bullet repeats `m_trim`; this interpretation uses its documented `a_trim` parameter and constructor default `0.05`, consistent with its code.

`ideal_enclosed` in `Proofs/IdealCertificates.lean` has the exact statement:

```lean
theorem ideal_enclosed (i : ℕ) (hi : i ∈ List.range 7) :
    (idealEndpoints i).Holds (factor idealMasks i)
```

`Box.Holds b x` means `(b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)`. Its endpoint constants give these exact-real factor intervals:

| Sample | Lower bound | Upper bound |
|---|---|---|
| 1 | 0.975527 | 0.975528 |
| 2 | 1.281083 | 1.281084 |
| 3 | 1.147754 | 1.147755 |
| 4 | 0.956411 | 0.956412 |
| 5 | 0.815785 | 0.815786 |
| 6 | 0.932437 | 0.932438 |
| 7 | 0.958280 | 0.958281 |

The observed retained-gene counts are:

| Calculation | Samples 1–7 |
|---|---|
| Exact ranks | 63, 79, 76, 283, 89, 95, 79 |
| edgeR replay | 65, 79, 77, 283, 89, 95, 81 |
| RNAnorm replay | 64, 79, 77, 283, 89, 95, 81 |

For example, matrix row 355 is `[13,3,5,8,9,5,23]`. In sample 1 versus reference 4, its exact A-rank is `232.5`, above the upper cutoff `232`. edgeR's floating-point calculation retains this row; RNAnorm's does not. Row 31 has an exact M-rank of `177.5`, outside the M cutoff `171`, but both floating-point calculations retain it after ties split. These are executable diagnostic observations, rather than additional Lean theorems. Geometric-mean rescaling propagates the different first raw factor into all seven normalized factors.

`verification/SHA256SUMS` pins the original input, both artifacts, both producer scripts, both implementations, and the documentation. The scripts never rewrite those files. `verification/check.py` checks the hashes, compares replay masks to both the JSON witnesses and Lean literals, and checks the exact-rank mask calculation independently. `verification/generate.py` can regenerate certificate proposals; it is not needed to check the delivered results. Incorrect proposed logarithm bounds or factor summaries are rejected by the Lean checks.

## Commands to check everything

Run from this directory, with the installed offline Lake dependencies:

```sh
python3 verification/check.py
lake clean proofs
lake build
lake env lean Proofs/Audit.lean
```

Use `lake clean proofs`, which cleans only this project's outputs; bare `lake clean` would also remove dependency builds. A fresh project build matters because `include_str` reads external files during elaboration. The hash/replay check also detects changed inputs and artifacts.

Success means:

1. The Python command exits zero, prints `All replay checks passed`, and reports the retained counts above. Assertions or hash mismatches are failures.
2. `lake build` exits zero with `Build completed successfully`, checking the root `Proofs.lean` and all proof modules. No network is required.
3. The audit exits zero and prints the axioms of the named results. The R3 comparison and rounding theorems use only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. Some data/finite-computation checks use `native_decide`; their generated computation axioms are discussed below. There must be no `sorryAx`.

Tested with Lean 4.35.0, Mathlib v4.35.0, Rscript 4.6.1, Python 3.14.8, and NumPy 2.5.4. The replay checks do not require SciPy, pandas, scikit-learn, or an installed edgeR/RNAnorm package.

## What must be trusted or reviewed

The mathematical proofs are checked by Lean. The numerical factor bounds, both exact-rank counterexample inequalities, the R3 inequalities/rounding checks, and the factor-file decimal parser checks have no native-decision axioms. Some matrix binding, shape, reference, and trimming-selection checks are marked `native_decide` and additionally trust Lean's native compiler/evaluator: Lean 4.35 reports generated axioms named `..._native.native_decide.ax_1_1` for these computations. These are explicitly part of the trust base, not kernel-reduced proofs of those computations. `Proofs/Audit.lean` exposes the dependencies. There are no handwritten axioms, `sorry`, or `admit` proofs. The real logarithm bounds use Mathlib's proved series remainder bound and rational inequalities; they do not assume decimal-library or libm accuracy.

Review `factor`, `weight`, rank definitions, decimal parsing, and the source-mask distinction to assess whether the formal statements express the desired requirements. The Python/R replays and their correspondence to full external runtimes are outside Lean. Trusting the source-selection interpretation of R1/R2 requires reviewing that bridge; the unresolved runtime proof is not hidden behind the numerical bounds.

Sizes below are source sizes, excluding generated build products and logs. Definitions and generated constants are included because they determine what is proved.

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs.lean` | 2 | 49 | Library entry point |
| `Proofs/Intervals.lean` | 132 | 6665 | Interval operations and real-log bounds |
| `Proofs/Logs.lean` | 271 | 18723 | Generated logarithm certificates |
| `Proofs/Data.lean` | 29 | 24082 | Matrix, file binding, decimals, masks |
| `Proofs/Model.lean` | 158 | 6560 | TMM definitions and interval soundness |
| `Proofs/IdealCertificates.lean` | 138 | 10053 | Exact-rank factor certificates |
| `Proofs/EdgeCertificates.lean` | 138 | 11116 | edgeR source-mask certificates |
| `Proofs/RnaCertificates.lean` | 138 | 10887 | RNAnorm source-mask certificates |
| `Proofs/Certificates.lean` | 3 | 93 | Certificate imports |
| `Proofs/Requirements.lean` | 92 | 3915 | Requirement statements and A-cutoff proof |
| `Proofs/Counterexample.lean` | 22 | 728 | Unconditional artifact comparison |
| `Proofs/Parsing.lean` | 24 | 950 | Total decimal parser and kernel-checked file-to-value binding |
| `Proofs/Audit.lean` | 17 | 621 | Axiom inspection commands |
| `verification/check.py` | 57 | 2702 | Byte and replay correspondence checks |
| `verification/replay.py` | 79 | 2698 | Source AST execution and dependency shims |
| `verification/replay.R` | 21 | 936 | Direct shipped R source execution |
| `verification/generate.py` | 193 | 10484 | Optional witness generator |
| `verification/edger-masks.csv` | 7 | 2881 | Optional R replay trace used by the witness generator |
| `verification/masks.json` | 2351 | 25035 | Readable discrete mask witnesses |
| `verification/SHA256SUMS` | 12 | 1016 | Original-file byte identities |

The shipped source/documents to compare with the models are `edgeR/R/normLibSizes.R` (99 lines, 3,950 bytes), `edgeR/R/calcNormFactors.R` (253 lines, 8,216 bytes), `edgeR/man/calcNormFactors.Rd` (122 lines, 7,033 bytes), `rnanorm/between_sample.py` (441 lines, 17,490 bytes), and `rnanorm/utils.py` (54 lines, 1,670 bytes). The producer scripts are 582 bytes combined. The matrix is 454 lines/6,518 bytes; the artifacts are seven lines each, 138 and 133 bytes. `README.md` and `CHECK.md` are 1,642 and 784 bytes.

Installed dependencies also belong to the trust base: Lean's kernel and any native evaluator/compiler used by `native_decide`, Mathlib's definitions/theorems, and, for the replay evidence, Python, NumPy, R, and the operating system. In this environment `/opt/lean` occupies about 2.9 GiB including binaries/build material, and the Mathlib `Mathlib/` source tree about 97 MiB. The audit separates the Lean theorem dependencies from the external replay evidence. The generated witnesses are checked data; the interpretation of the model as documentation/source semantics remains a human review obligation.
