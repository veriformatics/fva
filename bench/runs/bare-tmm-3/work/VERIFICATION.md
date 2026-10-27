# Verification of the shipped TMM factor files

The input is the **entire shipped `counts.tsv`**, not a synthetic matrix. I use an
absolute tolerance of **10⁻⁶** for R1 and R2. R3 fails outright on the shipped
bytes. R1 and R2 fail against the explicit **real-arithmetic, average-tie-rank
TMM model** below. Both files nevertheless reproduce their respective
floating-point computations. These are different results: reproducing a
floating-point computation does not establish its error relative to mathematical
TMM when rounding changes trimming decisions.

The documentation is prose, not a complete formal specification. In particular,
it does not fix tie handling; RNAnorm's procedure also says `m_trim` for A while
its parameter description and implementation use `a_trim`. The R1/R2
counterexamples use the source's average-rank convention and defaults
`m_trim = 0.3`, `a_trim = 0.05`. They are conditional on this stated interpretation
of documented TMM. I have **not** proved an interpretation-independent failure
of R1/R2, nor a formal refinement theorem from R/Python floating-point semantics.
If “TMM” is defined operationally as each source's floating-point computation,
the reproduction results below support R1/R2 instead. R3 needs no such choice.

## R1 — edgeR factors

`Proofs/Results.lean`, namespace `TMMVerification`, contains these exact
statements (Lean's `ℝ` is the mathematical real numbers):

```lean
theorem R1_counterexample :
    (1/1000 : ℝ) < |(edgeFactors[2]! : ℝ) - exactFactor 2|

theorem R1_fails : ¬ ∀ j ∈ indices,
    |(edgeFactors[j]! : ℝ) - exactFactor j| ≤ (1/1000000 : ℝ)
```

All indices are zero based. Sample 3 is the witness. Its shipped decimal is
`1.1253076397204775`. Lean proves the mathematical factor is **greater than
1.13**, so the chosen 10⁻⁶ tolerance is exceeded, by more than 0.001.

A separate execution check, `Verification/reproduce.R`, sources the shipped
`edgeR/R/normLibSizes.R` and `edgeR/R/calcNormFactors.R`, runs the default TMM
calculation and compares the `sprintf("%.17g", ...)` output, including newlines,
with the artifact. It reproduces **all 138 bytes exactly** on this environment.
This is an execution result, not an IEEE-754 correctness proof or proof about
an independently installed edgeR package.

## R2 — RNAnorm factors

The same file and namespace contain:

```lean
theorem R2_counterexample :
    (1/1000 : ℝ) < |(rnaFactors[2]! : ℝ) - exactFactor 2|

theorem R2_fails : ¬ ∀ j ∈ indices,
    |(rnaFactors[j]! : ℝ) - exactFactor j| ≤ (1/1000000 : ℝ)
```

Sample 3 is again the witness. Its shipped decimal is `1.1270795948647565`;
the same certified lower bound of 1.13 gives error greater than 0.001.

`Verification/reproduce_rnanorm.py` reproduces **all 133 bytes exactly** by
executing the shipped `TMM._get_norm_factors` method body. NumPy is installed;
SciPy, sklearn and the complete RNAnorm package are not. The script therefore
extracts that method with `ast`, removes its type annotations, and supplies
explicit adapters for library sums, average ranks, zero-gene removal and the
configuration context. It computes the reference and geometric normalization
outside the method. Its upper-quartile adapter checks that the adjacent
interpolation values are equal for this matrix. These adapters are disclosed
and must be reviewed; this is **not** execution of the complete RNAnorm 2.2.0
package or a proof of its external dependencies.

The real-arithmetic models coincide here: both choose sample 4 as reference,
use the same trimming fractions, inverse variances and geometric rescaling.
For this input the edgeR A cutoff is inactive. No claim is made that the two
implementations agree on arbitrary matrices.

## R3 — equality to at least ten decimal places

These statements require no TMM model:

```lean
theorem R3_counterexample :
    (9/1000 : ℝ) < |(edgeFactors[0]! : ℝ) - (rnaFactors[0]! : ℝ)|

theorem R3_fails : ¬ ∀ j ∈ indices,
    |(edgeFactors[j]! : ℝ) - (rnaFactors[j]! : ℝ)| ≤ (1/10000000000 : ℝ)
```

The first lines are `0.99099942459293067` and `0.9816880015656044`. Their exact
absolute difference is

```text
931142302732627 / 100000000000000000 = 0.00931142302732627
```

This exceeds 10⁻¹⁰ by many orders of magnitude. Rounding both values to ten
places also produces different numbers (`0.9909994246` and `0.9816880016`).
Even just these two artifact lines refute R3; the supplied full matrix is the
input that generated them.

## Model and connection to the implementation

`Proofs/Model.lean` embeds the three data files directly with `include_str`.
A character-list parser interprets counts as natural numbers and the factor
lines as **exact decimal rationals**, not binary floats. `indices` is
`List.range 7`. `input_checked` proves from these embedded files that there are
454 rows of 7 entries, 7 factors per file, no removed all-zero rows, library sums
`[1261,621,755,1097,1916,1136,1219]`, the seven exact upper quartiles, and reference
index 3. `Verification/check_artifacts.py` additionally checks the byte grammar
and identifies the original shipped files with fixed SHA-256 hashes.

The model follows the default branches relevant to this matrix:

1. Sum the counts for library sizes; remove all-zero genes. Use the default
   type-7 upper quartile and choose its normalized value nearest their mean.
   RNAnorm's preliminary geometric scaling of quartiles does not change this
   nearest-mean choice in real arithmetic. The low-quartile fallback is inactive.
2. For each sample/reference pair remove genes having a zero in either member.
   Rank M by `obs/ref`, and A by `obs*ref`. Strict monotonicity of the logarithm
   makes these the mathematical M/A ranks. Use average ranks of ties and inclusive
   cutoffs `floor(n*trim)+1` through `n-floor(n*trim)`. All positive-count
   proportions are at least `1/1916`, so all finite A-values exceed −12 and hence
   the edgeR cutoff −10¹⁰. The reference's raw factor is 1.
3. Weight each retained gene by the reciprocal of
   `(1/obs - 1/lib.obs) + (1/ref - 1/lib.ref)`.
   Take the weighted mean of log normalized count ratios and exponentiate.
4. Subtract the mean of the seven log factors before exponentiating, equivalent
   to dividing all factors by their geometric mean. Natural logs replace log₂
   without changing the result: the base conversion cancels exponentiation by 2.

`rawTerms` represents each weighted log factor as a list of coefficients of
natural logarithms of integer counts/library sizes. `centeredTerms` performs
step 4; `exactFactor` is its real exponential. This is a **manually written
mathematical model**, not mechanically extracted R/Python code. Its agreement
with the intended prose and the relevant source branches is a review obligation.

`trimming_checked` checks all seven exact trimming sets' sizes:

```text
positive pairs: 244, 195, 205, 300, 259, 244, 227
retained genes:  63,  79,  76, 283,  89,  95,  79
```

`Proofs/LogBounds.lean` proves certified logarithm enclosures using Mathlib's
`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add`: eight terms of
the atanh series plus a rigorous remainder, after power-of-two range reduction.
`Proofs/Certificates.lean` supplies and checks the rational certificates.
Signed linear combinations preserve these enclosures. In `Proofs/Results.lean`,
`centered_log_lower_checked` establishes

```lean
(13/100 : ℚ) < lowerTerms (centeredTerms 2)
```

The proved enclosure lemma and `Real.add_one_le_exp` then establish

```lean
theorem exact_third_factor_gt : (113/100 : ℝ) < exactFactor 2
```

No floating-point log/exp result is used in this proof. The optional independent
Decimal diagnostic prints approximately `1.1477549719101462` for this factor;
these diagnostic digits are not the claimed certified enclosure.

The floating-point discrepancy has a concrete trimming witness. In sample 1
versus reference 4, gene rows 163 and 355 have counts `(8,13)` and `(13,8)`.
Their mathematical A-values are equal because both products are 104. Their
average A-rank is 232.5, outside the upper cutoff 232. edgeR evaluates A as the
sum of two logarithms; RNAnorm evaluates the logarithm of a product. The former
rounding path splits this tie and retains row 355. The R reproduction diagnostic
keeps every other calculation fixed and shows 65 versus 64 retained genes when
switching these two A formulas. Exact mathematical M ties are also split by
floating division/log evaluation, explaining why *both* numerical paths can
differ from the exact-tie model. R3 is established by the artifact values,
independently of this explanation.

## Replay commands and success criteria

Run from this directory, offline, using the installed Lean 4.35.0 / Mathlib
v4.35.0 Lake project:

```sh
python3 Verification/check_artifacts.py
lake clean proofs
lake build
Rscript Verification/reproduce.R
python3 Verification/reproduce_rnanorm.py
python3 Verification/exact_diagnostic.py
```

The first command must print its two `PASS` lines and exit 0. `lake clean proofs`
removes only this project's cached build so the embedded bytes are read afresh.
`lake build` must exit 0 with `Build completed successfully`; it checks all
imported proof modules and prints the axioms of `R1_fails`, `R2_fails` and
`R3_fails`. The next two commands must print their `PASS` messages and exit 0;
the R command also prints the trimming diagnostic. The last command is optional
and prints illustrative high-precision factors. All the counterexample theorems
are **expected successes** of verification, not failed tests.

`Verification/generate_certificates.py` is optional: running it regenerates
`Proofs/Certificates.lean`; rerun `lake build` afterwards. The generator uses
ordinary numerical logarithms to propose endpoints, but Lean independently
checks every endpoint with exact rational inequalities. It is not trusted for
the proofs. No command rewrites the shipped matrix, source or factor files.

## Trust boundary and review size

There are no `sorry`, `admit`, or user-supplied mathematical axioms. R3 and the
log-certificate checker use kernel reduction (`decide +kernel`). R1/R2 also use
`native_decide` for the large finite matrix/trimming computation and the final
rational enclosure computation. Thus their printed dependencies include
`trimming_checked._native.native_decide.ax_1_1` and
`centered_log_lower_checked._native.native_decide.ax_1_1`, in addition to Lean's
standard `propext`, `Classical.choice` and `Quot.sound`. The native evaluator,
compiler and runtime are part of their trusted computing base; these are not
pure kernel-only reductions. `input_checked` also uses native evaluation.
R3's printed dependencies contain only the three standard axioms.

The main human review is the interpretation of the prose and the model's
correspondence to it, especially tie policy. Lean checks the mathematical
reasoning and computations within that model; it does not prove a formal
semantics for R, NumPy, SciPy or sklearn, or historical package provenance.
The reproduction results additionally trust their interpreters, numerical
libraries and the RNAnorm adapters. SHA-256 binding additionally trusts Python's
hashlib and the fixed manifest; hashes identify bytes rather than prove TMM.

Local files to review (UTF-8 bytes, newline-inclusive line counts):

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs.lean` | 1 | 22 | Proof entry point |
| `Proofs/Model.lean` | 107 | 4074 | Parsers and exact TMM specification |
| `Proofs/LogBounds.lean` | 65 | 2633 | Generic certified-log proof |
| `Proofs/Certificates.lean` | 72 | 4021 | Checked certificate data and lookup |
| `Proofs/Results.lean` | 119 | 4931 | Matrix checks, real bounds and R1–R3 theorems |
| `Verification/check_artifacts.py` | 22 | 1101 | Byte binding and grammar checks |
| `Verification/artifacts.json` | 50 | 1567 | Hash/size manifest for all 12 shipped files |
| `Verification/reproduce.R` | 29 | 1243 | R source execution and A-tie diagnostic |
| `Verification/reproduce_rnanorm.py` | 53 | 2322 | Python source-body execution and adapters |
| `Verification/exact_diagnostic.py` | 36 | 1475 | Optional numerical illustration |
| `Verification/generate_certificates.py` | 31 | 1471 | Optional, untrusted certificate generator |

The build configuration is `lean-toolchain` (1 line, 25 bytes), `lakefile.toml`
(12 lines, 264 bytes), and `lake-manifest.json` (117 lines, 3,536 bytes). The
manifest pins Mathlib to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0). The directly used analytic
foundation includes Mathlib's `Analysis/SpecialFunctions/Log/Deriv.lean`
(426 lines, 18,797 bytes), `Analysis/SpecialFunctions/Log/Basic.lean`
(713 lines, 28,165 bytes), and `Analysis/Complex/Exponential.lean`
(713 lines, 28,484 bytes). Their proofs and transitive dependencies are part of
the installed Mathlib library; the Lean kernel and native backend remain the
external trusted implementation. The local code imports `Mathlib` as a whole.

The shipped documentation/source review consists of `README.md` (1,642 bytes),
`edgeR/man/calcNormFactors.Rd` (7,033), `edgeR/R/normLibSizes.R` (3,950),
`edgeR/R/calcNormFactors.R` (8,216), `rnanorm/between_sample.py` (17,490), and
`rnanorm/utils.py` (1,670). The original producer scripts are 259 and 323 bytes.
The count input is 6,518 bytes; the two output artifacts are 138 and 133 bytes.
All shipped file sizes and hashes, including `CHECK.md`, are in the manifest.

Exact artifact SHA-256 values:

```text
counts.tsv          aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5
edger-factors.txt   df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943
rnanorm-factors.txt 62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d
```
