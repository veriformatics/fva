# Verification of the shipped TMM factors

R3 is false. The first entries in the two original output files differ by exactly
**0.00931142302732627**, far beyond ten decimal places.

R1 and R2 have machine-checked bounds against the explicit exact-real TMM model
below: absolute error **< 0.023** for every edgeR entry and **< 0.021** for every
RNAnorm entry. These are the tolerances stated for the positive results. They are
coarse bounds, not evidence of accuracy to ten decimal places. Lean also proves
that **both files fail an absolute tolerance of 1e-10 on sample 1 in this model**.
The distinction between this model and floating-point execution matters here.

No original data, output, implementation, documentation, or project configuration
file was changed. The proofs concern this one shipped matrix and these output
files, not all possible matrices.

## Requirements and exact checked statements

All theorem names below are in namespace `Verification`. Sample indices in Lean
are zero-based; `Fin 7` ranges over all seven samples.

### R1

[Proofs/Results.lean](Proofs/Results.lean) proves:

```lean
theorem R1_at_0023 (j : Fin 7) :
    |(edgeFactors[j.val]!:ℝ) - factor j.val| < 23/1000
```

Here `edgeFactors` parses the actual `edger-factors.txt` decimal text as rational
numbers, subsequently embedded in the reals. `factor` is the exact-real model
defined in [Proofs/Model.lean](Proofs/Model.lean). Thus every entry satisfies the
stated absolute tolerance 0.023 under that interpretation of documented TMM.
This is not a proof of faithful floating-point execution of the R source.

Separately, `Rscript verification/replay_edger.R` sources both shipped R files,
runs `normLibSizes(m, method="TMM")` with the default arguments, formats with the
producer's `%.17g`, and checks **exact equality of all output bytes**, including
the final newline. It passes with the installed R. This is execution evidence
for the concrete implementation, not a formal semantics proof of R or libm.

### R2

[Proofs/Results.lean](Proofs/Results.lean) proves:

```lean
theorem R2_at_0021 (j : Fin 7) :
    |(rnaFactors[j.val]!:ℝ) - factor j.val| < 21/1000
```

`rnaFactors` similarly parses the actual `rnanorm-factors.txt`. Every entry
satisfies absolute tolerance 0.021 against the model. The precise interpretation
of the docstring's trimming procedure is stated below.

`python3 verification/replay_rnanorm.py` additionally executes the **actual AST
bodies** of the shipped `remove_zero_genes` and `TMM._get_norm_factors` methods.
NumPy is installed; SciPy, sklearn, and the complete RNAnorm package are not.
The script substitutes local average ranks, library sums, and a null configuration
context, and computes the documented upper-quartile reference and geometric
rescaling. Its maximum difference from the shipped factors is zero on this
machine (the assertion allows 1e-14). This is a partial dependency-substituted
replay, not a verified execution of the complete RNAnorm package.

### Fine-tolerance counterexamples for R1 and R2

The input is the unchanged `counts.tsv`; the witness is its first sample and the
first entry of each factor file. [Proofs/Results.lean](Proofs/Results.lean) proves:

```lean
theorem fine_tolerance_failure :
    |(edgeFactors[0]!:ℝ) - factor 0| > (1:ℝ)/10^10 ∧
    |(rnaFactors[0]!:ℝ) - factor 0| > (1:ℝ)/10^10
```

These are counterexamples at absolute tolerance 1e-10 **against the exact-real
model**, not counterexamples to the claim that the output files were produced by
their floating-point implementations. The replays support their provenance.

### R3

[Proofs/Results.lean](Proofs/Results.lean) proves directly about the parsed files:

```lean
theorem R3_counterexample :
    edgeFactors[0]! - rnaFactors[0]! =
      (931142302732627:ℚ)/100000000000000000 ∧
    |edgeFactors[0]! - rnaFactors[0]!| > (1:ℚ)/10^10
```

It also contains this small kernel-checked arithmetic witness, which does not
use `native_decide` or depend on the TMM model:

```lean
theorem R3_decimal_witness :
    (99099942459293067/100000000000000000:ℚ) -
      9816880015656044/10000000000000000 =
      931142302732627/100000000000000000 ∧
    (99099942459293067/100000000000000000:ℚ) -
      9816880015656044/10000000000000000 > 1/10^10
```

The two fractions are exactly the first decimal strings
`0.99099942459293067` and `0.9816880015656044`. They also round to different values
at ten decimal places. This refutation needs no assumption about which TMM
implementation is correct.

## Model, numerical bounds, and the tie issue

The documentation does not fully specify floating-point evaluation order or
rounding. [Proofs/Model.lean](Proofs/Model.lean) supplies an explicit mathematical
interpretation, using the included implementations to specify the details:

1. Read the integer matrix; library sizes are column sums. Remove all-zero rows.
2. Use the linearly interpolated 75th percentile divided by library size, choosing
   the column closest to the mean. `reference_choice` checks that column 4 is
   uniquely closest. `data_shape` checks 454 rows, seven columns, and library
   sizes `[1261,621,755,1097,1916,1136,1219]`.
3. For each sample/reference comparison, remove pairs with a zero count. Rank M
   by the exact count ratio, and A by the exact count product. Positive scaling
   and logarithms preserve these orders. Ties receive average ranks.
4. Keep inclusive ranks from `floor(0.3*n)+1` to `n-floor(0.3*n)` for M, and from
   `floor(0.05*n)+1` to `n-floor(0.05*n)` for A. The RNAnorm docstring's `a_trim`
   parameter and implementation specify the A trim; its outline repeats
   `m_trim` in that bullet.
5. Weight by the inverse of
   `(L_o-o)/(L_o*o) + (L_r-r)/(L_r*r)`. Compute the weighted mean of natural logs
   of `(o/L_o)/(r/L_r)`. Natural logs cancel the base-2 conversion and exponent.
6. Subtract the mean of the seven weighted log factors and exponentiate. The
   reference comparison has raw log factor zero.

`dataset_conditions` checks positive variances, that every positive pair's
normalized count product exceeds 2^-24, and that each non-reference comparison
has a ratio greater than 2. Thus the A cutoff -1e10 removes no positive pair
(A > -12), and the edgeR near-zero M shortcut applies only to the reference.
The connection of these definitions to the prose/source is a reviewer obligation;
there is no formal translation or equivalence proof for R, Python, IEEE-754, or
their dependencies. A claim of formal floating-point correctness for R1/R2
remains unproved for that reason.

`factor_enclosures` in [Proofs/Results.lean](Proofs/Results.lean) has the exact
statement:

```lean
theorem factor_enclosures (j : Fin 7) :
    (lows[j.val]! : ℝ) < factor j.val ∧
    factor j.val < (highs[j.val]! : ℝ)
```

The rational endpoints defined in `Proofs/Certificates.lean` are:

| Sample | Exact-model factor, certified open interval |
|---|---|
| 1 | (0.97552, 0.97554) |
| 2 | (1.28107, 1.28110) |
| 3 | (1.14774, 1.14777) |
| 4 | (0.95640, 0.95643) |
| 5 | (0.81577, 0.81580) |
| 6 | (0.93242, 0.93246) |
| 7 | (0.95827, 0.95830) |

The bounds are rigorous real inequalities, not decimal-library approximations.
`forms_match` checks the complete selected genes and rational weights against
computations from the matrix. `certificates_valid` checks all proposed logarithm
certificates. [Proofs/LogBounds.lean](Proofs/LogBounds.lean) proves their soundness:
rescale each positive argument as `u * 2^k`, with `1/2 ≤ u ≤ 1`; bound its log
using 24 Taylor terms and a remainder bound, plus Mathlib's bound for log 2.
Each rounded logarithm has certified absolute error at most 1e-6. Propagating
these bounds through the weighted sums and comparing to bounded endpoint logs
proves the factor enclosures by monotonicity of exp.

Rounding before ranking is significant. `exact_tie_witness` checks that rows
163 and 355 have sample-1/reference counts `(8,13)` and `(13,8)`, respectively,
with product 104. There are 244 positive pairs; their exact A rank is 232.5,
above the retained upper rank 232. The R replay prints:

```text
Rows 163,355: sum-of-logs A ranks = 233 232 ; log-of-product A ranks = 232.5 232.5
```

Thus the mathematically equivalent A formulas in the two sources can select
different genes after floating-point rounding. This is a concrete boundary
diagnostic, not a proof that this pair explains every discrepancy.

## Connection to exact shipped bytes

`Proofs/Model.lean` uses `include_str` to embed the actual three input/output
files during elaboration. The parsers operate on those embedded strings.
[Proofs/Artifacts.lean](Proofs/Artifacts.lean) contains complete expected string
literals and proves by `rfl`:

```lean
theorem counts_bytes : countsBytes = expectedCountsBytes
theorem edge_bytes : edgeBytes = expectedEdgeBytes
theorem rna_bytes : rnaBytes = expectedRnaBytes
```

These pin the text, including every tab, decimal spelling, and final newline;
the files are ASCII, so the string equalities also pin their bytes. The parser
uses defaults for malformed input, but these literal equalities restrict the
results to the original well-formed files. There is no unspecified external
input assumption.

[verification/inputs.sha256](verification/inputs.sha256) additionally pins all
original requirements, data, factors, producer scripts, implementation files,
documentation, and Lake/toolchain configuration. The fresh check below rebuilds
only this project's outputs so cached modules cannot substitute for reading the
current artifact files.

## Reproduce every result, without a network

From this directory, with the installed tools and built Mathlib:

```sh
python3 verification/check.py
```

This runs the following exact commands, stopping on any nonzero exit:

```sh
sha256sum -c verification/inputs.sha256
python3 verification/generate.py --check
lake clean proofs
lake build
Rscript verification/replay_edger.R
python3 verification/replay_rnanorm.py
```

`lake clean proofs` removes only this package's build outputs, preserving the
installed dependencies. A fresh build may take several minutes. Success means
all hashes say `OK`, certificate regeneration says `PASS`, Lake says
`Build completed successfully`, both replays say `PASS`, and the final line is:

```text
ALL VERIFICATION CHECKS PASSED (R3 is refuted; see VERIFICATION.md).
```

Passing verifies the stated bounds and counterexamples; it does not mean R3 is
true. `verification/check.log` records the completed local run. The build prints
axiom dependencies for the principal results, including the independent R3
arithmetic witness.

## What must be read and trusted

The formal results use Lean 4.35.0 and Mathlib v4.35.0. There are no `sorry` or
`admit` proofs. The analytic arguments are kernel-checked. Finite matrix,
certificate, and parsed-artifact computations use Lean's `native_decide` and
therefore additionally trust Lean's native compiler/evaluator and runtime.
In this Lean version these appear in `#print axioms` as generated
`<theorem>._native.native_decide.ax_1_1` declarations. They must not be mistaken
for kernel-reduced arithmetic. In particular, R1/R2 depend on native checks
`forms_match`, `certificates_valid`, `endpoints_valid`, `numeric_enclosures`, and
`artifact_numeric_bounds`. `R3_decimal_witness` has only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies.

A reviewer must assess the model's correspondence to the documentation and
source, especially exact ties versus floating-point ranks. Neither the generator
nor its Decimal logarithms need be trusted for formal soundness: Lean checks the
proposed data against the matrix and proves the analytic bounds. The replays
add trust in R/libm and NumPy/Python plus the stated dependency substitutions;
they are supplementary evidence only.

Source sizes (lines / bytes):

| File | Size | Review role |
|---|---:|---|
| `Proofs.lean` | 2 / 46 | Imports all results into the default target |
| `Proofs/Model.lean` | 77 / 2,885 | Parsers and mathematical TMM definition; essential interpretation |
| `Proofs/LogBounds.lean` | 113 / 4,600 | Log-certificate soundness and error propagation |
| `Proofs/Results.lean` | 171 / 7,197 | Finite checks, all-factor bounds, and counterexamples |
| `Proofs/Artifacts.lean` | 17 / 10,572 | Full expected text and literal-equality proofs |
| `Proofs/Certificates.lean` | 599 / 134,929 | Generated rational data, checked rather than trusted |
| `verification/generate.py` | 78 / 3,525 | Optional deterministic certificate regeneration |
| `verification/check.py` | 17 / 668 | Command orchestration; inspect or run commands individually |
| `verification/inputs.sha256` | 15 / 1,262 | Original-file identity manifest |
| `verification/replay_edger.R` | 19 / 932 | Exact-byte R replay and boundary diagnostic |
| `verification/replay_rnanorm.py` | 51 / 2,136 | Extracted numerical-method replay and dependency substitutes |

The original interpretation sources are `README.md` (17 / 1,642),
`edgeR/man/calcNormFactors.Rd` (122 / 7,033), `edgeR/R/normLibSizes.R`
(99 / 3,950), `edgeR/R/calcNormFactors.R` (253 / 8,216),
`rnanorm/between_sample.py` (441 / 17,490; the TMM class starts at line 190),
and `rnanorm/utils.py` (54 / 1,670). The full count input is 6,518 bytes;
the factor files are 138 and 133 bytes. These are data under verification,
not assumed-correct expected answers.
