# Verification of the shipped TMM factors

Tolerance: **absolute error at most `10^-10` per factor**. Samples below use the README's one-based order; Lean indices start at zero.

R3 is false for the actual decimal files, independently of any model of TMM. For R1 and R2, the exact-real, average-rank interpretation of TMM is refuted at this tolerance. Floating-point execution instead reproduces the files. The distinction matters: ranking is discontinuous at ties, and the documentation does not specify floating-point tie-breaking. Thus the R1/R2 results below are explicitly about the mathematical model, not a claim that the files were incorrectly copied from those implementations.

## R1

`Proofs/Results.lean`, namespace `Verification`, proves exactly:

```lean
theorem R1_fails : ¬ (∀ j ∈ List.range 7,
    |factor 1 20 j - (edge[j]! : ℝ)| ≤ tolerance)
```

The stronger, localized counterexample in the same file is:

```lean
theorem R1_pair_fails :
    ¬ (|factor 1 20 2 - (edge[2]! : ℝ)| ≤ tolerance ∧
       |factor 1 20 3 - (edge[3]! : ℝ)| ≤ tolerance)
```

Input: the complete shipped `counts.tsv`, using its third sample against its fourth (reference) sample. At least one of the third and fourth shipped factors is outside the stated tolerance of this model. This is a pair counterexample; the proof does not identify which individual normalized factor fails.

The proof checks that the library sizes are `[1261,621,755,1097,1916,1136,1219]`, the upper-quartile rule selects sample 4, and the tiny-quartile reference fallback is inapplicable. Exact average ranks retain 76 pairs for sample 3. A rational logarithm bound proves that its unnormalized natural-log factor exceeds `181/1000`. Since `exp(x) ≥ 1+x`, after any common geometric-mean normalization the factors satisfy `factor[3] > 1.181 * factor[4]`. Exact rational comparison of the file's third and fourth decimals contradicts this inequality even after allowing `10^-10` error in both values.

For comparison, the supplementary replay executes the supplied edgeR R functions and reproduces `edger-factors.txt` exactly on this machine. That execution is evidence about the floating-point implementation; it is not a formal proof of R or its numerical libraries.

## R2

`Proofs/Results.lean` proves exactly:

```lean
theorem R2_fails : ¬ (∀ j ∈ List.range 7,
    |factor 1 20 j - (rna[j]! : ℝ)| ≤ tolerance)

theorem R2_pair_fails :
    ¬ (|factor 1 20 2 - (rna[2]! : ℝ)| ≤ tolerance ∧
       |factor 1 20 3 - (rna[3]! : ℝ)| ≤ tolerance)
```

The input and mathematical obstruction are the same as for R1. The default model uses M trim `3/10`, A trim `1/20`, inverse-variance weights, and common geometric-mean rescaling.

The RNAnorm class docstring has an internal inconsistency: its procedure bullet says to trim A with `m_trim`, whereas the `a_trim` parameter description and implementation use `a_trim=0.05`. The alternate literal reading, trimming both tails of both M and A by `0.3`, also fails:

```lean
theorem R2_literal_fails : ¬ (∀ j ∈ List.range 7,
    |factor 3 10 j - (rna[j]! : ℝ)| ≤ tolerance)
```

For that reading the checked sample-3 retained list has 30 pairs, and the same lower bound suffices.

The supplementary Python replay executes the supplied `_get_norm_factors` method body with small replacements for unavailable SciPy/sklearn utilities. It reproduces `rnanorm-factors.txt` exactly here. It does **not** execute or verify the entire RNAnorm package, estimator validation, or dependency stack.

## R3

`Proofs/Results.lean` proves exactly:

```lean
theorem R3_fails : ¬ (∀ j ∈ List.range 7,
    |(edge[j]! : ℝ) - (rna[j]! : ℝ)| ≤ tolerance)
```

`Proofs/Artifacts.lean` proves the stronger exact-decimal results:

```lean
theorem R3_all_seven_gaps : ∀ i ∈ List.range 7,
    (1 : ℚ) / 1000 < |edge[i]! - rna[i]!|

theorem R3_first_gap_exact : edge[0]! - rna[0]! =
    (931142302732627 : ℚ) / 10^17
```

The first values are `0.99099942459293067` and `0.9816880015656044`, separated by exactly `0.00931142302732627`. Every corresponding pair differs by more than `0.001`. This refutes both an absolute-error interpretation of ten-decimal agreement and agreement after rounding to ten decimal places. No logarithm evaluation, reference choice, or trimming model is needed for this result.

## Definitions and connection to the artifacts

`Proofs/Model.lean` embeds all three input/output files using `include_str`, then parses their actual characters. Counts are natural numbers; output decimals are exact rationals, not binary floating-point approximations. `Proofs/Artifacts.lean` additionally proves `edge_exact_bytes` and `rna_exact_bytes`, which state the complete output strings including final LF bytes, and proves both files have seven values.

`dimensions`, `count_format`, and `no_zero_rows` in `Proofs/Computation.lean` check the 454-by-7 shape, nonempty digit-only count cells, and that removing all-zero rows changes nothing. `default_selection` and `literal_selection` check the complete retained lists, with multiplicities and order preserved.

The exact-real model in `Proofs/Model.lean` is a manual mathematical transcription, not extracted semantics for R/Python:

- Library size is the column sum. The reference minimizes absolute distance from mean upper-quartile/library-size ratio, using the first minimum. Quartiles use linear interpolation at `3*(n-1)/4`. The proved reference is sample 4; the model's pair calculations consequently use that column.
- Ignore a gene when either member of the pair is zero. Rank M by the exact rational key `x/y`, and A by the exact integer key `x*y`. Common library-size constants and strictly increasing logarithms preserve these orders and ties. `Proofs/Semantics.lean` proves the real M/A strict-order equivalences (`m_order`, `a_order`); equality follows by applying the strict-order equivalences in both directions. Dividing logs by positive `log 2` also preserves order.
- Twice the average rank is `2*(number strictly below)+(number equal)+1`. Retain inclusive ranks from `floor(n*trim)+1` through `n-floor(n*trim)` on both axes.
- The precision weight is the reciprocal of `(L-x)/(L*x)+(R-y)/(R*y)`. The weighted mean of natural logs is equivalent to a weighted mean of base-2 logs followed by `2^mean`. `factor a d j` is `exp(rawLog a d j - meanLog a d)`, with A trim `a/d`. Self comparison has raw log zero.
- All positive count pairs here are well above edgeR's A cutoff `-10^10`. The reference comparison has raw factor one. The nontrivial comparison used in the counterexample has a weighted log above `0.181`, so edgeR's all-M-near-zero shortcut cannot apply. The counterexample only uses the third/reference factor relation; values of other raw factors cancel from this relation.

`Proofs/Bounds.lean` proves `logLower_sound` from Mathlib's `Real.sum_range_sub_log_div_le`, using three terms of the atanh series. In detail, for `z=(q-1)/(q+1)` it bounds `log(q)` below by

```
2*(z + z^3/3 + z^5/5) - 2*abs(z)^7/(1-z^2).
```

The rational bound and nonnegative weights are checked separately, then the analytic lemma transfers the result to actual real logarithms. Approximate numerical logarithms are never assumptions of these proofs.

Floating-point ties explain why the replay and exact-real model disagree. One diagnostic example is gene 451, with sample-3/reference counts `(5,10)`. Its exact M average rank is 57, below the lower retained rank 62; floating-point evaluation splits the mathematically tied ratio group and gives it rank 67, so both implementations include it. For sample 1, different evaluation orders of A also change the treatment of a boundary tie. `gene451_counts` and `gene451_exact_rank` formally check the count pair and exact rank. The floating-point rank is a supplementary numerical observation; the formal counterexamples follow from the checked exact selection and bounds, without trusting that observation.

The documentation leaves numerical semantics unspecified. Consequently this development does not establish an unconditional R1/R2 failure under a reading that defines TMM by the floating-point implementation's ranks, nor certify that entire implementation against such a reading. It establishes the exact statements above for the explicit mathematical model and the actual artifact decimals. R3 is an unconditional failure of the shipped files' agreement claim.

The verified artifact fingerprints are:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

## Recheck commands

From this directory, with the installed Lean 4.35.0 and Mathlib v4.35.0, run:

```sh
lake clean proofs
lake build
lake env lean Audit.lean
python3 reproduce.py
sha256sum counts.tsv edger-factors.txt rnanorm-factors.txt
```

`lake clean proofs` removes only this project's generated build outputs, leaving the prebuilt dependency packages intact. `lake build` must end with `Build completed successfully`, with no errors or `sorry` warnings. `Audit.lean` prints the exact principal theorem statements and their axiom dependencies. The supplementary replay must print `PASS: both floating-point replays match artifacts within 1e-14`; this environment produced maximum absolute errors zero for both. Hashes must match the table. No network or installed edgeR/RNAnorm package is required; the replay needs the available R and NumPy.

## Review and trust

The boundary between informal requirements and formal statements is the manual model above. A reviewer must compare it with `README.md`, the supplied documentation, and relevant source, especially the tie convention and the RNAnorm A-trim inconsistency. There is no formal proof of a natural-language document's meaning, of R/Python semantics, or of floating-point library behavior.

The Lean analytic and arithmetic proofs are checked by Lean. The finite parser/matrix/ranking/rational checks in `Proofs/Computation.lean` use `native_decide`; this adds trust in Lean's native evaluation/compiler mechanism, exposed by the axiom audit. The analytic arguments and their use of those computed certificates are kernel checked. The output-file results in `Proofs/Artifacts.lean` use kernel reduction (`decide +kernel`) and have no native-evaluation dependency. There are no custom axioms or admitted proofs. The usual Lean kernel, elaboration of literal files, Mathlib definitions/theorems, and the installed toolchain are also trusted. The replay script, R, NumPy, and replacement utilities are trusted only for the separate reproducibility observation, not for the formal counterexamples.

Sizes of the local review material are recorded below. Generated Lake outputs are not proof inputs. The retained lists need not be accepted on trust: their equality to the model computations is checked.

<!-- SIZES -->
