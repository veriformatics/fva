# Verification

The artifacts disagree with exact-arithmetic TMM at an absolute tolerance of **10⁻¹⁰**. R3 also fails directly: the first output values differ by exactly **0.00931142302732627**. These are counterexamples on the supplied `counts.tsv`, not claims about all possible matrices.

Run from this directory, without network access:

```sh
python3 verification/check.py
```

The command uses the installed Lake/Lean/Mathlib toolchain, `leanexport`, `leanchecker`, `con-ron`, Python 3 with NumPy, and base R.

Success ends with `VERIFICATION SUCCESS` and a statement that both kernels accepted the proofs and rejected both false-proof controls. Any failed build, changed artifact, missing theorem, unapproved axiom, kernel rejection of a valid proof, or acceptance of a false-proof control fails the command. Logs, the full proof export, and a machine-readable size/axiom report are written under `.verification/`.

## Exact results

The following are the exact public statements, in namespace `Verification`. Definitions are in `Proofs/Spec.lean`; `ℚ` values are interpreted as exact decimal rationals, not binary floating-point values.

| Requirement | Theorem and file | Result |
|---|---|---|
| R1 | `theorem R1_failure : ¬ Meets edge` — `Proofs/Results.lean` | First shipped edgeR value exceeds the exact TMM factor by more than 10⁻¹⁰. |
| R2 | `theorem R2_failure : ¬ Meets rna` — `Proofs/Results.lean` | First shipped RNAnorm value exceeds the exact TMM factor by more than 10⁻¹⁰. |
| R3 | `R3_failure` — `Proofs/ArtifactValues.lean` | The first values alone refute agreement to ten decimal places. |

```lean
theorem R1_failure : ¬ Meets edge
theorem R2_failure : ¬ Meets rna
theorem R3_failure : tolerance < |edge[0]! - rna[0]!|
```

The shared witness for R1/R2 is:

```lean
theorem first_TMM_lt : tmm 0 < (98 : ℝ) / 100
```

The files' exact first values are `99099942459293067 / 100000000000000000` and `9816880015656044 / 10000000000000000`. `edge_first` and `rna_first` in `Proofs/ArtifactValues.lean` check these identities. The stronger exact R3 difference is checked there as:

```lean
theorem first_difference : edge[0]! - rna[0]! =
    (931142302732627 : ℚ) / 100000000000000000
```

The requirement predicate is exactly:

```lean
def tolerance : ℚ := 1 / 10000000000
noncomputable def Meets (out : List ℚ) : Prop :=
  ∀ i ∈ List.range 7, |(out[i]! : ℝ) - tmm i| ≤ (tolerance : ℝ)
```

One failing sample suffices to refute each universal requirement. The artifact reader requires both output files to contain seven entries.

## Meaning of the specification

`Spec.lean` specifies mathematical TMM: library sums; linearly interpolated type-7 upper quartiles; the reference closest to their mean; positive count pairs; average ranks including exact ties; 30% trimming at each M tail and 5% at each A tail; inverse-binomial-variance weighting; and geometric-mean normalization. M ranks compare rational count ratios by cross multiplication. A ranks compare count products. Both comparisons follow from strict monotonicity of the logarithm and positive library sizes. Natural logarithms and `Real.exp` express the same factors as log₂ and exponentiation by 2, since the bases cancel.

`shape` checks 454 rows of seven counts with no all-zero row. `reference : refIndex = 3` certifies sample 4 as reference. `quantiles_above_fallback` checks that every upper quartile exceeds 10⁻²⁰; edgeR's low-quartile fallback is therefore irrelevant. `cutoff_irrelevant` proves that every positive pair's exact A-value exceeds the default −10¹⁰ cutoff. These supporting theorems are in `Proofs/Data.lean` and `Proofs/Defaults.lean`.

For RNAnorm I use the documented `a_trim` parameter and its default `.05`, as used by its shipped implementation. The procedure bullet that says to trim A with `m_trim` repeats the other parameter's name; that literal alternative reading is not the specification of `R2_failure`.

This is an exact-arithmetic reading of the documented statistical calculation, with average-rank ties as in the shipped methods. It is not a formal operational semantics of R, NumPy, or IEEE transcendental functions. If R1/R2 are instead read as requiring reproduction of each concrete floating-point implementation, the source diagnostics below pass; the Lean counterexamples concern mathematical TMM at the stated tolerance. No universal implementation-correctness or floating-point-error theorem is claimed.

## Why the difference occurs

Rounding perturbs exact ties at trim boundaries. For sample 1, 244 genes have positive counts in both it and reference sample 4. M ranks retained are 74 through 171; A ranks retained are 13 through 232. `tied_boundary` proves:

```lean
rank2 mLT (pairs 0) (6, 3) = 355 ∧
rank2 aLT (pairs 0) (13, 8) = 465 ∧ (pairs 0).length = 244
```

Thus gene 31, with counts `(6,3)`, has exact M rank 177.5; gene 355, with counts `(13,8)`, has exact A rank 232.5. Both should be excluded. The floating calculations admit the first gene in both implementations and the second in edgeR. The exact factor is approximately 0.97553; only the certified upper bound `< 0.98` is needed for the proof.

`verification/reproduce.R` sources the unchanged shipped R implementation and reproduces `edger-factors.txt` byte for byte. `verification/reproduce.py` executes the actual AST of RNAnorm's `_get_norm_factors`, with small replacements for unavailable packaging/dependency wrappers, NumPy library sums, and average ranks. Its factors match the supplied file in this environment. This is a diagnostic of that method, not a full installed RNAnorm-package execution or a premise of any Lean theorem.

## Binding to the shipped files

`verification/artifacts.json` pins all original inputs, sources, documentation, output files, and Lake configuration. In particular:

| File | SHA-256 |
|---|---|
| `counts.tsv` | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

Every check regenerates `Proofs/Input.lean` from these files using `verification/input.py`. The reader validates the ASCII grammars, dimensions, final newlines, decimal precision, and exact reconstruction of all three byte strings. Integer counts and decimal mantissa/scale pairs become literal Lean inputs. This small Python bridge is trusted for the byte-to-number interpretation; it is not proved correct in Lean. No floating-point calculation supplies a proof premise. Source files and shipped output files are never rewritten.

`Data.lean` certifies the reference, library sizes, and kept pairs against these generated inputs. `Numeric.lean` certifies all seven weighted natural-log means with rational bounds. The generators for these certificates are untrusted proof producers: altering a claimed result makes the kernel checks fail. `LogBounds.lean` proves rational logarithm enclosures using Mathlib's finite-series remainder theorem, and `MeanBounds.lean` propagates those enclosures through positive weighted means. No approximate logarithm or exponential is an axiom.

## Independent checking and false proofs

The command deletes local build products and compiles with Lean 4.35.0 and the installed Mathlib v4.35.0. It exports the public results **and their transitive dependency closure**, audits target presence and axioms, then replays that export through:

1. Lean's C++ kernel using `leanchecker --from-export`.
2. The independently implemented Rust kernel `con-ron --verified`, with its default pins and without trusted/testing modes.

The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. `sorryAx`, `Lean.trustCompiler`, and custom axioms are rejected. No `sorry`, `admit`, or `native_decide` is used.

Both kernels first accept valid control proofs. The driver then creates two syntactically valid, corrupted proof streams: an unchanged reflexivity proof offered for `37 + 5 = 43`, and a proof of `False → False` offered as a proof of `False`. Both kernels must return rejection (exit 1) with a type-mismatch diagnostic for both streams. Malformed input, usage failure, or a missing target cannot count as successful rejection.

## Review and trust sizes

The semantic specification is `Proofs/Spec.lean`: **57 lines, 2,695 bytes**, including imports, comments, and blank lines. Its three input definitions are in generated `Proofs/Input.lean`: **6 lines, 11,124 bytes**, containing 3,206 natural-number literals (3,178 counts and 28 decimal mantissa/scale components). The public theorem statements are reproduced above; their proof file `Results.lean` is 45 lines, 1,319 bytes, and `ArtifactValues.lean` is 19 lines, 617 bytes.

The artifact reader is **32 lines, 1,473 bytes** (`verification/input.py`). The checking driver is **111 lines, 5,672 bytes** (`verification/check.py`). The check also records every Lean file’s size and the exported dependency closure. Review this bridge and driver, the specification's correspondence to the supplied documentation, the artifact hashes, and the selected tolerance/interpretation.

Auxiliary definitions and their proofs are in `LogBounds.lean` (45 lines), `MeanBounds.lean` (38 lines), and `Defaults.lean` (49 lines); generated certificates are in `Data.lean` and `Numeric.lean`. Their proof terms are checked, not assumed. Mathlib's standard definitions of rationals, reals, logarithms, exponentials, lists, and arithmetic remain part of the transitive definitional foundation; `.verification/report.json` reports the complete exported declaration counts and byte size rather than hiding these dependencies behind a count of only the final statements.

The remaining trust is the two kernel executables, their parsers and runtime/hardware, the three named logical axioms, the artifact bridge/check driver, and the human interpretation of the mathematical specification. Sharing an exporter does not make its output trusted: both kernels check its declarations. This verification does not formalize the host filesystem, Python byte reader, R interpreter, NumPy, or the diagnostic wrappers.
