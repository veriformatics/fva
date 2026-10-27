The artifacts do **not** satisfy all the requirements: **R3 is false**. The first factors differ by exactly `0.00931142302732627`, far exceeding `10⁻¹⁰`.

R1 and R2 need a distinction between the mathematical formula and floating-point execution. All seven values in each file are proved within **absolute tolerance `1/40 = 0.025`** of the exact TMM formula with M trimming `0.3` and A trimming `0.05`. This is a coarse tolerance, not evidence of ten-decimal-place accuracy. Both artifacts fail against that formula at `10⁻¹⁰`. RNAnorm's procedure also literally says to trim A with `m_trim`; under that reading R2 fails even at `0.025`. The results for both readings are below.

Run everything, offline, from this directory:

```sh
python3 verification/check.py
```

Success ends with:

```text
ALL VERIFICATION CHECKS PASSED (the R3 requirement is refuted).
```

This means the verification results and rejection controls passed; it does not mean all software requirements hold. The command deletes and rebuilds this project's `.lake/build`, checks the artifact bindings, exports complete proof dependencies, replays them in two independent kernels, exercises false-proof and changed-artifact controls, and executes the shipped edgeR implementation. Logs are written under `verification/`. It needs the installed Lean 4.35.0/Mathlib project, Python 3, Rscript, and `leanexport`, `leanchecker`, and `con-ron` under Lean's installation `bin` directory. It performs no downloads.

**What the formal specification means.**

`Proofs/Spec.lean` parses the actual decimal file bytes as exact rationals and the count matrix as natural numbers. Sample indices in Lean are zero-based. `terms i aNum aDen` specifies TMM as follows:

- The reference is sample 4 (index 3). `reference_is_fourth` in `Proofs/Conformance.lean` proves that its library-normalized upper quartile is uniquely closest to the mean. The type-7 quartile uses sorted entries 340 and 341 with weights `1/4` and `3/4`, for this 454-row matrix. Common positive scaling by CPM or geometric-mean normalization preserves that choice.
- Pairs with a zero count are excluded. `matrix_shape` proves there are 454 rows, each with seven counts and a positive entry, so removing all-zero rows changes nothing. `libraries` proves library sizes `[1261,621,755,1097,1916,1136,1219]`. `libraries_bounded`, `positive_fraction`, and `cutoff_inactive` establish that edgeR's default A cutoff excludes no remaining pair.
- M ranks compare `obs/ref` using exact integer cross-products; A ranks compare `obs*ref`. These have the same ordering as the corresponding logarithms after library normalization. Ranks are average ranks, including ties, as in the shipped implementations. Trimming keeps ranks between `floor(n*trim)+1` and `n-floor(n*trim)`, inclusively. M trimming is `3/10`; A trimming is `aNum/aDen`.
- For each retained count pair `(o,r)`, the ratio is `q=o*Nref/(r*Ni)` and precision is `w=1/(1/o+1/r-1/Ni-1/Nref)`. Equal pairs are grouped with their multiplicity multiplying `w`. The raw log factor is `sum(w*log q)/sum(w)`. The final factor is its exponential after subtracting the mean of the seven raw log factors. This cancels the base-2 conversion and enforces geometric mean one.

The mathematical interpretation of the documentation, including the tie convention supplied by the source, is an explicit human review obligation. The specification uses exact real arithmetic. It does not identify floating-point ranks with exact ranks. A requirement interpreted solely as reproduction of edgeR's floating-point implementation has the separate execution result described below.

**R1.** In namespace `Verify`, `Proofs/Conformance.lean` proves these exact statements:

```lean
theorem r1_coarse : within edgeFactors (1/40)

theorem r1_fine_counterexample :
    |((edgeFactors[2]! : ℚ) : ℝ) - tmm 1 20 2| > (tolerance : ℝ)
```

Here `within actual tol` means `actual.length = 7` and, for every index below seven, absolute error from `tmm 1 20 i` is at most `tol`. `tolerance` is exactly `1/10000000000`. Thus R1 holds at the stated coarse tolerance, and a stronger `10⁻¹⁰` interpretation fails on the supplied matrix, sample 3. The proof establishes `tmm 1 20 2 > 1.13`; the third shipped edgeR value is `1.1253076397204775`.

`verification/reproduce.R` separately sources the two **unmodified shipped** edgeR R files, reads `counts.tsv`, invokes `normLibSizes(x, method='TMM')`, formats its result with the producer's `%.17g`, and compares all output bytes with `edger-factors.txt`. This passes exactly in the supplied environment. It is an execution check, with the R interpreter, libraries, and floating-point runtime in its trust boundary; it is not a general proof of the R implementation.

**R2.** The class docstring's parameter descriptions specify `a_trim` for A, and the source defaults are `m_trim=0.3, a_trim=0.05`. On that interpretation, `Proofs/Conformance.lean` proves:

```lean
theorem r2_coarse : within rnaFactors (1/40)

theorem r2_fine_counterexample :
    |((rnaFactors[2]! : ℚ) : ℝ) - tmm 1 20 2| > (tolerance : ℝ)
```

All seven values satisfy tolerance `0.025`; sample 3 refutes tolerance `10⁻¹⁰`. Its shipped value is `1.1270795948647565`, again below the proved mathematical lower bound `1.13`.

The procedure bullet instead says “Compute A values, filter by double trimming with m_trim”. Taking this literally makes A trimming `3/10`. For that reading the same file proves:

```lean
theorem r2_literal_counterexample :
    tmm 3 10 1 - ((rnaFactors[1]! : ℚ) : ℝ) > (1/40 : ℝ)
```

The supplied matrix, sample 2, is a counterexample even at tolerance `0.025`. Its artifact value is `1.2793096928626835`; the proof shows the literal formula exceeds `1.34`. The report does not silently resolve the conflicting documentation. No general Python-source correctness or reproduction claim is made: The shipped RNAnorm files are a package excerpt without its initializer/typing module, and SciPy, pandas, and scikit-learn are absent from the supplied environment. The artifact bounds use its bytes directly and need none of those dependencies.

For both R1 and the `a_trim` reading of R2, `factor_intervals` proves the following exact bounds on the mathematical factors:

| Sample | Lower bound | Upper bound |
|---|---:|---:|
| 1 | 0.974 | 0.977 |
| 2 | 1.279 | 1.284 |
| 3 | 1.146 | 1.150 |
| 4 | 0.955 | 0.959 |
| 5 | 0.814 | 0.817 |
| 6 | 0.931 | 0.934 |
| 7 | 0.956 | 0.960 |

These explain why the coarse tolerance should not be confused with close numerical conformance. The proofs establish the discrepancies without relying on a proposed diagnosis of their cause.

**R3.** `Proofs/Results.lean` proves:

```lean
theorem artifact_lengths : edgeFactors.length = 7 ∧ rnaFactors.length = 7

theorem first_difference :
    edgeFactors[0]! - rnaFactors[0]! =
      (931142302732627 / 100000000000000000 : ℚ)

theorem r3_counterexample :
    |rnaFactors[0]! - edgeFactors[0]!| > tolerance

theorem r3_fails : ¬ agrees rnaBytes
```

`agrees s` requires both files to parse into seven values and every paired absolute difference to be at most `10⁻¹⁰`. The first lines, `0.99099942459293067` and `0.9816880015656044`, suffice to refute this necessary condition for agreement to ten decimal places. This counterexample is independent of any interpretation of TMM or tie handling.

**Connection to the shipped artifacts.**

`Proofs/Artifacts.lean` contains literal lists of every byte of `counts.tsv`, `edger-factors.txt`, and `rnanorm-factors.txt`: 6,789 bytes in total, including tabs and final newlines. `verification/embed.py --check` regenerates this encoding in memory and demands byte-for-byte equality with the Lean source. `input_encoding` proves that every count token parses and all three files end in LF; `edge_values`, `rna_values`, and `matrix_eq` prove the exact decoded values. Formal rank, weight, and interval computations start from this decoded matrix. The checker also validates the SHA-256 snapshot of all shipped input, output, documentation, producer, and implementation files in `verification/artifacts.sha256`.

Changed-byte controls operate on temporary copies: independently changing the first byte of each of the three artifacts must make the actual embedding checker fail. The shipped files are never rewritten. `Proofs/Certificates.lean` contains generated candidate terms and rational intervals. Every equality connecting those candidates to the parsed matrix, every interval inequality, and the certificate soundness theorem is kernel checked. `verification/certificates.py` is an untrusted search tool; running it is unnecessary to check the proofs.

**Independent checking and rejection controls.**

`verification/Export.lean` exports the named theorem roots in `verification/roots.txt` together with their complete dependencies. The check audits root coverage, safe definitions, and an axiom allowlist containing only `propext`, `Classical.choice`, and `Quot.sound`. Neither `sorryAx` nor `Lean.trustCompiler` is permitted. The proofs use ordinary proof terms, including kernel reduction via `decide +kernel`, and exact rational bounds for logarithms. The analytic error bound is itself proved using Mathlib's `Real.sum_range_sub_log_div_le`, then replayed with its dependencies.

The same exported terms pass Lean 4.35's C++ kernel (`leanchecker --from-export`) and the independent Rust `con-ron` kernel in `--verified` mode. Imported library proofs in that dependency export are replayed too. No kernel is asked to assume the other kernel's verdict.

The controls require Lean to reject `True.intro` as a proof of `False`. They then re-export the R3 dependency closure alone and replace the **actual exported** `r3_fails` theorem's proposition with `False`, retaining its original proof and otherwise well-formed dependency stream. The positive checks cover all 17 roots; using the R3 closure alone keeps the negative controls short. Both replay kernels must reject that stream with the expected type-error verdict. Success is checked using both exit status and verdict text. Acceptance, unsupported-input errors, missing tools, and silently skipped checks do not count as success.

**Human review and trust size.**

`verification/review.txt` extracts all 33 handwritten `def` declarations, both `abbrev` declarations, and the 17 exact exported theorem statements from the four handwritten Lean files, plus the two exported generated theorem statements. It is **205 lines / 7,049 UTF-8 bytes**, including blank lines and source-location comments. `verification/review.py --check` detects a stale extraction. This is a conservative application-specific review slice: it includes certificate helper definitions as well as the mathematical specification and artifact parsers. The full handwritten proofs can additionally be read in `Proofs/Bounds.lean`, `Proofs/Spec.lean`, `Proofs/Results.lean`, and `Proofs/Conformance.lean`.

The generated byte embedding is 5 lines / 24,548 bytes; its underlying data is the 6,789 artifact bytes. Generated certificates are 166 lines / 40,758 bytes. These large literals need checking against the inputs, rather than manual mathematical review. Their proofs and the generator are outside the trusted semantic specification.

For the bridge from disk to theorem and the checking policy, review `verification/embed.py` (17 lines / 631 bytes), `verification/Export.lean` (9 / 275), `verification/audit.py` (35 / 1,487), and `verification/check.py` (69 / 3,619). The false-proof construction is `verification/negative.py` (27 / 1,223); the runtime reproduction check is `verification/reproduce.R` (9 / 513). The extraction script is `verification/review.py` (28 lines / 1,579 bytes). Review the documentation-to-formula interpretation above, `verification/roots.txt` (17 / 393) as well.

The 205-line figure does **not** include Lean/core/Mathlib definitions of rationals, reals, logarithms, exponentials, lists, and arithmetic. Their conventional meanings and the three listed axioms remain part of the foundational review boundary. The complete export is `verification/proofs.ndjson` (156,889,089 bytes); `verification/closure.json` records its census: 17 roots, 6,284 definitions, 22 opaque declarations, 708 inductive blocks, 19,560 theorems, four quotient records, and the three allowed axioms. This larger closure includes proof dependencies, and its proofs are replayed by the independent kernels. The script sizes above exclude the installed tooling. Hardware, operating-system execution, Lean’s source elaboration, LeanExport’s serialization, the byte bridge/driver, and correct operation of at least one of the independent proof kernels remain trusted. The R reproduction result additionally trusts the R runtime. There is no claim of a machine-code or general source-language correctness proof for either implementation.
