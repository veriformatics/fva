# Verification results

**R3 is false, with a kernel-checked counterexample covering all seven samples. R1 and R2 remain unproved as statements about documented TMM.** Both files are reproduced byte for byte by the numerical checks described below; that is not a formal proof of documentation conformance. The software, input matrix, documentation, producer scripts, and output files have not been edited.

Run everything, offline, from this directory:

```sh
./check.sh
```

Success is exit status 0 and the final line:

```text
CHECK PASSED: R3 formally REFUTED; R1/R2 reproduced numerically, full conformance UNPROVED.
```

This means the stated results and checker rejection controls passed, not that all README requirements hold. Logs, freshly compiled proof objects, exported proof terms, checker configurations, the dependency audit, and review sizes are regenerated under `.verification-build/`. No pre-existing project proof object is used by this command.

## Requirements and exact formal statements

All six theorem statements below are in [Proofs/Artifacts.lean](Proofs/Artifacts.lean), in namespace `Artifacts`. Their definitions are in that same file. Only Lean's `Init` is imported; Mathlib is unnecessary for these statements.

Each parsed natural number denotes the exact decimal value divided by `scale = 10^17`. `factors` requires a newline-terminated file, parses every line, and rejects malformed decimals. It operates on the UTF-8 bytes of the embedded file, with ASCII decimal digits, rather than floating-point numbers. The two explicit lists `edge` and `rna` contain all seven parsed values. Their equality to the parsed artifacts is proved:

```lean
theorem artifact_values :
    factors edgeBytes = some edge ∧ factors rnaBytes = some rna
```

### R1 — unproved; runtime reproduction and necessary properties checked

The formal result is only:

```lean
theorem r1_necessary_conditions : normalized edge
```

`normalized xs` means exactly seven positive values and

```text
|product(xs / 10^17) - 1| ≤ 10^-14.
```

Its definition uses exact integer inequalities, avoiding any floating-point rounding. Combined with `artifact_values`, this establishes these properties of `edger-factors.txt` itself.

[verification/replay.R](verification/replay.R) sources the shipped `edgeR/R/calcNormFactors.R` and `edgeR/R/normLibSizes.R`, reads the shipped `counts.tsv`, and executes `normLibSizes(m, method="TMM")` with the remaining defaults. It asserts matrix dimensions 454 × 7, finite nonnegative integer counts, seven finite outputs, and maximum absolute output error **≤ 10^-12**. It also formats the results using the shipped producer's `sprintf("%.17g", ...)` convention and asserts equality to **every byte** of `edger-factors.txt`. In the installed R 4.6.1 runtime the observed maximum error is **0**, and the bytes match exactly.

This is an execution check of the actual shipped R functions. There is no Lean theorem connecting the R execution, its sorting/ranking/logarithms, or its floating-point behavior to the documentation's TMM procedure. No formal definition of documented TMM or certified R evaluator has been supplied. Consequently neither the execution nor the normalization invariant proves R1 in the requested formal sense.

### R2 — unproved; numerical-body reproduction and necessary properties checked

The formal result is only:

```lean
theorem r2_necessary_conditions : normalized rna
```

Together with `artifact_values`, this proves the same seven-value, positivity, and product bound for the exact decimals in `rnanorm-factors.txt`.

[verification/replay.py](verification/replay.py) compiles **unchanged function ASTs** from the shipped `rnanorm/between_sample.py`: `remove_zero_genes`; UQ's `_get_norm_factors`, `get_norm_factors`, `_reset`, and `fit`; and TMM's corresponding methods plus `__init__` and `_get_ref`. It runs `TMM().fit(m.T).get_norm_factors(m.T)` on the shipped matrix. The check requires maximum absolute error **≤ 10^-12**, then separately requires exact equality of every output byte using the producer's `repr(float)` formatting. With installed NumPy 2.5.4, the observed maximum error is **0**, and the bytes match exactly.

**This is not a full RNAnorm package execution.** SciPy, pandas, and scikit-learn are unavailable offline. Explicit adapters supply NumPy average-tie ranks, linear percentiles, `exp(mean(log(x)))`, library-size sums, finite dense-array validation, and default output/context behavior. Methods are attached to lightweight classes without the unavailable sklearn base classes. `LibrarySize`'s numerical sum matches the operation configured in the shipped `utils.py`, but its complete sklearn wrapper is not executed. The adapter code is part of the material to review; its equivalence to those dependencies has not been proved.

There is no theorem deriving the output from the TMM docstring or certifying the Python/NumPy execution and adapters. Thus R2 remains formally unproved. The docstring also has a prose inconsistency: its procedure bullet says A-values use `m_trim`, while its parameter documentation and code use `a_trim`. This report does not silently select a formal interpretation and claim to have verified it.

### R3 — refuted for all seven shipped values

The exact theorem statements are:

```lean
theorem r3_all_samples_fail :
    edge.length = 7 ∧ rna.length = 7 ∧
    ∀ i : Fin 7, ¬ within10 edge[i.val]! rna[i.val]! ∧
      rounded10 edge[i.val]! ≠ rounded10 rna[i.val]!

theorem r3_sample1_gap :
    edge[0]! = rna[0]! + 931142302732627 ∧
    edge[0]! > rna[0]! + 10^14

theorem r3_failure_of_artifact :
    ∃ e r, factors edgeBytes = some e ∧ factors rnaBytes = some r ∧
      e.length = 7 ∧ r.length = 7 ∧
      ∀ i : Fin 7, ¬ within10 e[i.val]! r[i.val]! ∧
        rounded10 e[i.val]! ≠ rounded10 r[i.val]!
```

`within10 a b` is `a ≤ b + 10^7 ∧ b ≤ a + 10^7`, exactly absolute difference ≤ 10^-10 after dividing by `10^17`. `rounded10 a` is `(a + 5000000) / 10000000`, giving rounding to ten fractional decimal places, half upward. All seven pairs fail both tests. The final theorem directly mentions the parsed artifact strings, rather than just two disconnected lists of numbers.

The counterexample input is the shipped `counts.tsv`. Sample 1 alone is sufficient:

| File | Exact sample 1 decimal |
|---|---:|
| `edger-factors.txt` | 0.99099942459293067 |
| `rnanorm-factors.txt` | 0.9816880015656044 |
| Absolute difference | **0.00931142302732627** |

The rounded values are 0.9909994246 and 0.9816880016. The formal gap is `931142302732627 / 10^17`, over 93 million times `10^-10`. This refutation requires no assumptions about TMM or how the files were produced.

A separate runtime diagnostic traces a copy of edgeR's actual `.calcFactorTMM` function and records RNAnorm's rank calls. For sample 1, edgeR retains 65 genes and RNAnorm retains 64; gene 355 is the sole difference. The source computes A-values using a sum of logs versus a log of a product. Their floating-point rounding can change trimming at ties. The diagnostic is numerical evidence, not a proved explanation or a replacement implementation. Both paths select sample 4 as reference.

## Connection to the exact shipped artifacts

`edgeBytes` and `rnaBytes` use `include_str` to embed the actual files when Lean elaborates the proof. The proof parses those strings inside the logic. Independently of Lean's file-reading elaborator, `verification/check.py` reads the exported definitions' **string literal values**, encodes them as UTF-8, and compares them with the complete current artifact bytes. A changed-file control demonstrates that this binding check rejects other bytes.

[verification/inputs.sha256](verification/inputs.sha256) pins all 17 original input, source, documentation, producer, and project configuration files. In particular:

```text
counts.tsv          aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5
edger-factors.txt   df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943
rnanorm-factors.txt 62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d
```

The two factor files are 138 and 133 bytes; the count matrix is 6,518 bytes. Hashes identify the original snapshot; they do not replace the literal-to-file equality check. Changing the manifest alone cannot make the existing formal R3 theorem apply to different artifact literals. No handwritten TMM model is passed off as the shipped implementation.

## Independent checking and rejection controls

`./check.sh` freshly elaborates the Lean files with Lean **4.35.0**, exports just the six theorem targets and their complete transitive dependencies using `leanexport`, audits the targets and axioms, then replays the exported terms from an empty environment through:

1. Lean's C++ kernel, via `leanchecker --from-export`.
2. Lean's paranoid checker, via `leanchecker-paranoid --from-export` (an additional Lean checker configuration, not counted as an independent implementation).
3. **Nanoda 0.4.19**, an independently implemented Rust type checker, with natural-number and string extensions enabled and a strict axiom whitelist.

The only permitted and actually exported axioms are **`propext` and `Quot.sound`**. `sorryAx`, `Lean.trustCompiler`, arbitrary assumptions, and native-evaluation axioms are not allowed. The artifact proofs use ordinary kernel reduction via `decide`, never `native_decide`. All exported definition bodies and library proof dependencies are replayed, not merely the final theorem names.

The command then performs these mandatory controls:

| Control | Expected, observed result |
|---|---|
| [ForgedFalse.lean](verification/ForgedFalse.lean): inject theorem `False` with value `True.intro` while bypassing the initial checker | Both Lean replays and Nanoda reject the proof object for a type mismatch |
| [ForgedArithmetic.lean](verification/ForgedArithmetic.lean): inject theorem `1 = 0` with a proof of `1 = 1` | All three replays reject for a type mismatch |
| [AdmittedFalse.lean](verification/AdmittedFalse.lean): introduce `False` as an axiom | The explicit axiom audit and Nanoda's whitelist reject it |
| Bind the successful proof bundle to a temporary artifact containing `0.0` instead | The byte-binding audit rejects it |

The false proof objects are successfully constructed and exported before being challenged. A syntax error, missing checker, missing file, or unrelated nonzero status is not accepted as a successful control: expected rejection diagnostics are required. Deliberate kernel bypasses occur only in the two negative-control files, which are not imported by the actual proofs.

Nanoda reports **1,599 declarations with no typechecker errors** and exits 0 on the real bundle. It also emits one pretty-printer diagnostic, `Unable to print axioms`; this is not a typechecking success substituted for a rejection. Its false-proof controls fail with the expected `self.def_eq` assertion, and its forbidden-axiom control fails with `unpermitted axiom`. Full output is retained in the logs.

The installed `lean4lean` binary was also inspected, but its nightly-version object format is incompatible with this release's `.olean` files. It is not used or counted as a successful replay. Independent checking here uses Nanoda's exported-term interface.

## Review surface and remaining trust

The complete task-specific formal surface is **12 explicit definitions and six theorem statements in 83 lines / 3,027 bytes**, including proof bodies, comments, and axiom-printing commands, plus the one-line / 24-byte import in [Proofs.lean](Proofs.lean). A reviewer should read the entire small file, particularly decimal parsing, the scaling convention, tolerance, rounding rule, list order, and the limited meaning of `normalized`. It contains no TMM specification.

The full exported dependency closure is 4,244,311 bytes. It contains 684 definition records, one opaque definition with an exported value, 644 theorem records, two axiom records, 82 inductive blocks, and four quotient records. Inductive blocks include constructors and recursors, so record counts differ from the 1,599 declarations checked by Nanoda. These are largely standard Lean definitions and lemmas; they are replayed by the kernels. The report's mathematical meaning still assumes the usual interpretation of natural numbers, lists, finite indices, strings, and the two listed logical axioms. No Mathlib mathematics or R/Python floating-point library is trusted by the R3 proof.

Additional authored checking/reproduction code that should be reviewed:

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `verification/check.py` | 156 | 8,047 | Command orchestration, export audit, exact byte binding, negative controls |
| `check.sh` | 4 | 74 | Single-command entry point |
| `verification/replay.R` | 25 | 1,362 | Actual R source execution, byte comparison, retained-gene diagnostic |
| `verification/replay.py` | 100 | 3,845 | Original Python function loading, explicit dependency adapters, byte comparison |
| `verification/ForgedFalse.lean` | 13 | 378 | Deliberately invalid proof object |
| `verification/ForgedArithmetic.lean` | 12 | 371 | Deliberately invalid arithmetic proof object |
| `verification/AdmittedFalse.lean` | 3 | 107 | Forbidden-axiom control |
| `verification/inputs.sha256` | 17 | 1,428 | Original snapshot identities |

Exact current sizes are regenerated in `.verification-build/review-size.txt`. The manifest is data, not a proof. The runtime R evidence additionally trusts the two shipped R sources (352 lines / 12,166 bytes), the installed R implementation, and its mathematical libraries. The Python evidence additionally requires reviewing the shipped numerical methods and the dependency adapters and trusting Python/NumPy; it does not certify the absent packages. The source and documentation hashes make that review refer to this snapshot.

For the formal results, the remaining execution trust includes the checker executables, their natural-number/string primitives, the exporter/parser boundary, Python's file/JSON handling in the binding audit, and the operating system/hardware. Exported dependencies are checked by independently implemented kernels, and the explicit rejection controls exercise their ability to reject the kinds of false proof objects used here. This reduces reliance on a single kernel; it is not a proof that the toolchain or hardware cannot malfunction.
