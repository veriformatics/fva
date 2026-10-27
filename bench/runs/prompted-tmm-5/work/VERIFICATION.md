# Verification result

**R3 fails unconditionally. R1 and R2 fail at absolute tolerance `10⁻¹⁰` under the exact mathematical interpretation of the documented TMM calculation specified below.** All three counterexamples concern the supplied `counts.tsv` and the supplied output files. No implementation or original input/output file was changed.

There is an important interpretation boundary: the documentation does not specify floating-point rounding or how it changes mathematical ties. The R1/R2 results use exact counts, exact ties, average ranks, and real logarithms/exponentials. They do **not** assert that the files fail to reproduce a particular floating-point implementation. Indeed, executing the supplied edgeR source reproduces its file exactly. If R1/R2 instead mean equality to platform-specific R/Python execution, R1 has this reproduction test, and R2 execution correspondence remains unproved. R3 fails under either interpretation.

## The checked statements

All names below are in namespace `Verification`, in `Proofs/Finish.lean`. The complete custom definitions used by their statements are in `Proofs/Spec.lean`; the concrete data definitions are in `Proofs/Artifact.lean`.

```lean
theorem R1_fails : ¬ Compatible Artifact.edge (retained 1 20)
theorem R2_fails : ¬ Compatible Artifact.rna (retained 1 20)
theorem R2_literal_bullet_fails : ¬ Compatible Artifact.rna (retained 6 20)
theorem R3_counterexample :
    (9/1000 : ℚ) < |Artifact.edge.getD 0 0 - Artifact.rna.getD 0 0|
theorem R3_fails : ¬ Agree10
```

* **R1:** samples 3 and 4 of `edger-factors.txt` cannot both be within `10⁻¹⁰` of the documented mathematical TMM factors. This refutes the requirement that every sample satisfies that tolerance.
* **R2:** the same pair refutes the same tolerance for `rnanorm-factors.txt`. Defaults are 30% M trimming and 5% A trimming. The docstring also has a bullet saying `m_trim` for A; `R2_literal_bullet_fails` covers that literal alternative, 30% A trimming, as well.
* **R3:** sample 1 is a direct counterexample: `0.99099942459293067` versus `0.9816880015656044`. Their exact decimal difference is `0.00931142302732627`, proved greater than `0.009`. `Agree10` allows absolute differences up to `10⁻¹⁰` for all seven samples, so even this weak necessary condition for agreement to ten decimal places is false.

The input witnessing all these failures is the complete supplied 454 × 7 matrix, not a modified or synthetic input. Indices in Lean are zero based.

## Why the pair condition expresses a necessary TMM property

`Compatible values ps` means exactly:

```lean
∃ c : ℝ, 0 < c ∧
  |c - (values.getD 3 0 : ℝ)| ≤ 1 / 10^10 ∧
  |c * Real.exp (logMean ps) - (values.getD 2 0 : ℝ)| ≤ 1 / 10^10
```

The documentation-to-statement correspondence to review is the following:

1. The default reference is sample 4. `matrix_shape`, `library_sizes`, `quartile_brackets`, and `reference_is_four` in `Proofs/Compute.lean` establish that no row is entirely zero, the library totals are `[1261,621,755,1097,1916,1136,1219]`, the upper quartiles are `[4,2,2,3,5,3,3]`, and sample 4 uniquely minimizes distance of upper-quartile/library-size to its mean. Every such ratio exceeds `10⁻²⁰`, so edgeR's fallback does not apply. RNAnorm's additional common geometric rescaling of these ratios preserves that minimizer.
2. For a positive count pair `(o,r)`, ordering M is equivalent to ordering `o/r`; ordering A is equivalent to ordering `o*r`. `rankM` and `rankA` use integer cross products and twice the average rank, preserving exact ties. `retained` applies the floor-based trimming limits used in the supplied sources. There are 205 eligible pairs and 76 retained pairs for the defaults. `cutoff_safe` in `Proofs/Finish.lean` proves that every eligible A-value exceeds edgeR's default cutoff `-10¹⁰`.
3. `weight` is inverse asymptotic binomial variance. `logMean` is the weighted mean of the natural logs of `(o/lib.obs)/(r/lib.ref)`. Exponentiating this mean is the same exact-real expression as raising 2 to the weighted mean of log2 ratios.
4. The reference's raw factor is 1. Common positive geometric normalization therefore gives final factors `c` for sample 4 and `c * exp(logMean ps)` for sample 3, for some positive `c`. Consequently any factors satisfying R1/R2 must satisfy `Compatible`. Allowing **any** positive `c` avoids having to model the other five raw factors or their geometric mean.

This is a specification of the documented mathematical requirement, not a replacement implementation of R or Python. The correspondence above, including the intended treatment of exact ties, is the semantic interpretation a human must approve.

`raw_ratio_lower` proves the required raw ratio is strictly greater than `1181/1000`. Both files instead have sample-3/sample-4 ratio approximately `1.18007990023344`. `artifact_gaps` and `cannot_fit` make the contradiction rigorous while allowing the full absolute tolerance on both factors; division of approximate numbers is not used as proof.

The logarithm bound is proved in `Proofs/Bounds.lean` using Mathlib's checked two-term atanh-series remainder bound. All subsequent certificate arithmetic uses kernel reduction (`decide`, including `decide +kernel`), not native evaluation or an oracle. `Proofs/Certificate.lean` is untrusted candidate data: Lean proves it equals the retained pairs computed from the matrix.

## Connection to exact shipped bytes

`verification/artifacts.sha256` pins the matrix, both outputs, both producer scripts, all supplied implementation/documentation files, README, and CHECK. In particular:

| File | Bytes | SHA-256 |
|---|---:|---|
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

`verification/embed.py` transfers the actual TSV integers and exact decimal rationals to `Proofs/Artifact.lean`. It checks the matrix's canonical byte round trip and embeds the entire output strings, including line endings. The check command regenerates this module and requires byte equality with the checked-in module. The rational values thus denote the text artifacts exactly, rather than rounded binary doubles or manually copied expected results. The transfer script and Python's integer/Fraction parsing are a small, explicit trusted bridge from filesystem bytes to Lean literals.

`verification/runtime.R` additionally sources the actual supplied R files and checks exact binary-double equality with every shipped edgeR value. It prints 77 retained pairs for sample 3/reference 4, compared with the proved mathematical 76. For example, exact ratio `1/2` count pairs produce M-values `-0.46098502380924838` and `-0.46098502380924816`: their floating ranks split into 56.5 and 67, crossing the lower trim boundary 62. This diagnostic explains why exact mathematical verification and successful runtime reproduction can coexist. It is an execution test, not a proof of the R interpreter or its transcendental functions. The RNAnorm Python package dependencies are not installed here; no claim of executing that package is made.

## One check command

From this directory, with the supplied offline tool installation:

```sh
./check.sh
```

It checks hashes and the embedding, removes local proof oleans and rebuilds them with Lean 4.35/Mathlib, exports the requested declarations **with their complete dependency closure**, audits the axiom allowlist, and replays the same export from empty environments through:

* Lean's C++ kernel, using `leanchecker --from-export`;
* Nanoda 0.4.19, an independently implemented Rust kernel, using `nanoda_bin`.

The script discovers `leanexport`, `leanchecker`, and `nanoda_bin` beside the resolved `lean` executable; here they are in `/opt/lean/bin`. It uses no network and does not need wasmtime or wasm-tools. Generated exports, configurations, metrics, and rejection logs go to `.verification/`. Export/checking needs several minutes and hundreds of MB of temporary storage.

Both kernels first accept valid control proofs. `verification/negative.py` then produces well-formed exports with `True.intro` claimed to prove `False`, and `Eq.refl 0` claimed to prove `0 = 1`. Both kernels must reject both. The script checks for actual declaration-type errors, rather than treating a missing executable or malformed export as a successful negative test. Nanoda reports these type errors as an assertion failure in its definitional-equality check. Rejection logs are retained.

Success is exit status 0 and the final line:

```text
SUCCESS: artifact bytes, all theorems, both independent kernels, and negative controls checked.
```

The completed run exited 0 with that success line. Nanoda checked **27,821 declarations** in the full proof export; both false controls were rejected by both kernels. The run log is `.verification/check.log`.

Nanoda also prints `no typechecker errors`. Its separate `Unable to print axioms` pretty-printer message is harmless and is not a typechecking error. Any hash mismatch, edited embedding, failed build, unexpected axiom, missing result, rejected genuine proof, or accepted false proof makes the command fail.

## Review and trust size

The custom semantic surface is **58 physical lines / 2847 bytes**: all of `Proofs/Spec.lean` (48 / 2350) and `Proofs/Statements.lean` (10 / 497). The latter contains just the five statement-only roots, corresponding to the exact theorem types above, for measuring their transitive dependencies. This count includes imports, comments, and blank lines, and excludes generated input data. Supporting machine-checked data facts and proof derivations are in `Proofs/Compute.lean` and `Proofs/Finish.lean`; their theorem statements are also available for review.

The byte-transfer bridge is `verification/embed.py`: **24 lines / 1405 bytes**. Generated `Proofs/Artifact.lean` is **464 lines / 12642 bytes**. Its data need not be manually transcribed or trusted independently of that bridge and the pinned input files.

Additional reviewable automation totals **162 lines / 7703 bytes**:

| File | Lines | Bytes |
|---|---:|---:|
| `verification/check.py` | 104 | 5200 |
| `verification/negative.py` | 24 | 1112 |
| `verification/runtime.R` | 24 | 1146 |
| `verification/Fixture.lean` | 6 | 171 |
| `check.sh` | 4 | 74 |

These scripts are separate from the mathematical meaning of the theorem statements. Exact sizes can be reproduced with:

```sh
wc -l -c Proofs/*.lean verification/*.py verification/*.R verification/*.lean check.sh
cat .verification/metrics.json
```

The standard Lean/Mathlib definitions of rationals, reals, logarithms, exponentials, lists, and logic remain part of the semantic foundation. To avoid concealing their size behind the small custom surface, the command also writes `.verification/statements.ndjson`: a **conservative complete dependency export of the statement-only roots**, including construction proofs required by those definitions. On the completed export this closure has **4255 definition records, 564 inductive blocks, 10575 theorem records, 3 axiom records, and 67,231,736 serialized bytes**. The full-proof closure has 6201 definition records, 708 inductive blocks, 19384 theorem records, the same 3 axioms, and 150,109,700 serialized bytes. These are conservative infrastructure sizes, not a claim that a human can ignore library meanings. Counts and byte sizes are reproduced in `.verification/metrics.json`.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. There is no `sorryAx`, new axiom, `Lean.trustCompiler`, `native_decide`, or admitted analytic/numerical result. Mathlib proof bodies are replayed, not assumed merely because its oleans were already built. The remaining infrastructure trust includes the filesystem/hash tools, Python and its byte transfer, exporter/format parsing, the two kernel executables, their standard logical foundations, OS/hardware, and the documentation-to-formal-specification correspondence above. Two implementations and negative controls reduce checker risk; they do not prove the absence of common bugs or establish an unformalized floating-point execution specification.
