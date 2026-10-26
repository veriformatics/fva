# Verification of edgeR CPM and expression filtering

Both requirements have counterexamples on their stated domains. The evidence combines kernel-checked FVA proofs of the decoded artifact's arithmetic and IEEE-754 results with executions of the unchanged Wasm and R code. It does **not** constitute a formal proof of complete C-function execution or of an R interpreter.

## R1 — fails without a restriction excluding intermediate overflow

Use a one-row, one-column matrix, `c = L = 2^1020`, and `nthreads = 1`. Both inputs are finite, positive, exactly represented binary64 values (`0x7fb0000000000000`). The exact required CPM is

```
(c / L) * 1000000 = 1000000.
```

The unchanged `edgeR.so` writes positive infinity. Its cell update computes `fl(fl(c * 1000000) / L)`: the multiplication overflows before division. A computation of `(c/L)*1000000` would be exact for this input.

Consequently there is **no finite absolute or relative rounding-error bound over the unrestricted domain in R1**. The error for this input is positive infinity. No general finite-error theorem is claimed. If “as double-precision arithmetic allows” is intended to permit arbitrary intermediate overflow, that interpretation must be distinguished from a finite rounding-error guarantee about the specified real expression.

Machine-checked supporting statements, in [Proofs/Proof.lean](Proofs/Proof.lean):

```lean
theorem Proofs.artifact_arithmetic_holds : Proofs.artifact_arithmetic
theorem Proofs.overflow_witness_holds : Proofs.overflow_witness
```

These are the exact theorem types; their complete statements and supporting definitions are in [Proofs/Spec.lean](Proofs/Spec.lean). `artifact_arithmetic` states that the export `calc_cpm_raw` names function 160 and that a selected inner-loop instruction sequence is exactly the 13 listed load/multiply/load/divide/store instructions. `overflow_witness` conjoins that artifact fact with:

- `dbl 0x7fb0000000000000` is a finite number with positive real value;
- its real value divided by itself, times 1,000,000, equals 1,000,000;
- FVA's binary64 multiplication of it by `dbl 0x412e848000000000` (1,000,000) has the unique result `+infinity`;
- division of `+infinity` by this positive input has the unique result `+infinity`.

The complete-function counterexample is asserted by [verification/check.R](verification/check.R), which calls the original artifact through [verification/artifact_cpm.py](verification/artifact_cpm.py). Recorded output is in [verification/counterexamples.txt](verification/counterexamples.txt).

## R2 — fails as an exact equivalence with the documented count threshold

Use these arguments to the shipped R function:

```r
y <- matrix(c(10, 10), nrow=1)
filterByExpr(y, lib.size=c(36, 36), min.sample.size=2)
```

All other arguments have their defaults, including `min.count=10`, `min.total.count=15`, `large.n=10`, and `max.n.samples=40`. The single gene reaches 10 reads in both required samples. Its total is 20, so it also satisfies the separately documented total-count condition. The median library size is 36, equal to each sample's library size, so the documented scaling does not change the exact count boundary.

Nevertheless the unchanged R code returns `FALSE`:

| Quantity | Binary64 value | IEEE bits |
| --- | --- | --- |
| Artifact CPM, `(10 * 1000000) / 36` | `277777.77777777775` | `0x4110f4471c71c71c` |
| R cutoff, `(10 / 36) * 1000000` | `277777.77777777781` | `0x4110f4471c71c71d` |

These adjacent doubles differ by `2^-34`. The first comparison `CPM >= CPM.Cutoff` fails in both samples. The R code's `tol=1e-14` is applied to sample-number and total-count comparisons, not to the CPM comparison.

Machine-checked supporting statement, in [Proofs/Proof.lean](Proofs/Proof.lean):

```lean
theorem Proofs.threshold_witness_holds : Proofs.threshold_witness
```

Its exact statement is the `threshold_witness` definition in [Proofs/Spec.lean](Proofs/Spec.lean). It conjoins `artifact_arithmetic` with these four singleton result sets in FVA's IEEE semantics:

```
fmul(0x4024000000000000, 0x412e848000000000) = {0x416312d000000000}
fdiv(0x416312d000000000, 0x4042000000000000) = {0x4110f4471c71c71c}
fdiv(0x4024000000000000, 0x4042000000000000) = {0x3fd1c71c71c71c72}
fmul(0x3fd1c71c71c71c72, 0x412e848000000000) = {0x4110f4471c71c71d}
```

Here each hexadecimal argument/result denotes `dbl bits`, and each operation uses `f64fmt`. The theorem also states strict inequality between the real values of the last two CPM/cutoff patterns. Singleton equality proves uniqueness, not just existence of an allowed result.

[verification/check.R](verification/check.R) asserts the actual artifact CPM, the cutoff, the total-count condition, and the actual `FALSE` returned by the sourced `filterByExpr`. It also sources the supplied `R/cpm.R` unchanged.

This refutes R2's exact count-based equivalence, even when the additional total-count condition is included. The supplied documentation's operational formula, interpreted as a comparison of the two differently rounded computed CPM values, does describe this rejection. The finding is a boundary discrepancy between that floating calculation and the exact count-based requirement, not a claim that R executes its written comparison incorrectly. No universal verification of other filtering inputs or branches is claimed.

## Connection to the shipped files

The target is the original 96,558-byte Wasm file, not a recompilation of `src/compute_cpm.c`:

```
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb  edgeR.so
b43ab97191a448ef8d141decdef802be3329801692a9c9a0618cf5ef874eb39b  R/cpm.R
abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f  R/filterByExpr.R
45cef156e3cd3163cb7e20276d921a57715e71c27beb2487f6514b789c21c98a  man/filterByExpr.Rd
```

[Proofs/Lifted.lean](Proofs/Lifted.lean) was generated with:

```sh
lake exe fva lift edgeR.so Proofs/Lifted.lean --ns Proofs.Lifted
```

Its `Proofs.Lifted.decode_eq` proves `decode bytes len = .ok module` by kernel evaluation. FVA independently checks the generated file and its connection to the on-disk artifact, and replays `decode_eq` alongside the three project theorems. The audit reports `Proofs.Lifted (edgeR.so) [lifted]: matches`.

The artifact imports R/Emscripten functions, memory, globals, and a table. The concrete runner supplies a fresh 32-page memory, a valid table, ABI globals, zero-initialized allocation, and a free operation without reuse. Other imported functions trap if called, apart from two explicitly named constructor-support stubs. No arithmetic is supplied by a host stub. The wrapper writes valid one-row `cmx` structures, count and library buffers, invokes the original `calc_cpm_raw` export, and reads its output buffer. The original Wasm bytes are never rewritten or replaced by an extracted function.

The R test replaces the unavailable R-to-Wasm FFI with this runner. Its restricted `makeCompressedMatrix` adapter accepts the row-vector library representation used by these tests; its `.Call` adapter accepts only the raw-CPM call for one-row matrices and one thread. R coercion, input checks, cutoff calculation, sample counting, total counting, and filtering run from the supplied sources. This is a concrete integration harness, not a formal model of R or a test of the package's SEXP conversion wrappers.

## Reproduction

Run from this directory, with the supplied offline Lean/Mathlib/FVA installation and `Rscript`, `python3`, `wasmtime`, and `wasm-tools` on PATH:

```sh
sha256sum edgeR.so R/cpm.R R/filterByExpr.R man/filterByExpr.Rd
lake build
python3 verification/check_fva.py
Rscript verification/check.R
```

Success means:

1. The hashes match those above.
2. `lake build` exits zero and prints `Build completed successfully`.
3. The FVA command exits zero and prints `fva trust: PASS`, all three named claims, both kernel replays accepted, and the artifact link matching.
4. The R command exits zero and prints both `COUNTEREXAMPLE` messages followed by `All counterexample assertions passed.` Any failed assertion or trapped Wasm call causes failure.

`check_fva.py` builds the checker executable **outside the judged project** in a temporary `/tmp` directory, linking the supplied prebuilt FVA objects using its supplied response file and the installed Lean toolchain. It copies FVA's source, manifest and pinned canaries unchanged, relocates only FVA object paths, and invokes:

```
<external-checker> trust . --spec-module Proofs.Spec --root-module Proofs
```

It saves the full report to [verification/fva-trust.txt](verification/fva-trust.txt) and deletes the temporary checker afterward. This is an external link of the supplied built package, not a fresh recompilation of every FVA source. The recorded audit accepted all proofs in `leanchecker` (65 seconds) and independent `con-leche` (71 seconds). Of the 72 known-false canaries, Lean rejected 71 and accepted one documented exception; con-leche rejected 69 and declined three, accepting none. FVA's full coverage/known-exception rules passed. A PASS here certifies the three stated supporting claims; it does not assert that R1 or R2 holds.

The numerical counterexamples can also be checked directly:

```sh
python3 verification/artifact_cpm.py 1.1235582092889474e307 1.1235582092889474e307
python3 verification/artifact_cpm.py 10,10 36,36
```

Expected outputs are `inf`, and two lines each equal to `277777.77777777775`, respectively. The runner verifies the artifact SHA-256 before every invocation and disables Wasmtime's disk cache.

## Review and trust surface

Sizes below count physical lines, including comments, unless stated otherwise.

| File/component | Size | Role |
| --- | ---: | --- |
| `Proofs/Spec.lean` | 73 lines / 3,350 bytes; **47 code lines** by FVA | Read the complete claim definitions, code selection, bit-pattern decoding, and intended interpretation. |
| `verification/artifact_cpm.py` | 90 lines / 4,715 bytes | Trust/review import generation, allocator, `cmx` layout, wrapper, exact artifact invocation, and result transport for the concrete executions. |
| `verification/check.R` | 40 lines / 1,887 bytes | Trust/review the narrow FFI adapters and all counterexample assertions. |
| `verification/check_fva.py` | 42 lines / 1,923 bytes | Trust/review external checker linking, unchanged FVA inputs, audit invocation and exit-status propagation. |
| `R/cpm.R`, `R/filterByExpr.R` | 114 + 115 lines; 3,771 + 3,745 bytes | Actual R implementation executed; review relevant paths and trust the installed R interpreter. |
| `man/filterByExpr.Rd` | 161 lines / 7,329 bytes | Interpret the documented CPM scaling, required samples and extra total-count guard. |
| `Proofs/Proof.lean` | 85 lines / 3,132 bytes | Kernel-checked proof implementation; no manual trust in tactics or proof text required. |
| `Proofs/Lifted.lean` | 897 lines / 1,167,921 bytes | Generated artifact representation; generated-file, byte-link and decoder proofs are checked, not manually assumed. |
| FVA `FVA/Spec/**/*.lean` | 23 files / 3,606 lines | Reviewed-once Wasm, binary, numeric and trust specifications. |
| FVA `FVA/Trust/*.lean` and `FVA/Tool/*.lean` | 887 + 2,894 lines | Supplied audit/export/link/canary/process glue, including commands unrelated to this task. |

The formal proof stack additionally trusts the pinned Lean 4.35.0/Mathlib v4.35.0 environment and the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`. Both replay kernels accepted the proofs; no `sorry`, custom axiom, or `native_decide` is used. FVA's verified decoder and floating implementation connect executable calculations to its reviewed specifications. Concrete execution additionally trusts Wasmtime, wasm-tools, Python, the C ABI interpretation in the harness, and R's binary64 evaluation. Logs are records, not substitutes for rerunning the commands.

No shipped Wasm, C source, R source, or documentation was changed. No universal error bound on a restricted safe-input domain, complete Wasm execution theorem, R formal semantics, or source-to-binary compilation theorem is claimed or needed for these concrete counterexamples.
