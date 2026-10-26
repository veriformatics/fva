Both requirements fail as stated. The evidence consists of executions of the shipped files, supported by arithmetic certificates checked by three proof kernels. No implementation source was changed.

Run this single command from this directory, without network access:

```sh
python3 verify/check.py
```

Success is exit status 0 with the final line:

```text
VERIFICATION PASS: both requirements refuted; all three kernels accepted the certificates and rejected both false proofs.
```

The command checks original-file hashes, runs the actual WASM in Node and Wasmtime, executes the shipped R functions, rebuilds the Lean certificates, exports their dependency closure, and replays both valid and deliberately invalid proofs. It writes disassembly, certificates, and individual logs to `.verification/`. It deletes and rebuilds this project's `.lake/build/`; it does not rebuild Mathlib. Dependencies are Python 3, Node, Rscript, wasm-tools, wasmtime, and the installed Lean 4.35 toolchain, including `leanexport`, `leanchecker`, `con-ron`, and `nanoda_bin`. No additional Python, R, or Node packages are required.

R1 fails on a one-row, one-column matrix with count and library size both equal to the finite, exactly representable binary64 number `2^1023` (`0x7fe0000000000000`). Pass `nthreads = 1` and initialize the in-place CPM buffer with that count. The exact answer is **1,000,000**, which is exactly representable. Evaluating the stated expression `(c/L)*1000000` also produces exactly 1,000,000 with zero rounding error. Both runtimes executing the shipped `calc_cpm_raw` return **positive infinity**, bits `0x7ff0000000000000`.

The artifact multiplies the count by 1,000,000 before division: its relevant instructions are `f64.load; f64.const 1000000; f64.mul; ... f64.load; f64.div; f64.store`. The intermediate product exceeds `2^1024`, so it overflows before division can cancel the large library size. This witness admits no finite real-valued absolute or relative error bound for the returned result. Thus a universal bounded-rounding guarantee for R1 cannot be proved under its sole library-size precondition `L > 0`. This is not an example where the correct final answer itself requires overflow. Execution checks are in `verify/check.py`, `verify/runtime.mjs`, and `verify/driver.wat`; the supporting theorem is `Evidence.r1_witness` in `Proofs/Counterexamples.lean`.

R2 fails even when the documented total-count condition is included. Run:

```r
y <- matrix(c(20, 16), ncol=1)
filterByExpr(y, min.count=20)
```

All other parameters use their shipped defaults. The default library size and median library size are 36. The required sample count is 1. The first gene has exactly `min.count` reads in that sample, and its total count 20 exceeds the default `min.total.count = 15`. Its exact CPM equals the documented cutoff, `20/36*1000000 = 5000000/9`; the specified exact rule therefore keeps it. The actual result is `c(FALSE, FALSE)`.

The first gene's CPM from the shipped artifact is `555555.5555555555`, bits `0x4120f4471c71c71c`. R computes the cutoff as `555555.55555555562`, bits `0x4120f4471c71c71d`. The values differ by exactly one binary64 step, `2^-33`. Their exact common-denominator forms are respectively `4772185884444444/8589934592` and `4772185884444445/8589934592`. They straddle `5000000/9`. Multiplication before division in the CPM calculation and division before multiplication in the cutoff calculation cause the boundary rejection. `verify/filter.R` checks both exact bit patterns and the actual returned Boolean vector. The arithmetic certificate is `Evidence.r2_boundary_witness`.

There is also a separate R2 sample-count counterexample, away from a CPM boundary:

```r
filterByExpr(matrix(c(20, 0), nrow=1),
             lib.size=c(1e6, 1e6), min.sample.size=1 + 2^-50)
```

Exactly one sample qualifies; the gene's total count is 20. The documented required number is strictly greater than one: `1.0000000000000009`. The exact sample-count rule rejects it, but the shipped function returns `TRUE`, because it subtracts `tol = 1e-14` before the comparison. Its exact binary64 tolerance value is `6338253001141147/2^99`, greater than `2^-50`. `verify/filter.R` checks the input conditions and actual result; `Evidence.r2_tolerance_witness` certifies the relevant arithmetic. These two R2 examples concern the literal “exactly when” requirement; an explicitly approximate specification could describe the implemented behavior instead.

The exact supporting theorem statements follow. They are in namespace `Evidence` in `Proofs/Counterexamples.lean`. All arithmetic is on natural numbers: the division in R1 is exact integer division, and the comparisons between fractions in R2 are expressed by cross multiplication. The proof of each is `by decide`, checked by kernel reduction. These statements certify the mathematics of the inputs and reference values; they do not assert that a handwritten model simulates the software.

```lean
theorem r1_witness :
    0 < (2^1023 : Nat) ∧
    2^1023 ≤ (2^53-1)*2^971 ∧
    (2^1023*1000000)/2^1023 = 1000000 ∧
    2^1024 ≤ 2^1023*1000000 ∧
    1000000 < 2^53

theorem r2_boundary_witness :
    (20 : Nat) ≥ 20 ∧ 20 ≥ 15 ∧ (1 : Nat) ≥ 1 ∧
    20*1000000*9 = 5000000*36 ∧
    4772185884444444*9 < 5000000*8589934592 ∧
    5000000*8589934592 < 4772185884444445*9 ∧
    (4772185884444444 : Nat) < 4772185884444445

theorem r2_tolerance_witness :
    (1 : Nat)*2^50 < 2^50+1 ∧
    (2^99 : Nat) < 6338253001141147*2^50 ∧
    (20 : Nat) ≥ 10 ∧ 0 < (10 : Nat) ∧ 20 ≥ 15
```

The connection to the artifact is execution of the original **96,558 bytes** of `edgeR.so`, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

`verify/artifacts.json` records hashes of the README, CHECK, both shipped R files, both documentation files, and both supplied C/header files as well. The check rejects changed originals. Node instantiates `edgeR.so` directly. Wasmtime preloads that same file directly; it does not execute a reconstructed or recompiled copy. Disassembly is used only to generate import providers. Both runtimes agree on exact output bits for zero, an ordinary finite case, the R2 boundary, and the R1 overflow.

The host providers supply shared memory, the wasm32 `cmx` structures, zero-initialized allocation, and free. Unused function imports throw or trap. Ignoring free is sufficient for these fresh, short-lived instances. `verify/driver.wat` is a one-cell call harness; it contains no CPM arithmetic. `verify/runtime.mjs` also contains no CPM arithmetic. The structure layout is the one in `src/edgeR.h`.

For R2, `verify/filter.R` sources **both original R files unchanged**. The surrounding edgeR package is not installed. The harness supplies `makeCompressedMatrix` for the exercised double-matrix/row-vector-library-size path and intercepts `.Call` to invoke the real WASM export through Node. The shipped `cpm.default` validation and the complete shipped `filterByExpr.default` execute. No filter or CPM algorithm is substituted. This adapter and its wasm32 memory layout are part of the review surface.

Every exported arithmetic certificate and its dependencies is checked by Lean's default C++ kernel (`leanchecker --from-export`), the independent Rust `con-ron --verified` kernel, and the independent Rust Nanoda kernel. The exporter includes the transitive proof dependencies. There are no axiom or opaque declarations in the export, and no unsafe definitions. Nanoda has an empty permitted-axiom list. Lean also reports no axioms for all three theorems. There is no `sorry`, `native_decide`, compiler trust axiom, or assumed implementation-correctness axiom in the certificates.

The same kernels first accept a positive control from `Proofs/Controls.lean`. The check then generates two syntactically valid export streams: each retains the proof `Eq.refl 0` but declares its type to be respectively `(0 : Nat) = 1` and `(1 : Nat) < 0`. The changed theorem is placed after its expression dependencies. All three kernels reject both streams **during type checking**, with a type mismatch; missing-file and parser failures do not count as successful negative controls. The command requires the expected rejection statuses and diagnostic markers. Original and mutated streams and all kernel logs are retained in `.verification/`.

The human review surface is small because there is no custom WASM interpreter, floating-point semantics, C model, R model, or compiler-correctness layer. The three formal statement signatures total **18 lines, 610 UTF-8 bytes** (including separating blank lines), with **zero custom supporting definitions**. Their standard dependencies are natural-number arithmetic and logic from Lean's `Init`, including notation instances. For a conservative bound that does not hide any definitions, the complete exported closure, including proof terms as well as statement dependencies, is **191 declaration records, 7,571 JSON lines, 409,225 bytes** in `.verification/evidence.ndjson`. Inductive records also contain constructors and recursors; “191” counts records rather than claiming that each generated constant is a separate record.

The additional source files to inspect are:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexamples.lean` | 41 | 1,633 | Statements, comments, proofs, axiom reports |
| `Proofs/Controls.lean` | 8 | 317 | Positive seed and false propositions |
| `Proofs.lean` | 1 | 30 | Library import |
| `verify/check.py` | 178 | 8,744 | Hash checks, execution, export/replay, negative controls |
| `verify/runtime.mjs` | 42 | 2,146 | Node host and original-artifact call |
| `verify/driver.wat` | 17 | 736 | Wasmtime call harness |
| `verify/filter.R` | 37 | 2,018 | R adapters, inputs, assertions |
| `verify/artifacts.json` | 11 | 774 | Original-file identity |

That is **335 lines, 16,398 bytes** across the listed files. The two shipped R files add 229 lines, 7,516 bytes of implementation to inspect for the R linkage. The interpretation of the README/documentation, binary64's specified meanings, host adapters, file/byte handling, runtime engines, and proof-checker implementations remain trusted. Independent engines and kernels reduce dependence on any one implementation; they do not remove these assumptions. In particular, the kernels certify the arithmetic, while the executable counterexample steps are reproducible execution evidence, not a deductive semantics theorem about WASM or R. Neither failed universal requirement is claimed as proved.
