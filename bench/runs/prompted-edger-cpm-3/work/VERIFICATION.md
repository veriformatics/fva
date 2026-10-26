Both README requirements have reproducible counterexamples. The original software was not modified. The results below are execution demonstrations against the shipped code, supported by small, independently checked arithmetic proofs. They are not universal correctness theorems or a formalization of the Wasm or R operational semantics.

R1 fails on the finite, exactly representable input `c = L = 2^1020`, in a one-row, one-column matrix, with one thread. `L > 0`, and the exact mathematical CPM is `1,000,000`, also exactly representable as binary64. Executing the shipped `calc_cpm_raw` returns positive infinity, with bits `0x7ff0000000000000`. The artifact multiplies the count by `1,000,000` before dividing by the library size. That intermediate product exceeds `2^1024` and overflows; division by the finite library size leaves infinity. The final result therefore has infinite absolute and relative error against the specified mathematical value. No finite rounding-error bound holds for all inputs in R1. Rounding the complete exact expression would have zero error on this witness. This does not claim a discrepancy with IEEE arithmetic for the implementation's particular sequence of operations; it demonstrates why that sequence cannot meet the unrestricted mathematical requirement with a finite error bound.

The executable witness is in [verify/check.py](verify/check.py), using [verify/runtime.py](verify/runtime.py). The C source's multiplication order is visible at [src/compute_cpm.c](src/compute_cpm.c#L142), but the check executes the compiled artifact, without recompilation or extraction of a replacement function.

R2 fails under both the README's literal sample-only equivalence and the documentation's fuller rule:

| Input, with all unspecified options at their defaults | Required/documented result | Shipped result |
| --- | --- | --- |
| `y = matrix(10, 1, 1)`, `lib.size = 1e6`, `min.sample.size = 1` | The README sample criterion is true: one sample reaches count 10 and CPM 10. | `FALSE`, because the total count is below the default `min.total.count = 15`. The documentation explicitly describes this additional condition, so this example refutes the README's literal equivalence rather than that fuller documentation. |
| `y = matrix(c(20, 0), 1, 2)`, `lib.size = c(1e6, 1e6)`, `min.sample.size = 1 + 2^-48` | `FALSE` even including the documented total-count condition. CPMs are exactly `[20, 0]`, cutoff is exactly 10, total count is 20, and only one sample qualifies. One is less than the required `k = 1.0000000000000036`. Neither the large-group reduction nor the maximum-samples cap changes `k`. | `TRUE`: [R/filterByExpr.R](R/filterByExpr.R#L108) subtracts `1e-14` from `k` before comparing. This tolerance is absent from the exact documented sample rule. |

[verify/filter.R](verify/filter.R) executes these inputs and asserts both the expected predicates and actual results. The second example uses the documented explicit effective sample-size argument; it does not require rounding an integer group size or an ill-formed design matrix.

The exact supporting theorem statements, in [Proofs/Arithmetic.lean](Proofs/Arithmetic.lean), are:

```lean
namespace Evidence

theorem r1_witness :
    0 < Nat.pow 2 1020 ∧
    Nat.pow 2 1020 < Nat.pow 2 1023 ∧
    Nat.mul (Nat.pow 2 1020) 1000000 = Nat.mul 1000000 (Nat.pow 2 1020) ∧
    1000000 < Nat.pow 2 53 ∧
    Nat.pow 2 1024 < Nat.mul (Nat.pow 2 1020) 1000000

theorem r2_total : (10 : Nat) ≤ 10 ∧ ¬ (15 : Nat) ≤ 10

theorem r2_tolerance :
    Nat.pow 2 48 < Nat.add (Nat.pow 2 48) 1 ∧
    Nat.pow 10 14 < Nat.pow 2 48 ∧
    (15 : Nat) ≤ 20

end Evidence
```

The file supplies `by decide` proofs checked by reduction, without `native_decide`, admitted axioms, or `sorry`. The R1 equality is the cross-multiplied exact quotient equation. The R2 inequalities establish that `0 < 2^-48 < 10^-14` and that the total count passes. These theorems certify arithmetic facts used to interpret the execution results; they do not assert that a handwritten model equals the artifact. Binary64 overflow behavior and the R branch results are checked by execution.

The artifact connection is direct. [verify/inputs.sha256](verify/inputs.sha256) pins the original README, CHECK, both R files, both documentation files, both C/header files, and the complete 96,558-byte `edgeR.so`. Its SHA-256 is `e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb`, matching the README. Hashes are checked before and after verification.

The runtime harness preloads that exact `edgeR.so` into Wasmtime. It supplies shared linear memory, full double `cmx` descriptors with the header's field layout, an allocation host, and a wrapper that calls the exported `calc_cpm_raw` and reads output bits. The artifact's internal library-size extraction and matrix loops execute unchanged. Its other imported functions trap if reached. Allocation uses fresh zero-filled memory in each instance; freeing is a no-op within that single-call instance. No source or artifact instructions are replaced. The generated disassembly is saved as `.verification/edgeR.wat` for inspection, not used as an alternative implementation.

For R2, both shipped R files are sourced unchanged into a fresh Rscript process. The small adapter supplies `makeCompressedMatrix` and the `.Call` boundary for these numeric-matrix/vector-library-size fixtures. It serializes the inputs, invokes the actual Wasm matrix function, and reconstructs its result in R's column-major order. It does not compute CPM in R or Python. The original R code performs dispatch, validation, median scaling, sample-size adjustment, comparisons, total-count filtering, and the final conjunction. The unavailable full R-universe dynamic loader and native R SEXP entry wrapper are not verified; this adapter is an explicit review obligation. No claim is made about other methods, presets, compressed layouts, threading, or memory safety in general.

From this directory, run the single offline command:

```sh
python3 verify/check.py
```

It requires the installed Lean 4.35 toolchain, Wasmtime, wasm-tools, Python 3, Rscript, and R's installed `jsonlite` package. It locates `leanexport`, `leanchecker`, and `nanoda_bin` in `lean --print-prefix`'s `bin` directory. Mathlib remains the project's installed dependency; these small proofs only need `Init`. No network access is used.

Success is exit status 0 with the final line:

```text
VERIFICATION PASSED: R1 and R2 are refuted by the reproduced witnesses; supporting proofs and negative controls passed.
```

This means the counterexamples and checking controls passed, not that the software satisfies the requirements. Any compilation, hash, execution, kernel-acceptance, or expected-rejection failure makes the command fail. The script freshly compiles both result proof modules, exports the three named theorems and their dependencies, checks their presence, forbids every axiom, and replays the same export into an empty Lean kernel and Nanoda's independent Rust kernel. It does not count the Lean frontend and Lean's replay checker as independent kernels.

The script also compiles [verify/Canary.lean](verify/Canary.lean) and checks its valid export in both kernels. It then changes only the theorem types to submit the well-scoped false proofs `False := True.intro` and `(0 : Nat) = 1 := Eq.refl 0`. Both kernels must reject both for type mismatch, rather than missing imports or malformed serialization. Lean must additionally reject [verify/Bad.lean](verify/Bad.lean). Expected negative exits are tested; an always-accepting or always-rejecting checker cannot pass these controls.

Generated proof exports, checker configurations, and diagnostic logs are in `.verification/`; `.verification/sizes.json` records the review footprint. Lean reports acceptance for the valid export. Nanoda reports 166 declarations with no typechecker errors; this installed version also emits a nonfatal `Unable to print axioms` pretty-printer message for the axiom-free export. Its positive exit status must still be zero. The false-proof Nanoda logs show the failing `self.def_eq(u, v)` type-checking assertion; the Lean logs identify the incompatible types.

The complete authored verification footprint, including comments and blank lines, is:

| File to review | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Arithmetic.lean` | 26 | 893 | Three exact propositions and proofs; no custom semantic definitions. |
| `Proofs.lean` | 1 | 25 | Imports the result module. |
| `verify/runtime.py` | 97 | 4,502 | Artifact loading, host generation, ABI layout, result extraction. |
| `verify/filter.R` | 38 | 1,801 | R boundary adapter and both R2 fixtures. |
| `verify/check.py` | 129 | 6,472 | Assertions, integrity checks, fresh compilation, export replay, negative controls. |
| `verify/Canary.lean` | 7 | 193 | Valid proof seeds and two trivial types for deliberate corruption. |
| `verify/Bad.lean` | 2 | 60 | Deliberately false frontend proof. |
| `verify/inputs.sha256` | 9 | 708 | Identity of original inputs. |
| **Total** | **309** | **14,654** | Excludes this explanatory report and generated files. |

The human-facing formal result file is only 26 lines/893 bytes and adds no program model. Its notation and definitions come from Lean `Init`: natural numbers and their arithmetic/order operations, equality, conjunction, negation, and decidability. The full exported dependency closure, including proofs as well as definitions, is 166 declarations and 267,441 serialized bytes: 85 definitions, 27 theorems, 17 inductive types, 20 constructors, and 17 recursors, with zero axioms or opaque declarations. The independent kernels recheck that entire closure. Standard logical/numeric meanings, the exporter's preservation of source declarations, and the mapping between the informal README and the displayed propositions remain review assumptions.

The execution demonstrations additionally trust the Wasm and R runtimes, the small adapter and check scripts above, SHA-256/file I/O, the installed tool binaries, and the operating system/hardware. Independent proof replay reduces reliance on a single proof kernel; it does not formally verify these runtimes or the artifact adapter. The original source/documents remain review inputs for understanding the interface and the requirements, rather than substitute verified implementations.
