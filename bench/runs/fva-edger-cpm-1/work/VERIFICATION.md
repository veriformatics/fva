# Verification of edgeR CPM and filtering

The unrestricted requirements in README.md have counterexamples. The Lean results concern the original compiled functions, in the explicit calling context below. The R results combine execution of the shipped R filter with CPM values separately checked on the original Wasm. They are not a formal verification of an R interpreter or a complete installed edgeR package.

## R1: intermediate overflow prevents a universal finite error bound

Use a one-row, one-column matrix, count `c = 2^1023`, positive library size `L = 2^1023`, and `nthreads = 1`. Both inputs are finite, exactly represented positive binary64 values, with bits `0x7fe0000000000000`.

The original `calc_cpm_raw` writes positive infinity, bits `0x7ff0000000000000`. Its multiplication by `1000000` overflows before division. In contrast, the exact real value `c / L * 1000000` is exactly `1000000`; evaluating division first in binary64 also gives exactly `1000000`.

Consequently there is no finite absolute or relative rounding-error bound over the entire stated domain. For this input the error is infinite in the extended-real sense. This refutes R1 interpreted as a universally accurate approximation to the stated formula, even for finite nonnegative counts and finite positive library sizes. If “as double-precision arithmetic allows” is intended to permit intermediate overflow even when the answer is representable, that weaker interpretation is consistent with this result; no universal finite-error guarantee has been established. No theorem here asserts a general error bound on an overflow-free restricted domain.

The exact Lean theorem declaration is:

```lean
theorem Proofs.r1_counterexample_holds : Proofs.r1_counterexample
```

Its complete statement is the definition `r1_counterexample` in [Proofs/Spec.lean](Proofs/Spec.lean); its proof is in [Proofs/Proof.lean](Proofs/Proof.lean). The claim conjoins:

* `CallReturns` for the original export in the explicit linking context, returning no values and writing the infinity bits at address 32840;
* finiteness and positivity of the input value in FVA's binary64 semantics;
* exact equality of its real-valued CPM to `1000000`.

`CallReturns` establishes termination and absence of traps for every execution allowed by the specified context. The C function returns `void`; the checked numeric result is its memory write, not a Wasm return value. The proof uses FVA's sound deterministic runner, evaluated by the Lean kernel. The fuel 1000 is only a proof mechanism; the claim is a total-correctness statement without fuel.

## R2: the stated sample/count equivalence is false

### Additional total-count condition

Call `filterByExpr.default(matrix(10, 1, 1), lib.size=1000000, min.sample.size=1)`, leaving the tuning parameters at their defaults. The gene reaches `min.count=10` in the required one sample, with CPM exactly 10 and cutoff exactly 10. Nevertheless, the result is `FALSE`: its total count 10 is below the default `min.total.count=15`.

The documentation explicitly describes this additional condition. Thus this example exposes an omission in README R2's sample-only “exactly when”, rather than a disagreement with that part of the package documentation.

The exact Lean theorem declaration is:

```lean
theorem Proofs.r2_total_witness_holds : Proofs.r2_total_witness
```

The claim in [Proofs/Spec.lean](Proofs/Spec.lean) conjoins an artifact-level `CallReturns` writing CPM 10 with `filterDecision 1 1 10 15 = false`. `filterDecision` is an explicitly reviewed rational model of the final sample-count and total-count comparisons, including tolerance `1/10^14`. It is not a semantics of R. [verification/filter_test.R](verification/filter_test.R) also calls the shipped R function and asserts `FALSE`.

### A rounding boundary, even when total count passes

Use `y = matrix(10, 1, 2)`, `lib.size = c(18,18)`, `min.sample.size=2`, with the other defaults. Both counts reach 10 at the median library size 18, and total count 20 passes the minimum-total condition. Yet the function returns `FALSE`:

| Quantity | Binary64 value | Bits |
|---|---:|---|
| Artifact CPM: `(10 * 1000000) / 18` | 555555.5555555555 | `0x4120f4471c71c71c` |
| R cutoff: `(10 / 18) * 1000000` | 555555.5555555556 | `0x4120f4471c71c71d` |

The values differ by one ULP (`2^-33`). Neither sample satisfies the computed `CPM >= CPM.Cutoff`. The `1e-14` tolerance is applied to the required number of samples and total count, not to this CPM comparison. The documented CPM comparison is implemented; interpreting it as an exact threshold on scaled raw counts loses this floating-point boundary effect.

The exact Lean theorem declaration is:

```lean
theorem Proofs.r2_rounding_witness_holds : Proofs.r2_rounding_witness
```

The claim in [Proofs/Spec.lean](Proofs/Spec.lean) conjoins:

* artifact execution for the scalar count/library-size pair, writing `0x4120f4471c71c71c`;
* total execution of `cutoffComparison`, an explicit FVA numeric model of R's `actualCPM >= (10/18*1000000)`, returning integer false (`i32 0`);
* `filterDecision 0 2 20 15 = false`.

The proof is in [Proofs/Proof.lean](Proofs/Proof.lean). The two-column matrix execution is additionally asserted on the original Wasm by `artifact_test.py`. The shipped R filter is exercised by `filter_test.R`. These executable checks and the reviewed translation connect the scalar/suffix proofs to the R counterexample; there is no claim of a machine-proved translation of arbitrary R programs.

## Connection to the shipped files

The artifact is exactly the unchanged 96,558-byte `edgeR.so`, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

[Proofs/Lifted.lean](Proofs/Lifted.lean) was generated by `fva lift` without modification. It holds the bytes and a kernel-checked `decode_eq`. FVA's link check compares its numeral, length, and generated text against `edgeR.so`. No recompilation or replacement implementation of the CPM kernel is used. The target is Wasm function index 160, decoded defined-function index 86; `get_row` is Wasm index 207, decoded index 133.

[Proofs/Context.lean](Proofs/Context.lean) uses FVA's `allocModule` to allocate **every original defined function** with the original types, index mapping and exports. Imported allocation/free are small Wasm shims supplying separate 4-byte and 8-byte scratch blocks in initially zero memory; unused function imports are host functions. Caller-owned structs and arrays are initialized according to `cmx` in `src/edgeR.h`. Count and output share the in-place CPM buffer, as required by the C interface.

The formal call proofs start in this allocated, explicitly initialized calling context. They do **not** prove `Instantiated` or `LoaderReady`, all import contracts, general allocation, the R `.Call` wrapper, or arbitrary matrix sizes. The selected execution calls no unspecified host function. Independently, `artifact_test.py` embeds the complete **original binary bytes** in a WAST script, supplies typed imports, executes its start function and exported relocations/constructors, and invokes the original export. Unused imports trap if called; allocator/free and constructor support are explicit. Wasmtime assertions check the overflow, ordinary CPM, both boundary operation orders, and the two-column boundary matrix. This executable evidence checks that the formal calling-context witness is realizable with the artifact rather than asserting full formal loader correctness.

`filter_test.R` loads the unchanged `R/filterByExpr.R`. Since an installed edgeR runtime and its R/C bridge are absent, it supplies a narrow `cpm` callback returning the CPM matrices asserted in the Wasm test, with input guards. The filtering body, its cutoff computation, sample-size calculation, total-count check, and conjunction execute as shipped. This dependency substitution and the manual correspondence between R and the Lean numeric/rational models are part of the review boundary. No theorem about the bytes of the R interpreter or an installed edgeR package is claimed.

[verification/sources.sha256](verification/sources.sha256) pins the Wasm, R sources, documentation, and supplied C sources/header. The R check verifies these hashes before sourcing the filter. The C sources are used to review the calling convention, not as a substitute for the artifact proof.

## Reproduction (offline, from this directory)

Run:

```bash
bash verification/check.sh
```

This checks source hashes, runs `lake build`, the Wasmtime assertions and the R assertions, then builds and runs a copy of FVA **outside the project** in a temporary directory. Only the external copy's Lake package-directory metadata is adjusted to use the existing local packages; it downloads nothing. The CLI entry point and executable are rebuilt there. Success means exit status zero, successful Lean build, both executable checks printing `PASS`, and the FVA verdict `PASS`. FVA `PASS` here validates the stated counterexample/model theorems, not the original requirements.

The individual proof and executable commands are:

```bash
sha256sum -c verification/sources.sha256
lake build
python3 verification/artifact_test.py
Rscript --vanilla verification/filter_test.R
```

The decisive FVA command, with `FVA` pointing to an externally built binary, is:

```bash
"$FVA" trust "$PWD" --spec-module Proofs.Spec --root-module Proofs
```

The existing lift can be regenerated with:

```bash
lake exe fva lift edgeR.so Proofs/Lifted.lean --ns Proofs.Lifted
```

A saved external-verifier JSON report is [verification/fva-trust.json](verification/fva-trust.json). The validation status and review-surface counts are recorded below.

## Review and trust

A reviewer must read the claim definitions and linking/input context, plus the R-model correspondence and executable harnesses. The generated lift and proof implementation are kernel checked; they do not replace reviewing the statements. Sizes are recorded below.

The inherited FVA trust boundary includes its Wasm syntax, binary grammar, operational/numeric/instantiation semantics, claims and trust specification; its verified implementations; the unverified collection/link/export/replay glue; Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`); Lean/Mathlib and the external kernels. The executable demonstrations additionally trust Python's harness, wasm-tools, Wasmtime and R. The hash tool binds the files used in those demonstrations. `cutoffComparison` is a manually reviewed translation of the R arithmetic; `filterDecision` uses exact rationals rather than an R floating-point semantics. Neither model is silently presented as verification of the complete R program.

### Recorded validation

Validation completed on 2026-10-25 (UTC):

* `lake build`: success, including all three theorems and the full-artifact decode proof.
* Wasmtime WAST assertions: success, including the two-column boundary input.
* Shipped R filtering-body assertions: success for both rejection witnesses; all pinned source hashes matched.
* External `fva trust`: **PASS**, exit 0, `issues: []`. `leanchecker` and independently implemented `con-leche` both accepted the complete exported proof closure and `decode_eq`. All artifact link checks were true. Each theorem uses only Lean's three standard axioms.
* FVA checked 72 known-false canaries per kernel. Its policy accepted the documented existing exceptions: `leanchecker` accepted the known `prelude-15704/replaced-prelude` canary; `con-leche` declined three unsupported tutorial cases and rejected the other 69. The report retains these details; this is not a claim that every kernel rejected every canary.

The externally rebuilt verifier and the supplied verifier have the same executable SHA-256, `5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407`. The saved JSON report contains the exact claims, axiom closures, byte links, kernel statuses, canary outcomes and review modules.

### Sizes of the review material

Line counts below include comments and blank lines; bytes are file sizes. FVA separately reports **85 code lines** in the formal review surface: 37 in `Proofs.Spec` and 48 in `Proofs.Context`.

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs/Spec.lean` | 62 | 3,459 | Exact claims, numeric comparison model, rational filtering model |
| `Proofs/Context.lean` | 73 | 3,347 | Original-function allocation, import shims, input layout |
| `verification/artifact_test.py` | 97 | 5,147 | Exact-binary WAST construction, linking context, assertions |
| `verification/filter_test.R` | 30 | 1,555 | CPM dependency substitution and execution of shipped filter |
| `verification/check.sh` | 32 | 1,371 | Offline reproduction and external-verifier build |
| `verification/sources.sha256` | 7 | 557 | File identity manifest |
| `R/filterByExpr.R` | 115 | 3,745 | Shipped filtering logic, reviewed against models and executed |
| `R/cpm.R` | 114 | 3,771 | R-to-C interface context; not executed by these tests |
| `man/filterByExpr.Rd` | 161 | 7,329 | Documented thresholds, scaling and total-count condition |
| `man/cpm.Rd` | 160 | 7,280 | CPM documentation |
| `src/edgeR.h` | 381 | 14,858 | Review the `cmx` layout and CPM signature |
| `src/compute_cpm.c` | 266 | 6,996 | Source context; execution proofs use the binary instead |

The machine-checked proof file is 60 lines / 2,538 bytes. The generated lift is 897 lines / 1,167,921 bytes, holding the whole 96,558-byte artifact and its decoded module; its generation, byte identity and decoding are checked rather than manually trusted.

For the inherited tool base, `fva/FVA/Spec/` contains 23 Lean files, 3,606 lines / 161,903 bytes. The principal unverified verdict-collection/replay/canary/CLI glue (`FVA/Trust/{Collect,Replay,Canary}.lean` and `FVA/Tool/Trust.lean`) totals 1,036 lines / 50,676 bytes. The complete supplied FVA Lean source tree, excluding build products, is 129 files, 24,215 lines / 1,106,254 bytes; most of this is verified implementation and proofs rather than additional project specifications. The tool's linked trust report describes which layers remain trusted.
