# Verification result

Both README requirements have counterexamples. No implementation source or shipped binary was changed. The evidence combines execution of the original artifact with exact arithmetic certificates, replayed by three proof kernels.

| Requirement | Result |
| --- | --- |
| R1 | The unrestricted accuracy claim fails through intermediate overflow: finite positive inputs with an exactly representable CPM produce positive infinity. No universal finite rounding-error bound holds on the stated domain. |
| R2 | The exact minimum-count criterion fails at an ordinary integer-count boundary, even with the documented total-count condition satisfied. |

## Reproduce everything

From this directory, run:

```sh
./check.sh
```

Success means exit status 0 and the final line:

```text
SUCCESS: R1 and R2 counterexamples reproduced; three kernels accepted the certificates and rejected both false proofs.
```

This command checks hashes, regenerates the Wasm callers, executes the original binary under Wasmtime and V8, executes the shipped R functions, compiles fresh Lean proofs, exports their complete dependency closure, checks it with three kernels, and checks both deliberately false proof streams. It needs no network. It uses Python 3, Node, Rscript, wasm-tools, wasmtime, Lake/Lean 4.35.0, the installed Mathlib, and `leanexport`, `leanchecker`, `con-ron`, and `nanoda_bin` in the Lean installation's `bin` directory. Missing tools, unsupported checking, and unexpected failures fail the command.

Generated evidence is in `.verification/`: `edgeR.wat`, `env.wat`, `caller.wat`, binary outputs `case0.bin` through `case4.bin`, `proofs.ndjson`, the two `false-*.ndjson` streams, checker configurations/logs, and `review-size.txt`. Nothing in this directory is accepted as a cached verification result: the command regenerates its inputs and proofs.

## R1: overflow destroys a representable answer

Use a 1 by 1 matrix with count and library size both equal to `2^1023`, a finite positive binary64 value with encoding `0x7fe0000000000000`. Initialize the caller-owned CPM buffer with that count and call the real `calc_cpm_raw` with `nthreads = 1`.

The exact mathematical value is

```text
(2^1023 / 2^1023) * 1000000 = 1000000.
```

One million is exactly representable as binary64 (`0x412e848000000000`). Both Wasmtime and V8 instead observe output `0x7ff0000000000000`, positive infinity. This is `case0`; `case1` checks the ordinary `c = L = 1000000` control and returns one million.

The shipped Wasm multiplies by one million before dividing by the library size. Its intermediate product overflows. Thus this witness has no finite absolute or relative error against the finite mathematical target, despite a representable final answer and `c <= L`. It refutes any interpretation of R1 promising a finite rounding-error bound for every finite count and positive finite library size. If “as double-precision arithmetic allows” expressly permits intermediate overflow, this demonstrates the exception that such a contract must state; it does not establish an unrestricted accuracy guarantee.

The exact arithmetic is certified by `Certificate.bit_values` and `Certificate.overflow_target` in [Proofs/Certificate.lean](Proofs/Certificate.lean). The executable result is checked in [verification/artifact.py](verification/artifact.py).

The finite rounding error proved for the boundary witness below is exactly `1 / 19327352832`, or `4/9` of an ulp and less than half an ulp. That is a statement about that input, not a global error bound or a proof of all nonoverflowing executions.

## R2: a gene at min.count is rejected

Run the unmodified R function with all defaults:

```r
filterByExpr(matrix(c(10, 8, 10, 8), nrow=2))
```

The column-major matrix is:

| Gene | Sample 1 | Sample 2 | Total |
| --- | ---: | ---: | ---: |
| A | 10 | 10 | 20 |
| B | 8 | 8 | 16 |

Both column sums, and hence both library sizes and their median, are 18. With no group or design, the required sample number is 2; neither the large-group adjustment nor the cap changes it. Gene A reaches the default `min.count = 10` in both samples and exceeds the default `min.total.count = 15`.

Nevertheless, the returned vector is `c(FALSE, FALSE)`. Gene A's Wasm CPM and the R cutoff differ:

| Quantity | Encoding | Exact value |
| --- | --- | --- |
| Actual CPM, `fl(fl(10 * 1000000) / 18)` | `0x4120f4471c71c71c` | `1193046471111111 / 2147483648` |
| Exact CPM and exact cutoff | — | `5000000 / 9` |
| R cutoff, `fl(fl(10 / 18) * 1000000)` | `0x4120f4471c71c71d` | `4772185884444445 / 8589934592` |

Here `fl` denotes a binary64 arithmetic operation. The actual CPM is strictly below the exact threshold, which is strictly below the computed cutoff. The two encodings are adjacent. Their gap is `1 / 8589934592`, one ulp at this magnitude. The actual CPM's error is below half an ulp, but the independently rounded cutoff is higher, so `CPM >= CPM.Cutoff` is false in both samples. The R tolerance `1e-14` applies to sample-number and total-count comparisons; it does not apply to this CPM comparison.

[verification/filter.R](verification/filter.R) checks this outcome, the precise cutoff bytes, and the kept-gene control with row A changed to `(11,11)` and row B to `(7,7)`. The exact arithmetic is certified by `Certificate.boundary_target`, `Certificate.boundary_gap`, `Certificate.boundary_error`, and `Certificate.bit_values`.

There is also a separate discrepancy with a literal reading of README's “exactly when”: `filterByExpr(matrix(10,1), lib.size=1e6, min.sample.size=1)` rejects its gene because its total count is below 15; setting `min.total.count=0` keeps it. This behavior is documented in `man/filterByExpr.Rd`, so this second example identifies an omitted condition in README, rather than a violation of that additional documentation. The two-sample boundary example satisfies the additional condition.

These results concern the exact minimum-count criterion requested in README. The R code does implement a conjunction of its computed, rounded CPM predicate and its total-count predicate. Taking that operational expression itself as the specification would be a different claim; no universal theorem about every R execution is asserted here.

## Exact formal statements

The following are the declaration types in [Proofs/Certificate.lean](Proofs/Certificate.lean), with their single local definition. All divisions in `Rat` are exact rational divisions. `normal64` is the usual value formula for a positive finite normal binary64 encoding, whose exponent field is between 1 and 2046; it is not a floating-point execution model. It is applied only to such encodings. Positive infinity is identified separately by its exponent and zero fraction fields.

```lean
def Certificate.normal64 (b : Nat) : Rat :=
    ((2^52 + b % 2^52 : Nat) : Rat) / 2^(1075 - b / 2^52) *
      2^(b / 2^52 - 1075)

Certificate.bit_values :
    Certificate.normal64 0x7fe0000000000000 = 2^1023 ∧
    Certificate.normal64 0x4120f4471c71c71c = (1193046471111111 : Rat) / 2147483648 ∧
    Certificate.normal64 0x4120f4471c71c71d = (4772185884444445 : Rat) / 8589934592 ∧
    0x7ff0000000000000 / 2^52 = (2047 : Nat) ∧
    0x7ff0000000000000 % 2^52 = (0 : Nat)

Certificate.overflow_target :
    (0 : Rat) < 2^1023 ∧
    (2^1023 : Rat) / 2^1023 * 1000000 = 1000000

Certificate.boundary_target :
    (10 : Rat) / 18 * 1000000 = 5000000 / 9 ∧
    (10 : Rat) + 10 ≥ 15

Certificate.boundary_gap :
    (1193046471111111 : Rat) / 2147483648 < 5000000 / 9 ∧
    (5000000 : Rat) / 9 < 4772185884444445 / 8589934592 ∧
    (4772185884444445 : Rat) / 8589934592 -
      1193046471111111 / 2147483648 = 1 / 8589934592

Certificate.boundary_error :
    (5000000 : Rat) / 9 - 1193046471111111 / 2147483648 = 1 / 19327352832 ∧
    (1 : Rat) / 19327352832 < (1 / 8589934592) / 2
```

These are arithmetic certificates for the counterexamples. They do not assume an execution observation as a Lean axiom, and do not purport to prove a Wasm or R interpreter correct. The implementation results are executable demonstrations, as permitted for requirements that fail.

## Connection to the shipped implementation

The binary tested is exactly the 96,558-byte `edgeR.so` named in README:

```text
sha256 e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

[verification/SHA256SUMS](verification/SHA256SUMS) pins this binary, the requirements, supplied checking instructions, both R files, both documentation files, the C source and header, and the original Lake configuration/toolchain files. The check rejects changed inputs.

The callers link the original binary as a separate module. They use its exported `make_cmx` to construct descriptors, then call its exported `calc_cpm_raw`; the binary's own `get_row`, loops, loads, arithmetic, and stores run. No C source is rebuilt, no Wasm function body is replaced, and no arithmetic expression copied from C is used to supply outputs. Each of the eleven output words is reproduced independently by Wasmtime and Node's V8 before being used as evidence.

The bounded host environment supplies zero-initialized allocation and a nonreusing allocator; freeing is a no-op because these short executions never reuse freed blocks. Other imported host functions trap if called. Unused dynamic-linking globals and the table are placeholders. The script audits the reached call graph in the disassembly: `make_cmx` and `get_row` call nothing; `calc_cpm_raw` can call only `get_row`, `R_chk_calloc`, and `R_chk_free`; none of these Wasm bodies accesses globals or makes indirect calls. Thus the placeholders and omitted package initialization are irrelevant to the calls tested. Buffers, descriptors, heap, and stack occupy separate regions of the shared memory.

The R check loads `R/cpm.R` and `R/filterByExpr.R` verbatim in a fresh `Rscript --vanilla` process. Since native R cannot directly load a Wasm dynamic library, a witness-only ABI adapter supplies `makeCompressedMatrix` and intercepts `.Call` at the R/Wasm boundary. It accepts only the exact matrices and library sizes of the recorded examples, and returns the bit-for-bit results of the real Wasm matrix calls; unknown inputs fail. Dispatch, library-size calculation, median, cutoff calculation, sample requirements, comparisons, row sums, tolerance, and the final conjunction all execute the shipped R code. This adapter is part of the review surface, not a general implementation of edgeR's R ABI.

## Independent checking and rejection tests

[verification/check.py](verification/check.py) forcibly recompiles the project proof files and exports the five named certificates and every transitive dependency. It permits only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; the export contains no `sorryAx`, compiler-trust axiom, or custom axiom. It then replays the whole export from scratch with:

1. Lean 4.35.0's C++ kernel, using `leanchecker --from-export`.
2. The independent Rust kernel `con-ron`, using `--verified --jobs=2`.
3. The independent Rust kernel Nanoda 0.4.19, with an explicit axiom allowlist and Nat/String kernel extensions enabled.

The frontend and `leanchecker` are counted as one kernel implementation. Mathlib tactics generate proof terms; their successful execution alone is not accepted as evidence. All three replayers check the exported dependency closure, rather than trusting imported project proof objects.

The same harness appends two well-formed, deliberately invalid declarations to that otherwise valid export: `Eq.refl 0` claimed as a proof of `False`, and `Eq.refl 0` claimed as a proof of `(0 : Nat) = 1`. Every kernel must reject both. Lean and `con-ron` must return a rejection status of 1. Nanoda reports failed type equality by a Rust assertion: the harness requires status 101, a `src/tc.rs` location, and the specific `self.def_eq(u, v)` assertion. A parser panic or unrelated crash is not counted as rejection. The six rejection logs are retained alongside the successful replay logs. Nanoda's successful log can include an “Unable to print axioms” pretty-printer warning; its typechecker reports no errors.

## Review and trust surface

The custom formal surface is **one three-line definition and five closed theorem statements**. The entire certificate file, including imports, proofs, comments, and whitespace, is **48 lines, 1,888 bytes**. `Proofs.lean` adds only its one-line import (26 bytes). There is no handwritten model of C, Wasm, or R.

The executable bridge, checking driver, and hash manifest must also be reviewed. Physical sizes are:

| File | Lines | Bytes |
| --- | ---: | ---: |
| `Proofs/Certificate.lean` | 48 | 1,888 |
| `Proofs.lean` | 1 | 26 |
| `check.sh` | 3 | 53 |
| `verification/check.py` | 145 | 6,348 |
| `verification/artifact.py` | 96 | 5,238 |
| `verification/run-wasm.mjs` | 13 | 714 |
| `verification/filter.R` | 39 | 2,132 |
| `verification/SHA256SUMS` | 12 | 954 |
| **Total added formal/checking files** | **357** | **17,353** |

The check regenerates these counts in `.verification/review-size.txt`. The two shipped R files add 229 lines / 7,516 bytes of implementation to understand. The requirements and documentation are separate supplied inputs, pinned in the manifest. The report itself, generated files, and external tools are excluded from the table.

The full standard-library/Mathlib proof export has **3,745 declaration records** (252,077 NDJSON lines / 13,151,460 bytes): 1,286 definitions, 2,233 theorems, 218 inductive blocks, 4 quotient records, 3 axioms, and 1 opaque declaration. These include the local certificates. Recursors and constructors are contained within inductive blocks, so these are record counts, not counts of individual constants. They are all replayed; they are not 3,745 additional hand-written verification assumptions. A semantic review still relies on the usual meanings of Lean's natural numbers, exact rationals, arithmetic/order operations, and the three standard axioms. The rational representation and arithmetic definitions come from Lean/Mathlib, rather than being invented here.

The remaining trusted components are the three proof-checker implementations and their execution platforms, Lean's exporter and the scripts connecting its output to the stated declarations, SHA-256 and file I/O, wasm-tools' import/disassembly handling, the Wasmtime and V8 runtimes and standard binary64 encoding/arithmetic, and the R interpreter/base functions. The adapter and allocator assumptions are described above. Cross-checking and false-proof tests reduce reliance on any one checker; they do not prove these tools or the host hardware correct. No claim is made about other edgeR entry points or universal correctness on a restricted replacement domain.
