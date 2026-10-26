# Verification results

Both universal requirements in README.md have counterexamples. The original
software was left unchanged. The evidence combines execution of the shipped
WebAssembly bytes with Frama-C 33.0 WP proofs of the arithmetic witnesses.
It is not a proof of the whole WebAssembly module or of arbitrary R executions.

## R1: intermediate overflow produces infinity for a finite answer

Use a one-row, one-column matrix, initialized output count `c = 1e308`, library
size `L = 1e308`, and `nthreads = 1`. Here both decimal inputs denote the same
finite binary64 value `0x1.1ccf385ebc8a0p+1023`.

The exact required value is `(c / L) * 1000000 = 1000000`, which is exactly
representable as binary64. The original `calc_cpm_raw` returns positive infinity,
with bits `0x7ff0000000000000`. Its multiplication by one million overflows
before its division by L. This is demonstrated by
`verification/check_artifact.py`, which calls the original export, not a C
recompilation. A control input `c = 10, L = 1000000` returns exactly 10.

Thus R1, with its unrestricted positive library sizes and finite counts, cannot
have a universal finite absolute or relative rounding-error guarantee: this
witness has infinite error despite a finite, exactly representable answer.
The implementation does obey the individual IEEE operations on this witness;
the failure is that their order does not deliver a rounded finite CPM answer.
Restricting inputs to avoid intermediate overflow would change R1's domain.

The supporting WP results in `verification/witnesses.c` are:

* `exact_reference(c)`: for every finite binary64 c with c > 0,
  `((real)c / (real)c) * 1000000 == 1000000`.
* `overflow_reference()`: returns exactly `1000000.0`. Its proved assertions
  additionally establish that the particular c is positive, that its exact-real
  product with 1000000 exceeds the largest finite binary64 number, and that
  its exact-real CPM is 1000000. The function computes division before
  multiplication, with zero rounding error on this input.

These theorems support the reference calculation; the infinity result comes
from executing the shipped artifact. WP is not asked to prove an overflowing
C operation safe.

## R2: a count exactly at min.count is rejected

Run the shipped R functions with this matrix and all default arguments:

```r
y <- matrix(c(10, 10, 8, 8), nrow=2, byrow=TRUE)
filterByExpr(y)
```

The first gene has counts `(10,10)`. Both column sums are 18, so the median
library size is 18. The required sample number is 2, `min.count` is 10, and
the total count 20 exceeds the default `min.total.count = 15`. There is no
group-size reduction or sample-number cap in this example. The documented
scaling makes the exact count threshold `10 * 18 / 18 = 10` in each sample.
Consequently this gene satisfies the count-based requirement, including the
additional documented total-count condition.

Nevertheless, the actual result is `c(FALSE,FALSE)`. The first gene's CPM in
each sample is computed by the artifact as

```
RN(RN(10 * 1000000) / 18)
  = 0x1.0f4471c71c71cp+19
  = 1193046471111111 / 2147483648
```

The R cutoff is computed in the other order:

```
RN(RN(10 / 18) * 1000000)
  = 0x1.0f4471c71c71dp+19
  = 4772185884444445 / 8589934592
```

Here RN denotes binary64 rounding to nearest, ties to even. The cutoff is
exactly one ULP (`1 / 8589934592`) above the CPM. Neither sample passes the
CPM comparison. The `1e-14` tolerance is applied to the required number of
samples and to the total count, not to the CPM comparison, so it does not
prevent this failure.

The following are exact WP-proved statements in `verification/witnesses.c`.
Every listed function has `assigns \nothing`; the first two additionally
ensure that their result is finite.

| Function | Exact result/postcondition |
| --- | --- |
| `raw_boundary()` | `(real)result = 1193046471111111 / 2147483648`; signed error relative to `5000000 / 9` is exactly `-1 / 19327352832` |
| `cutoff_boundary()` | `(real)result = 4772185884444445 / 8589934592`; signed error relative to `5000000 / 9` is exactly `5 / 77309411328` |
| `filter_boundary()` | `result == 0`, for the C translation of this gene's two comparisons, sample-number test, total-count test, and conjunction |
| `specification_boundary()` | `result == 1`, for the concrete count requirements `10 >= 10`, `10 >= 10`, and `20 >= 15` |
| `r2_disagreement()` | `result == 1`, computed as `filter_boundary() != specification_boundary()` |

All assertions in the file are also proved, including CPM < cutoff, zero
passing samples, and failure of the sample-number test. The two signed-error
equalities are concrete rounding-error results, not general error bounds.

`verification/check_filter.R` sources the unmodified `R/cpm.R` and
`R/filterByExpr.R`, and asserts the exact values and the dropped first gene.
Its `.Call` adapter executes the original `calc_cpm_raw` on the entire 2-by-2
matrix, including both rows and columns. As a control, it verifies that the
first gene is kept for `matrix(c(10,10,0,0),2,byrow=TRUE)`, whose library sizes
are 10 and 10.

This refutes README R2's equivalence to reaching the scaled **count** threshold.
The manual also describes the algorithm using a computed `CPM >= CPM.cutoff`
predicate; the observed result agrees with that floating-point predicate.
The counterexample identifies the rounding discrepancy between these two
descriptions. It does not rely on omitting the documented total-count rule.

## Connection to the delivered software

The executed artifact is the original `edgeR.so`, 96,558 bytes, SHA-256:

```
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

`verification/inputs.sha256` also pins both R files, both supplied C/header
files, both manual files, README.md, and CHECK.md. The checking script checks
all these hashes. No shipped input file was edited.

`check_artifact.py` uses `wasm-tools print` to discover the module's imports
and generates small host/driver modules. Wasmtime preloads **edgeR.so itself**.
There is no extraction, patching, replacement, or recompilation of its code.
For review, `wasm-tools print edgeR.so` shows `calc_cpm_raw` exported as function
160, calling `get_row` (207), and using `f64.mul` followed by `f64.div` with
the constant 1000000.

The host supplies 2 MiB of memory, a function table, and the required globals.
Its only nontrapping function imports are zero-initializing, aligned bump
allocation for `R_chk_calloc` and a no-op `R_chk_free`. The driver verifies
exactly two allocations and two frees for each call. Other function imports
trap if called. No freed block is reused or observed. The supplied buffers,
data segment, and heap occupy disjoint memory ranges.

The driver initializes 32-byte Wasm32 `cmx` structures according to
`src/edgeR.h`: a full count matrix and a row-repeated double library vector
(`type = 2`), with null row selections. Counts are stored in column-major
order and copied into the in-place CPM buffer. It calls the original export
with `nthreads = 1`. The scalar replay checks the raw returned bits; the R
replay checks the full matrix results after round-trip decimal conversion.

The R adapter supplies `makeCompressedMatrix` and `.Call` because the full
edgeR R package/runtime is not installed. Its supported domain is explicitly
limited to the small matrices used here. It delegates the numeric CPM work
to the original artifact and does not implement its formula in R. Each
requested matrix entry is obtained by running the complete matrix kernel in
a fresh Wasmtime instance. This adapter and its struct layout are part of
the review boundary; this is not an execution under a complete WebR runtime.

WP checks a scalar C model of the witness arithmetic and R predicates. Its
connection to the executable is the matching concrete artifact/R replays and
the manually reviewable operation correspondence, not a proved compiler or
decompiler equivalence. No universal claims about other matrix layouts,
thread counts, R methods, or inputs are made.

## Reproduction

From this directory, with the tools specified in the task and R/Python on PATH:

```sh
sh verification/check.sh
```

This runs exactly:

```sh
sha256sum -c verification/inputs.sha256
python3 verification/check_artifact.py
Rscript verification/check_filter.R
frama-c --check-wp . verification/witnesses.c \
    -wp -wp-rte -wp-model Typed+float -wp-prover qed,alt-ergo -wp-timeout 10 -wp-cache none
```

Success means exit status zero, every hash marked `OK`, both replay `PASS`
messages, `Proved goals: 64 / 64`, and the final
`PASS: all counterexample replays and all WP goals checked`. A changed artifact,
unexpected runtime result, trapping host call, or unproved WP goal fails the
check. WP's cache is disabled, so provers run again. No network access or Lean
build is used. The generated modules are
recreated under `verification/generated/` on each run.

The observed transcript is `verification/results.log`; rerunning the command,
rather than trusting that transcript, checks the results. Tool versions used:
Frama-C 33.0 (Arsenic), Alt-Ergo 2.5.4, Wasmtime 50.0.0, wasm-tools 1.262.0,
R 4.6.1, and Python 3.14.8. WP's warning about `1e-14` records its actual binary64
representation. Its generic warnings about skipped alignment and function
pointer guards do not affect this pointer-free C proof model.

## Review and trust boundary

The following are the authored definitions, models, and scripts to review.
Sizes include comments and blank lines.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `verification/witnesses.c` | 71 | 2,094 | ACSL statements and concrete C arithmetic/predicate model; no axioms or assumed function contracts without implementations |
| `verification/check_artifact.py` | 140 | 6,739 | Artifact identity, generated host/driver definitions, scalar bit checks |
| `verification/check_filter.R` | 53 | 2,467 | R runtime adapter, witness and control assertions |
| `verification/check.sh` | 9 | 424 | Reproduction command sequence and failure propagation |
| `verification/inputs.sha256` | 9 | 708 | Identities of the supplied inputs |

The generated text modules are also available for inspection: `env.wat`
(91 lines, 6,172 bytes), `GOT.mem.wat` (41 lines, 2,380 bytes), `GOT.func.wat`
(35 lines, 1,981 bytes), and `driver.wat` (46 lines, 2,485 bytes). They are
generated from the reviewed Python script and artifact imports.

For the interpretation and code correspondence, review README.md (13 lines,
1,287 bytes), `man/filterByExpr.Rd` (161 lines, 7,329 bytes),
`R/filterByExpr.R` (115 lines, 3,745 bytes), `R/cpm.R` (114 lines, 3,771 bytes),
the `cmx` declaration in `src/edgeR.h` (whole file: 381 lines, 14,858 bytes),
and the raw CPM loop in `src/compute_cpm.c` (whole file: 266 lines, 6,996 bytes).
The binary itself remains the 96,558-byte artifact identified above.

The trusted tools are Frama-C's parser/constant evaluation, ACSL and WP's IEEE
floating-point model, Qed, Alt-Ergo and its floating-point theory, wasm-tools,
Wasmtime's WebAssembly implementation, base R's double arithmetic and S3/base
operations, Python's subprocess/hash/bit handling, and the host OS/toolchain.
These are automated WP proofs and executable counterexamples, not
Lean-kernel-checked proof certificates. The only general input assumption in
the proof file is the explicit finite-positive precondition of
`exact_reference`; the concrete witness proofs have no input preconditions.
