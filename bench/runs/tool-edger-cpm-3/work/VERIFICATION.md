# Verification of the shipped edgeR artifact

Both universal requirements fail. The evidence includes executions of the
**unmodified `edgeR.so` bytes**, executions of the supplied R functions, and
exact arithmetic certificates proved with Frama-C 33.0 WP. The WP certificates
are a small mathematical model of these witnesses; they are not a verified
translation of the entire Wasm module or the R interpreter.

## R1: failure through intermediate overflow

Input: a one-row, one-column double matrix containing `1e308`, library size
`1e308`, and `nthreads=1`. The output array initially contains the count, as
required by the C interface. Both inputs are positive, finite binary64 values.

- Exact mathematical CPM: `(c / c) * 1000000 = 1000000`.
- Actual artifact output: positive infinity.
- Executable evidence: `verification/artifact.cjs`, which asserts both results.

The artifact multiplies the count by one million before dividing by the library
size. This overflows even though the final exact result is representable. Thus
there is **no finite universal absolute or relative rounding-error bound** for
R1 on its stated domain. This is not an unavoidable overflow of the final
answer; dividing first gives exactly one million on this input. No general
finite-input accuracy theorem is claimed.

`1e308` has bits `0x7fe1ccf385ebc8a0`, checked by the executable witness. Its exact
value is `5010420900022432 * 2^971`. The positive binary64 round-to-nearest
overflow threshold is `(2^54 - 1) * 2^970`. WP proves the following postconditions
of `r1_reference_and_overflow()` in `verification/certificates.c`:

```text
2 * 5010420900022432 * 1000000 > 18014398509481983
((real)5010420900022432 / 5010420900022432) * 1000000 = result
result = 1000000
```

Cancelling the common positive power of two explains the overflow inequality.
The proof checks that inequality and the exact reference value; the infinity
observation comes from execution of the artifact, not from treating C floating
point operations as real arithmetic.

## R2: failure at the minimum-count boundary

Reproduce with these ordinary matrix inputs:

```r
y <- matrix(c(10, 10), nrow=1)
filterByExpr(y, group=c("A", "A"), lib.size=c(1000009, 1000009))
# actual: FALSE; the R2 count condition requires TRUE
```

All tuning parameters take their documented defaults. The required number of
samples is two. Both libraries equal their median, so the exact scaled count
threshold is ten in each sample. Both counts reach ten; their total, twenty,
also exceeds the documented `min.total.count=15`. Consequently this example
satisfies the documented total-count condition as well as R2's sample condition.

Let `RN` mean binary64 round-to-nearest, ties-to-even. Here no rounding tie occurs.

```text
artifact CPM = RN(10000000 / 1000009)
             = 5629448869173297 / 2^49
             = bits 0x4023fff43420d831
R cutoff     = RN(RN(10 / 1000009) * 1000000)
             = 5629448869173298 / 2^49
             = bits 0x4023fff43420d832
```

The cutoff is one ULP above both computed CPMs. Zero samples pass, and the
function rejects the gene. The `1e-14` tolerance applies to the number of
samples and the total count, not to the CPM comparison, so it does not help.
This refutes the exact minimum-count equivalence requested in R2; the supplied
R implementation does perform its literal comparison against its rounded CPM
cutoff.

`verification/artifact.cjs` checks the two actual artifact outputs bit for bit.
`verification/filter_witness.R` sources **both supplied R files unchanged**,
runs their `cpm` and `filterByExpr` functions, checks these same bit patterns,
and asserts `actual == FALSE` and `expected == TRUE`.

### Exact WP certificate statements

All contracts below are in `verification/certificates.c`. Define:

```text
N(n,d,q) := d > 0 and -d < 2*(n-q*d) < d
B(q)     := 4503599627370496 <= q < 9007199254740992
D        := 562949953421312       (= 2^49)
E        := 590295810358705651712 (= 2^69)
```

`N` certifies a strict nearest integer to the rational `n/d`; `B` certifies a
normal 53-bit significand. The exact postconditions, in addition to
`assigns \nothing` on every function, are:

| Function | Preconditions | Proved postconditions |
|---|---|---|
| `raw_numerator()` | none | `B(result)`; `N(10000000*D,1000009,result)`; `10000000*D-result*1000009=440327`; `result=5629448869173297` |
| `cutoff_div_numerator()` | none | `B(result)`; `N(10*E,1000009,result)`; `10*E-result*1000009=-463220`; `result=5902904977442260` |
| `cutoff_mul_numerator(s)` | `s=5902904977442260` | `B(result)`; `N(s*1000000,1048576,result)`; `s*1000000-result*1048576=-123648`; `result=5629448869173298` |
| `r2_documented_keep()` | none | `result=1` |
| `r2_rounded_keep()` | none | `result=0` |
| `r2_counterexample()` | none | `result=1` (the two decisions differ) |

The integer numerators represent values on their binary64 binades: divide by
`2^49` for CPM and final cutoff, and by `2^69` for the intermediate `10/L`.
Multiplication `10*1000000` is exact. The nearest-point certificates justify
the displayed rounding results under IEEE binary64 semantics. In particular,
the exact signed errors relative to `x=10000000/1000009` are:

```text
artifact CPM - x = -440327 / (1000009 * 2^49)
R cutoff     - x =  559682 / (1000009 * 2^49)
```

The artifact CPM error in this witness is strictly less than half an ULP in
magnitude. It is enough to break R2 because the cutoff rounds differently.
The certificates use mathematical integers and a real cast only in R1's
reference division. There are no custom axioms, admitted lemmas, or unspecified
external functions. The model's final sample-count comparison uses integer two;
the actual tolerance-bearing R expression is checked by the R execution.

## Connection to the shipped artifact

`edgeR.so` is 96,558 bytes, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

The Node harness checks this size and hash, instantiates those exact bytes,
and calls the real exported `calc_cpm_raw`. It supplies wasm32 `cmx` structures
with the layout in `src/edgeR.h`, a repeated library-size row (type 2), and an
output array initialized to the counts. The artifact's own `get_row` executes.
Neither the arithmetic nor that helper is replaced.

The module imports its memory, table, globals, and R allocation functions. The
harness supplies fresh zeroed allocations and checks the exact allocation/free
call sequence. All other imported functions throw if called. The module start
runs normally; optional C++ constructors are not called and are not needed by
this kernel. No full R WebAssembly distribution is available or assumed.

The R harness supplies the absent `makeCompressedMatrix` helper for this input
shape and intercepts the `.Call` boundary in the sourced functions' environment.
It sends the validated counts and library sizes to the Node harness, which
executes the real artifact. It preserves doubles using round-trip decimal
serialization. This adapter is explicitly part of the trusted harness; it is
not a claim to have run the entire package in an Emscripten R installation.
The R filtering logic, CPM input checks, and cutoff calculation run as supplied.

The input and evidence files are pinned in `verification/SHA256SUMS`. The C
sources are contextual evidence, not a substitute for the named artifact.
There is no universal correctness proof for arbitrary shapes, groups, designs,
threading, or other package functions; one valid counterexample suffices for
each universal requirement.

## Reproduction

From this directory, with no network:

```sh
sh verification/check.sh
```

The script runs exactly:

```sh
sha256sum -c verification/SHA256SUMS
wasm-tools validate edgeR.so
node verification/artifact.cjs
Rscript --vanilla verification/filter_witness.R
frama-c --check-wp . verification/certificates.c \
  -wp -wp-rte -wp-cache none -wp-model Typed+float \
  -wp-prover alt-ergo -wp-timeout 10
```

Success means exit status zero, all checksum lines `OK`, both counterexample
`PASS` markers, WP `Proved goals: 58 / 58`, and the script's final
`ALL VERIFICATION CHECKS PASS`. These markers mean the **counterexamples** are
confirmed, not that R1 or R2 holds. `wasm-tools validate` is silent on success.
The WP run includes runtime-error obligations and uses no cached prover results.
Its generic warnings about skipped pointer-alignment and function-pointer guards
are inapplicable: the certificate C file has neither pointers nor indirect calls.
`verification/check.log` records the completed run.

Observed tools: Frama-C 33.0, Alt-Ergo 2.5.4, Node v26.11.1, R 4.6.1,
wasm-tools 1.262.0. Lean and Wasmtime are not needed by these checks.

## Review and trust inventory

The reviewer must read the requirement interpretation, the rational/binary64
mapping above, and these evidence files. Sizes are bytes and lines:

| File | Bytes | Lines | Role |
|---|---:|---:|---|
| `verification/certificates.c` | 3,593 | 103 | All seven WP contracts, definitions, and decision model |
| `verification/artifact.cjs` | 4,238 | 96 | Exact-byte execution, host imports, memory layout, assertions |
| `verification/filter_witness.R` | 2,524 | 46 | R boundary adapter, actual calls, expected decision |
| `verification/check.sh` | 420 | 10 | Reproduction orchestration |
| `verification/SHA256SUMS` | 1,078 | 13 | Checksums of inputs and evidence |
| `R/cpm.R` | 3,771 | 114 | Supplied R CPM functions executed by the harness |
| `R/filterByExpr.R` | 3,745 | 115 | Supplied filtering functions executed by the harness |
| `README.md` | 1,287 | 13 | Requirements and artifact identity |
| `CHECK.md` | 784 | 8 | Delivery requirements |
| `man/filterByExpr.Rd` | 7,329 | 161 | Threshold, sample-size and total-count documentation |
| `man/cpm.Rd` | 7,280 | 160 | CPM documentation |
| `src/edgeR.h` | 14,858 | 381 | Context for wasm32 `cmx` layout |
| `src/compute_cpm.c` | 6,996 | 266 | Context for kernel interface and arithmetic order |

Also trusted: Frama-C's parser, ACSL semantics, WP/Qed and its Why3/Alt-Ergo
integration, Alt-Ergo, Node's WebAssembly engine and binary64 behavior, R's
interpreter and binary64 operations, the IEEE decoding/rounding interpretation,
and the checksum/validation tools. SMT solver results are not Lean proof terms.
The execution adapters and the mapping from certificates to IEEE semantics are
review obligations, not separately mechanized refinement proofs. The saved
log and this report are explanatory records, not extra proof assumptions.
