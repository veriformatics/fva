# Verification results

Both requirements, read as the mathematical statements in README.md, have
counterexamples. The original software was not changed. Frama-C 33.0 WP checks
the exact integer rounding certificates in `verification/wp.c`; execution of
the shipped WebAssembly and supplied R code demonstrates the failures.
These are counterexamples with supporting proofs, not a universal correctness
proof of either implementation.

## R1: intermediate overflow defeats the stated universal formula

Use a 1-by-1 matrix, initialize the output/count buffer to `c = 2^1023`, and
set the library size to `L = 2^1023`, with `nthreads = 1`. Both inputs are
finite, exactly representable binary64 numbers, and `L > 0`.

The shipped `calc_cpm_raw` returns positive infinity:

| Quantity | Exact value or binary64 bits |
|---|---|
| `c`, `L` | `2^1023`, bits `0x7fe0000000000000` |
| Mathematical `c / L * 1000000` | `1000000`, exactly representable |
| Actual output | `+Infinity`, bits `0x7ff0000000000000` |

The artifact multiplies before dividing. The multiplication overflows even
though dividing first would give the exact finite result. In round-to-nearest
binary64, the largest finite number is `2^1024 - 2^971`, and the overflow
rounding midpoint is `T = 2^1024 - 2^970`. WP proves that
`2^1023 * 1000000 > T`. Dividing the resulting infinity by finite positive `L`
leaves infinity. There is consequently no finite absolute or relative error
bound valid for every input permitted by R1.

`verification/artifact.mjs` executes and asserts this counterexample on the
original artifact. `overflow_certificate` in `verification/wp.c` supplies its
exact integer arithmetic certificate. No claim that WP directly verified the
Wasm floating-point instructions is made.

For the finite R2 witness below, the proved raw-CPM absolute rounding error is
exactly `1/19327352832`, downward, and its relative error is exactly
`1/10737418240000000`. These are bounds for that witness, not universal R1
bounds.

## R2: an exact threshold count can be rejected

Run the supplied R function with:

```r
y <- matrix(c(10, 10), nrow=1)
filterByExpr(y, group=c("A", "A"), lib.size=c(18, 18))
```

All other arguments retain their defaults. The required sample number is 2;
neither the large-group adjustment nor the cap changes it. The median library
size is 18. Each count is exactly `min.count = 10`, and each library size is
exactly the median, so the documented scaling factor is 1. Both samples
therefore satisfy the exact count threshold. The total count is 20, satisfying
the additional documented `min.total.count = 15` condition as well.

Nevertheless the actual returned value is `FALSE`. The two evaluation orders
put raw CPM one binary64 unit below the cutoff:

| Quantity | Binary64 bits | Exact value |
|---|---|---|
| Raw CPM, `(10 * 1000000) / 18` | `0x4120f4471c71c71c` | `4772185884444444 / 2^33` |
| Intermediate `10 / 18` | `0x3fe1c71c71c71c72` | `5003999585967218 / 2^53` |
| Cutoff, `(10 / 18) * 1000000` | `0x4120f4471c71c71d` | `4772185884444445 / 2^33` |

Thus zero samples pass the implemented `CPM >= CPM.Cutoff` comparison.
The tolerance used for the required sample number and total count does not
apply to this CPM comparison. `verification/filter.R` executes the original
R generic, default method, and CPM wrapper, and asserts `actual = FALSE`
versus the exact scaled-count condition `TRUE`.

This refutes R2's exact count-threshold equivalence. The documentation also
describes an operational `CPM >= CPM.cutoff` comparison: if that is interpreted
as comparing two independently rounded doubles, the implementation agrees
with that weaker interpretation on this witness. The discrepancy demonstrated
here is between that floating comparison and the exact scaled-count criterion;
it does not allege an incorrect comparison instruction.

## Exact WP statements and their scope

All statements below are in `verification/wp.c`. Let

```text
S(n,d,k) := d > 0 AND (2*k-1)*d < 2*n AND 2*n < (2*k+1)*d
a := 4772185884444444
b := 5003999585967218
t := 4772185884444445
C := 2^1023
T := 2^1024 - 2^970
```

`S` is the file's `strict_nearest` predicate: `k` lies strictly within half a
unit of `n/d`. There are no tie cases. ACSL integers are mathematical integers,
including products larger than a machine word. The file defines `C` and `T`
as decimal integer literals; `artifact.mjs` checks those literals against the
power-of-two definitions above using exact BigInt arithmetic.

The exact proved statements are:

* `nearest_unique_for_witness_grids`: for all mathematical integers `n,d,k,j`,
  if `(d = 18 OR d = 1048576) AND S(n,d,k) AND S(n,d,j)`, then `k = j`.
* `rounding_certificate`: on return,
  `2^52 <= a < 2^53`, `2^52 <= b < 2^53`, `2^52 <= t < 2^53`,
  `S(10000000*8589934592,18,a)`,
  `S(10*9007199254740992,18,b)`,
  `S(b*1000000,1048576,t)`, `t = a+1`,
  `10000000*8589934592 - a*18 = 8`,
  `8*19327352832 = 8589934592*18`, and
  `8*10737418240000000 = 10000000*8589934592`.
* `overflow_certificate`: on return, `C > 0`, `C*1000000 > T`, and
  `(C*1000000)/C = 1000000` (integer division, exact here).
* `filter_witness`: returns 0. Its body compares `a` and `t`, counts either
  two or zero passing samples, and applies the sample and total gates.
* `documented_witness`: returns 1. Its body applies `10 >= 10` in two samples
  and the total-count condition `20 >= 15`.

Every function contract also has `assigns \nothing` and no preconditions.
WP checks the lemma, all postconditions, termination, frame conditions, and
the generated applicable run-time obligations. The successful run reports
`36 / 36` goals proved, including the lemma. No user axioms, admitted goals,
or external unproved function contracts are used.

The binary64 interpretation of these integer certificates is part of the
reviewed model: normal numbers with exponent 19 have grid spacing `2^-33`,
and those with exponent -1 have spacing `2^-53`. Multiplying 10 by 1000000
is exact. Scaling the three exact operation results to those grids gives
the three ratios in `rounding_certificate`. Their certified significands
are representable and uniquely nearest; the test script also checks their
bit encodings. This is a mathematical certificate for specific operations,
not a Frama-C proof of a general IEEE-754 rounding implementation.
The two integer filter bodies model the Boolean decision for this witness;
execution of the original R code, including its actual tolerances, confirms
the decision without relying on that translation alone.

## Connection to the shipped software

The artifact is exactly `edgeR.so`, 96,558 bytes, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

`artifact.mjs` verifies this length and hash before loading the bytes directly
into Node's WebAssembly engine and calling the exported `calc_cpm_raw`.
It does not rebuild the source or replace the arithmetic. It creates valid
wasm32 `cmx` structures using the layout in `src/edgeR.h`: the count/output
buffer is column-major, and a type-2 compressed library-size row is repeated
over genes. The matrices have positive dimensions and `nthreads = 1`.

The host supplies linear memory, a table, imported i32 globals, zero-filled
allocation and deallocation. All other imported function calls throw.
The harness asserts that the only imported calls executed are two
`R_chk_calloc` calls and two `R_chk_free` calls, and that scratch allocations
are freed. Module instantiation executes its start function normally.
This host models the reachable allocation services, not a complete R host.

For independent inspection, `wasm-tools print edgeR.so` exposes
`calc_cpm_raw` as function 160 and `get_row` as function 207. Function 160
contains `f64.const 1000000`, `f64.mul`, then `f64.div`; the C source agrees
at `src/compute_cpm.c:142`. These observations are explanatory; the artifact
counterexamples depend on execution of the hashed bytes, not source-to-binary
equivalence or a trusted disassembly translation.

The R check sources `R/cpm.R` and `R/filterByExpr.R` unchanged. A narrow
`makeCompressedMatrix` adapter and `.Call` adapter route the exercised raw-CPM
path to that same artifact. The former validates and passes the library-size
row; the latter transfers round-trip decimal doubles to the Node harness,
then reconstructs the returned matrix. Thus the raw CPM arithmetic is
executed by the artifact, while the cutoff, group-size calculation, sample
comparison, total comparison, and final conjunction run in the supplied R
functions. Full R-Wasm integration and other entry paths are not proved.

`verification/inputs.sha256` records all original requirement, source, and
documentation hashes. The checker verifies them before running. Logs are
generated evidence and are never used as proof inputs.

## Reproduction

From this directory, run:

```sh
bash verification/check.sh
```

The exact component commands are:

```sh
sha256sum -c verification/inputs.sha256
frama-c --check-wp . verification/wp.c -wp -wp-rte -wp-prover alt-ergo -wp-timeout 10 -wp-cache none -wp-verbose 2
node verification/artifact.mjs
Rscript --vanilla verification/filter.R
```

Success requires exit status zero for every command, all input hashes `OK`,
WP's `Proved goals: 36 / 36`, `ARTIFACT COUNTEREXAMPLES PASS`, and
`R FILTER COUNTEREXAMPLE PASS`. The driver saves `verification/wp.log`,
`verification/artifact.log`, and `verification/filter.log`, and finishes with
`VERIFICATION CHECKS PASS (both requirements have counterexamples)`.
A successful check confirms the failures; it does not mean the requirements
hold. `--check-wp` rejects unproved goals, and `-wp-cache none` reruns proofs.

Frama-C emits two generic skipped-RTE warnings for alignment and indirect
function pointers. The proof file contains no pointer accesses or indirect
calls; those warnings do not omit an applicable obligation here.

Optional artifact inspection:

```sh
wasm-tools validate edgeR.so
wasm-tools print edgeR.so > /tmp/edgeR-inspect.wat
```

No network, Lean build, or installed edgeR package is needed. The checked
environment used Frama-C 33.0, Alt-Ergo 2.5.4, Node v26.11.1, and R 4.6.1.

## Review and trust inventory

Sizes below are lines and bytes (`wc -lc`), including comments. Review the
definitions and model interpretation above, the certificates, and both host
adapters. Tool correctness remains trusted: Frama-C/WP/Qed, Alt-Ergo, Node's
WebAssembly and JavaScript engines, R, BigInt arithmetic, SHA-256 tooling,
Bash, and the operating environment. There is no verified compiler or
verified R interpreter in this result.

| Review input | Lines | Bytes | Role |
|---|---:|---:|---|
| `verification/wp.c` | 72 | 3303 | Exact ACSL certificates and small decision models |
| `verification/artifact.mjs` | 129 | 5483 | Artifact hash, Wasm host, layout, bit checks, model-constant checks |
| `verification/filter.R` | 35 | 1729 | Original-R execution, restricted bridge, counterexample assertions |
| `verification/check.sh` | 8 | 479 | Fail-on-error reproduction commands |
| `verification/inputs.sha256` | 9 | 708 | Original-input identities |
| `R/cpm.R` | 114 | 3771 | Original CPM wrapper being executed |
| `R/filterByExpr.R` | 115 | 3745 | Original filtering code being executed |
| `README.md` | 13 | 1287 | Requirement statements |
| `CHECK.md` | 8 | 784 | Delivery requirements |
| `man/filterByExpr.Rd` | 161 | 7329 | Threshold, sample-size, and total-count documentation |
| `man/cpm.Rd` | 160 | 7280 | CPM interface documentation |
| `src/edgeR.h` | 381 | 14858 | Reviewed wasm32 structure-layout description |
| `src/compute_cpm.c` | 266 | 6996 | Explanatory source; not substituted for artifact execution |
| `edgeR.so` | binary | 96558 | Original software executed directly |

The existing Lean project was left unchanged. No correctness result depends
on an informal reimplementation being silently equated with the artifact.
