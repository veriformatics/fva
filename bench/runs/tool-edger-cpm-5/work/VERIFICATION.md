# Verification results

Both README requirements have counterexamples. The shipped code and binary were
left unchanged. Frama-C 33.0/WP proves the arithmetic and decision facts below;
execution of the original WebAssembly and R code connects these facts to the
shipped software. This is a refutation by concrete inputs, not a universal
correctness proof.

## R1: fails on finite, positive inputs

Use a one-element count matrix with `c = 2^1020`, a library size
`L = 2^1020`, and `nthreads = 1`. Both inputs are finite binary64 values, and
`c <= L`. The exact requested result is

```
c / L * 1000000 = 1000000.
```

This result is exactly representable, so correctly rounding it has zero error.
The original `edgeR.so` export `calc_cpm_raw` instead returns positive infinity.
It evaluates `c * 1000000` first, which overflows, and then divides by `L`.
Thus its absolute and relative errors on this input are infinite; no finite
absolute or relative rounding-error bound holds over all the inputs allowed by
R1. This is intermediate overflow with a finite final mathematical result.

`verification/artifact.cjs` checks the binary's hash and size, instantiates those
original bytes, invokes that export, and asserts the infinity result. It also
checks that division followed by multiplication returns exactly `1000000`.
No modified or rebuilt binary is used.

The supplementary WP result `overflow_witness_real_arithmetic`, in
`verification/counterexamples.c`, has no preconditions and proves exactly:

```
witness > 0
witness / witness * 1000000 == 1000000
witness * 1000000 > largest_double * 2
```

Here the ACSL definitions are exact real constants:
`witness = 2^1020` and
`largest_double = (2^53 - 1) * 2^971`, written out in decimal in the file.
The last inequality puts the intermediate result well beyond the binary64
overflow threshold. The WP result concerns real arithmetic; the infinity
returned by WebAssembly is established by the execution assertion, not by a
claim that WP proved floating-point overflow.

## R2: fails at the minimum count boundary

Run the default method with every tuning argument at its default:

```r
y <- matrix(c(10, 8, 10, 8), nrow=2)
#        sample 1  sample 2
# gene 1       10        10
# gene 2        8         8
filterByExpr(y)
```

The column sums and their median are all `18`. There is one group of two
samples, so the required number of samples is `2`; neither the large-group
adjustment nor the maximum-sample cap changes it. Gene 1 reaches `min.count=10`
in both samples and has total count `20 >= min.total.count=15`. The documented
scaling preserves equality: its exact CPM and the exact cutoff are both
`5000000/9`. Hence the README's exact count criterion requires retaining gene 1.

Actual result: `c(FALSE, FALSE)`. The count-based result, including the documented
total-count requirement, is `c(TRUE, FALSE)`. Gene 1 is incorrectly rejected
under R2's exact count equivalence because the two floating-point expressions
have different operation orders:

| Quantity | Evaluation order | Exact binary64 value |
| --- | --- | --- |
| Actual CPM | `(10 * 1000000) / 18` | `1193046471111111 / 2147483648` |
| R cutoff | `(10 / 18) * 1000000` | `4772185884444445 / 8589934592` |

The cutoff exceeds the actual CPM by exactly `1/8589934592`, one binary64 step
at this magnitude. Their decimal displays are `555555.5555555555` and
`555555.5555555556`. Consequently zero samples pass the CPM comparison. The
`1e-14` tolerance is applied to the number of passing samples, not to their CPM
values, so it does not prevent this rejection. The total-count test passes.

This refutes the README's **exact count-threshold equivalence**. The code does
apply the floating CPM comparison printed in the manual. If that comparison
itself is taken as the entire specification, allowing its rounding to change
count-boundary decisions, this example agrees with that weaker specification.
It does not satisfy the exact count statement in R2.

The following precondition-free WP results are in
`verification/counterexamples.c`. All functions also have `assigns \nothing`
contracts. The exact functional postconditions are:

- `shipped_cpm_at_boundary()` returns a finite double equal to
  `(double)555555.5555555555` and to the exact real
  `1193046471111111.0 / 2147483648.0`. Its signed error relative to the exact CPM
  is exactly `-1.0 / 19327352832.0`.
- `documented_cutoff_at_boundary()` returns a finite double equal to
  `(double)555555.5555555556` and to the exact real
  `4772185884444445.0 / 8589934592.0`.
- `rejects_boundary_gene()` returns `0`. Its body evaluates both floating
  expressions, counts the two comparisons, and applies the sample-count and
  total-count predicates including their tolerances.
- `ideal_boundary_gene_meets_threshold()` proves the exact real identity
  `10.0 / 18.0 * 1000000.0 == 5000000.0 / 9.0` and the conjunction
  `10 >= 10 && 2 >= 2 && 20 >= 15`.

ACSL arithmetic in postconditions is mathematical real arithmetic unless an
explicit double cast is present; executable C arithmetic uses WP's binary64
model. In particular the exact real identities do not assert that floating
operations are associative.

## Connection to the shipped artifact and R code

The target binary is exactly 96,558 bytes, SHA-256:

```
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

`verification/inputs.sha256` identifies all original inputs used here and the
proof/harness files. The replay checks these hashes first.

`verification/artifact.cjs` executes the original binary through Node's
WebAssembly implementation. It provides linear memory, an indirect table,
loader globals, a zeroing allocator, and a checked free operation. Every other
imported function throws if called. Only allocation/free imports are reached
by these fixtures. The harness constructs valid wasm32 `cmx` objects using the
layout in `src/edgeR.h`: double data pointer, integer data pointer, dimensions,
compression type, integer flag, physical stride, and row-selection pointer.
The library objects use a repeated row (`type=2`); counts initialize the
caller-owned output buffer as required by `calc_cpm_raw`. The actual `get_row`
and kernel implementations execute inside the original module.

For the R2 matrix the harness writes all four measured CPM values to
`verification/cpm.csv`. It checks their values before writing them. Then
`verification/filter.R` sources the unchanged `R/filterByExpr.R` and `R/cpm.R`
and calls `filterByExpr(y)` with the matrix above. This checkout does not contain
a complete native edgeR installation, and native R cannot load this WebAssembly
shared object. The R harness therefore provides a fixture-specific bridge:
`makeCompressedMatrix` validates the dimensions/library sizes, and a local
`.Call` validates the symbol, counts, library sizes, and thread argument, then
returns the CPM matrix just measured from the real binary. No other R filtering
logic is replaced. CSV serialization round-trips these doubles. Assertions
check the actual result, the exact count criterion, and the failure of their
equivalence.

The C file is a small, manually transcribed scalar model of the arithmetic in
`src/compute_cpm.c:142` and the predicates in `R/filterByExpr.R:105-114`.
It is not a translation or a formal semantics of the full WebAssembly or R
program. The connection of that model to those expressions requires inspection;
the artifact/R assertions independently demonstrate both failures on the
stated fixtures. No source-to-binary equivalence theorem, general memory-safety
result, full R interpreter proof, or other-input correctness claim is made.

For optional binary inspection, run `wasm-tools print edgeR.so`. The
`calc_cpm_raw` export refers to function 160, which uses `f64.mul` with
`1000000` followed by `f64.div`, and calls the original row extractor,
function 207. The binary's `clamp_threads` returns 1.

## Replay

From this directory, with the installed offline tools:

```sh
bash verification/run.sh
```

The script runs exactly:

```sh
sha256sum -c verification/inputs.sha256
wasm-tools validate edgeR.so
frama-c --check-wp . verification/counterexamples.c \
  -wp -wp-model Typed+float -wp-prover alt-ergo -wp-timeout 10 \
  -wp-rte -wp-cache none
node verification/artifact.cjs
Rscript verification/filter.R
```

It saves the last three outputs to `verification/wp.log`,
`verification/artifact.log`, and `verification/filter.log`, regenerating the CSV
between the WP check and the R check. It needs no network, package installation,
Lean proof, or rebuilding of `edgeR.so`.

Success means exit status zero, all hashes `OK`, silent successful Wasm
validation, WP `Proved goals: 42 / 42`, `Artifact checks passed`,
`Shipped R checks passed`, and the final message
`All verification checks passed (both requirements have counterexamples).`
There must be no unproved WP goals. The `--check-wp` wrapper and shell
`pipefail` enforce failure propagation. These checks succeeding means the
counterexamples and supporting proofs succeeded, not that R1 or R2 hold.

Observed tools: Frama-C 33.0, Alt-Ergo 2.5.4, Node v26.11.1,
R 4.6.1, wasm-tools 1.262.0. WP reports the inexact representation of `1e-14`
and skipped alignment/function-pointer guards. The former is the actual
binary64 literal used in the predicates; the scalar model contains no pointers
or indirect calls to which the latter guards could apply. R's informational
message about assuming a single group is expected.

## Review and trust

The reviewer must inspect the following files. Sizes are lines / bytes;
the manifest contains SHA-256 hashes. Logs and the CSV are reproducible outputs,
not additional proof assumptions.

| File | Size | Role |
| --- | ---: | --- |
| `README.md` | 13 / 1287 | Requirements and binary identity |
| `CHECK.md` | 8 / 784 | Delivery instructions |
| `verification/counterexamples.c` | 54 / 2222 | Scalar models, exact constants, ACSL contracts |
| `verification/artifact.cjs` | 64 / 2913 | Original-binary execution, loader fixtures, assertions, CSV writer |
| `verification/filter.R` | 34 / 1561 | Unchanged R source execution, fixture bridge, assertions |
| `verification/run.sh` | 11 / 573 | Replay and failure propagation |
| `verification/inputs.sha256` | 13 / 1071 | Input identity manifest |
| `src/compute_cpm.c` | 266 / 6996 | Original kernel source; raw CPM function is the relevant part |
| `src/edgeR.h` | 381 / 14858 | Original `cmx` layout and declarations |
| `R/cpm.R` | 114 / 3771 | Original R-to-kernel path |
| `R/filterByExpr.R` | 115 / 3745 | Original sample-size, cutoff and filtering logic |
| `man/filterByExpr.Rd` | 161 / 7329 | Documented count/sample/total criteria |
| `man/cpm.Rd` | 160 / 7280 | CPM documentation |
| `edgeR.so` | 96558 bytes | Executed binary, not assumed equivalent to source |

The added proof and execution code is 163 lines / 7269 bytes, excluding the
manifest and this report. Trust also includes the Frama-C parser/WP/Qed,
its IEEE floating-point model and constant evaluation, Alt-Ergo, the tool
wrapper's all-goals check, Node's WebAssembly engine, the R interpreter and base
numeric operations, decimal serialization/parsing, hashing tools, and the local
execution environment. There are no user axioms, assumed function contracts,
`admit`/`sorry`, or external theorem libraries in these proofs. There is no
independent Lean kernel check of WP/Alt-Ergo results.
