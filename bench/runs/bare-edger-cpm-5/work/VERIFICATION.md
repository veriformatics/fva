# Verification result

Both README requirements, read as universal claims about the stated count
formula and an exact minimum-count decision, have counterexamples. The shipped
software has not been modified. These are executable counterexamples with Lean
certificates for their exact arithmetic, not a universal verification of R or
WebAssembly semantics.

## R1: counterexample to universal numerical accuracy

Use one row and one column, double count `c = 2^1020`, double library size
`L = 2^1020`, an output buffer initially containing `c`, and `nthreads = 1`.
Both inputs are finite, exactly representable, nonnegative, and `0 < L`, with
`c <= L`. The shipped `calc_cpm_raw` returns **positive infinity**. The required
real result is exactly `1000000`; binary64 evaluation of `(c/L)*1000000` also
returns exactly `1000000`.

The binary evaluates `(c*1000000)/L`. Its first multiplication overflows.
`verification/check.py` checks the actual exported function's result using
Wasmtime `assert_return`, and separately checks the division-first reference.
`r1_positive_input`, `r1_ideal`, and
`r1_intermediate_exceeds_overflow_midpoint` certify positivity, the exact answer,
and crossing the round-to-nearest overflow midpoint, respectively.

**Rounding error:** on this input the artifact has infinite absolute and relative
error against the finite exact result. Consequently no finite uniform accuracy
bound of the stated kind holds over all the inputs in R1. No universal finite
rounding bound is claimed. For the ordinary finite R2 witness below,
`r2_rounding_cells` additionally certifies an absolute error strictly less than
`2^-50` for the artifact's CPM, and strict half-ulp bounds for each cutoff
operation. The failure of R1 does not imply incorrect hardware rounding of its
individual instructions: they correctly implement the overflow-prone operation
order. If "as double-precision arithmetic allows" is intended to permit such
intermediate overflow, the concrete operational result is established, but that
interpretation supplies no finite accuracy guarantee for R1's domain.

## R2: counterexamples

### Boundary failure, including the documented total-count condition

Run the shipped R default method through its generic:

```r
y <- matrix(c(10, 10), nrow=1)
filterByExpr(y, lib.size=c(1000009, 1000009), min.sample.size=2)
# FALSE
```

Other arguments have their shipped defaults: `min.count=10`,
`min.total.count=15`, `large.n=10`, `min.prop=0.7`, `max.n.samples=40`,
`preset=NULL`. The required sample size remains 2. The median library size is
1000009. In both samples the scaled minimum count is exactly
`10 * L / median(L) = 10`, and each count reaches it. The total count is
20, exceeding 15. Thus the exact minimum-count criterion, even with the total
condition added, says to keep the gene.

The executable checks establish:

| Quantity | Binary64 value | Exact value |
|---|---|---|
| Each artifact CPM | `0x1.3fff43420d831p+3` | `5629448869173297 / 562949953421312` |
| R cutoff | `0x1.3fff43420d832p+3` | `2814724434586649 / 281474976710656` |

The CPM is approximately `9.9999100008099919`; the cutoff is approximately
`9.9999100008099937`. The difference is exactly one ulp, `2^-49`.
Neither CPM reaches the cutoff. The `1e-14` tolerance in
`R/filterByExpr.R:109` applies to the number of passing samples, after the CPM
comparisons; it does not repair either comparison. The actual output is `FALSE`.

`r2_encodings`, `r2_rounding_cells`, and `r2_one_ulp_gap` certify the finite
encodings, midpoint inequalities, and exact gap. `r2_boundary_counterexample`
certifies the mismatch in the concrete rational model of the final predicates.
R execution separately checks the actual binary64 decisions and output.

### Literal README iff omits the total-count gate

With `y=matrix(10,1,1)`, `lib.size=1000000`, and `min.sample.size=1`, the
minimum-count/sample criterion passes exactly, but the function returns `FALSE`
because the total count 10 is below default `min.total.count=15`.
`r2_literal_iff_counterexample` and the execution checks establish this second
failure of the README's literal iff. This extra gate is expressly documented
in `man/filterByExpr.Rd`.

**Interpretation:** the boundary example refutes equivalence to the exact scaled
minimum-count criterion. It does not refute the documentation if that is instead
read as the operational predicate "compare the already-rounded CPM values with
the separately-rounded cutoff, and also test total count." The source implements
that latter predicate on these inputs. The literal README criterion and that
operational predicate are different specifications.

## Connection to shipped bytes and execution scope

The checker pins these SHA-256 hashes before running:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb  edgeR.so
b43ab97191a448ef8d141decdef802be3329801692a9c9a0618cf5ef874eb39b  R/cpm.R
abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f  R/filterByExpr.R
```

`edgeR.so` is 96,558 bytes, matching README. The Python checker validates it,
reads its import declarations using `wasm-tools print`, and embeds **all original
bytes** in a WAST binary module. It does not recompile the C source or substitute
a mathematical implementation of the kernel. A separate wrapper constructs valid
32-byte wasm32 `cmx` structs for full double matrices, initializes both the count
matrix and a separate output copy, then calls the exported `calc_cpm_raw`.
The two-column test checks both output cells. This exercises the artifact's own
row extraction and loops.

The import environment provides shared memory, table, relocation globals, and a
zeroing bump allocator for `R_chk_calloc`. `R_chk_free` is a no-op: freed memory
is never reused in these short tests. All other function imports trap if called.
Stack, relocated data, test buffers, and heap occupy disjoint regions. The
artifact's original start function runs normally. This is a concrete valid
kernel call environment, not an emulation of a complete R installation.

The edgeR R package and several of its helpers are absent. `verification/check.R`
sources both shipped R files unchanged. It supplies a concrete
`makeCompressedMatrix` helper and an R-level `.Call` adapter. The adapter accepts
only the two matrices above, verifies its symbol, dimensions, counts, library
sizes, and thread argument, and returns values whose exact bits the preceding
Wasm assertions checked. The boundary matrix is transferred as little-endian
binary64 bytes. The one-cell value 10 is also independently asserted against the
Wasm export. The S3 dispatch, `cpm.default` checks, median, cutoff arithmetic,
sample adjustment, comparisons, sums, and final conjunction execute in R from
the shipped files.

This bridge is explicitly part of the trusted connection for R2. There is no
claim that the absent package's SEXP wrapper or general compression helper was
verified. The test does not execute a full R/Wasm package installation. The
Lean module is an exact rational certificate for the named witnesses; it is not
a formalization of the source interpreter, allocator, or compiler. In particular,
its tolerance is the rational `1/10^14`; actual R tolerance rounding and decisions
are checked by R separately. No universal correctness, memory-safety, other
matrix shapes, threading configurations, or other package functions are claimed.

## Reproduce every result

From this directory, with the installed offline toolchain and Mathlib:

```sh
lake build
lake env lean verification/Audit.lean
python3 verification/check.py
```

All commands must exit zero. The first prints `Build completed successfully`
(or successful cached build output). The audit prints all eight theorem names,
each depending only on `[propext, Classical.choice, Quot.sound]`; it must not list
`sorryAx` or any additional axiom. The execution checker ends with:

```text
R1: shipped calc_cpm_raw(2^1020, 2^1020) = +inf; reference = 1000000
Wasm: both boundary CPM entries = 0x1.3fff43420d831p+3
R2 boundary: CPM=9.9999100008099919 < cutoff=9.9999100008099937; documented=TRUE; actual=FALSE; total=20 >= 15
R2 literal iff: one count 10, L=1000000, required samples=1: CPM passes, total fails, keep=FALSE
PASS: all artifact, floating-point, and R counterexample assertions
```

The checker creates and deletes temporary WAST and binary exchange files. No
network, external R packages, Python packages, or changes to the artifact are
needed. Verified with Lean/Mathlib 4.35.0, Wasmtime 50.0.0, wasm-tools 1.262.0,
R 4.6.1, and Python 3.14.8.

## What must be reviewed and trusted

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs/Counterexamples.lean` | 78 | 3218 | Definitions, all exact theorem statements and kernel-checked arithmetic proofs |
| `Proofs.lean` | 1 | 30 | Library import |
| `verification/Audit.lean` | 10 | 459 | Prints proof axiom dependencies |
| `verification/check.py` | 107 | 5991 | Artifact hashes, generated Wasm environment and wrapper, assertions, R invocation |
| `verification/check.R` | 52 | 2458 | Restricted bridge and assertions while executing shipped R code |
| `R/cpm.R` | 114 | 3771 | Shipped R dispatch and CPM path |
| `R/filterByExpr.R` | 115 | 3745 | Shipped filtering code |
| `src/edgeR.h` | 381 | 14858 | ABI layout used by wrapper; it can also be checked against actual load offsets |
| `src/compute_cpm.c` | 266 | 6996 | Source correspondence for explanation; not substituted for binary execution |
| `man/filterByExpr.Rd` | 161 | 7329 | Interpretation of scaling, sample requirement, and total-count gate |
| `README.md` | 13 | 1287 | Requirements being assessed |
| `lakefile.toml` | 12 | 264 | Build target and Mathlib dependency |
| `lean-toolchain` | 1 | 25 | Lean version |
| `lake-manifest.json` | 117 | 3536 | Offline dependency resolution |

Also trust the Lean kernel and its standard logical axioms, Mathlib rational
definitions, the Lake import/build configuration, R's interpreter and binary64
behavior, Wasmtime's WAST assertions and Wasm execution, wasm-tools' validation
and import printing, Python's standard library and SHA-256, and the host/toolchain.
Tactics construct proof terms checked by Lean; no `sorry`, custom axioms, or
`native_decide` are used. The execution portions are machine-checked demonstrations
using those runtimes, not kernel proofs of their implementations. The entire
96,558-byte artifact is loaded unchanged; only the named paths execute.

## Exact Lean theorem statements

All statements below are in namespace `EdgeRVerification` in
`Proofs/Counterexamples.lean`. Their definitions are in that same file and are
part of the review surface listed above. The first three support R1; the
remaining five support R2 and the stated local rounding bounds.

```lean
theorem r1_positive_input : (0 : ℚ) < 2^1020

theorem r1_ideal : idealCPM (2^1020) (2^1020) = 1000000

theorem r1_intermediate_exceeds_overflow_midpoint :
    (2 : ℚ)^1024 - (2 : ℚ)^970 < (2 : ℚ)^1020 * 1000000

theorem r2_encodings :
    positiveNormalValue 0x4023fff43420d831 = actualCPM ∧
    positiveNormalValue 0x4023fff43420d832 = cutoffCPM ∧
    positiveNormalValue 0x3ee4f8a92a52c5d4 = cutoffDivision ∧
    0x4023fff43420d831 / 2^63 = 0 ∧
    0x4023fff43420d831 / 2^52 % 2048 = 1026 ∧
    0x4023fff43420d832 / 2^63 = 0 ∧
    0x4023fff43420d832 / 2^52 % 2048 = 1026 ∧
    0x3ee4f8a92a52c5d4 / 2^63 = 0 ∧
    0x3ee4f8a92a52c5d4 / 2^52 % 2048 = 1006

theorem r2_rounding_cells :
    insideRoundingCell ((10 : ℚ) * 1000000 / 1000009) actualCPM ulpAtTen ∧
    insideRoundingCell ((10 : ℚ) / 1000009) cutoffDivision (1 / 2^69) ∧
    insideRoundingCell (cutoffDivision * 1000000) cutoffCPM ulpAtTen

theorem r2_one_ulp_gap : cutoffCPM - actualCPM = ulpAtTen

theorem r2_boundary_counterexample : boundaryDocumented ∧ ¬ boundaryKeep

theorem r2_literal_iff_counterexample :
    (10 : ℚ) ≥ 10 ∧ (1 : ℚ) ≥ 1 - 1/10^14 ∧
    ¬ ((10 : ℚ) ≥ 15 - 1/10^14)
```
