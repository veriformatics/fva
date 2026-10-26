# Verification result

Both requirements fail as universal, exact mathematical statements. The supplied
checks demonstrate the failures on the original Wasm and the shipped R functions.
Lean checks the exact arithmetic supporting the witnesses. This is a verification
by counterexample, not a universal correctness proof or a Lean formalization of
the Wasm/R runtimes. The original software and requirements have not been changed.

## R1: avoidable intermediate overflow

Input: one row, one column, count `c = 2^1020`, library size `L = 2^1020`,
one thread, output buffer initially containing the count as required by the
in-place C interface. Both inputs are finite positive binary64 values, with
`c <= L`. The input bit pattern is `0x7fb0000000000000`.

The original exported `calc_cpm_raw` returns positive infinity, bit pattern
`0x7ff0000000000000`. The exact result `c / L * 1000000` is `1000000`, itself
exactly representable as binary64 (`0x412e848000000000`). The reason is that the
artifact computes `fl(fl(c * 1000000) / L)`: its intermediate multiplication
overflows. This is not unavoidable rounding of the final mathematical result.
No finite absolute or relative rounding-error bound applies over the entire
input domain in R1; the error here is infinite in the extended-real convention.
R1 would need additional range restrictions or an explicitly weaker statement
about rounding each operation in this particular evaluation order.

Machine-checked execution result: `verification/wasm.cjs` asserts the artifact's
size and SHA-256, executes the exported function, and checks both output bits
and the representable reference result. It also checks a small two-row,
two-column case to exercise the column-major layout. Lean's `r1_inputs`,
`r1_exact`, `r1_intermediate_overflow`, and `r1_target_representable` certify the
exact arithmetic facts below. They do not assume the C source compiled correctly.

## R2: integer counts at the threshold are rejected

The main witness uses **all default arguments**:

```r
y <- matrix(c(10, 8, 10, 8), nrow=2)
#       sample1 sample2
# gene1      10      10
# gene2       8       8
filterByExpr(y)
```

Column sums and median library size are 18. There is one group of two samples,
so the required number is 2. Gene 1 reaches `min.count = 10` in both samples;
its total is 20, satisfying the documented `min.total.count = 15` condition.
At equal library sizes, the documented mathematical scaling cancels exactly.
Nevertheless, gene 1 is rejected:

| Quantity | Evaluation order | Actual binary64 value |
|---|---|---|
| Each CPM | `(10 * 1000000) / 18` | `1193046471111111 / 2^31` |
| Cutoff | `(10 / 18) * 1000000` | `4772185884444445 / 2^33` |

The two quantities have the same exact mathematical value, `5000000 / 9`.
Their computed values differ by `2^-33` (one ULP at this magnitude), with CPM
strictly below the cutoff. The number of qualifying samples becomes zero.
`r2_rounding_cells` certifies the strict nearest-rounding intervals of these
operations; the per-operation error in each certified cell is less than half
its stated spacing. `r2_integer_witness` certifies the threshold and total-count
facts and the exact one-ULP gap.

Two additional witnesses make the interpretation of R2 explicit:

* With `y = matrix(10,1,1)`, `lib.size = 1000000`, and `min.sample.size = 1`,
  the CPM expression condition holds exactly but the function returns `FALSE`
  because total count 10 is below 15. This refutes the README's expression-only
  “exactly when” literally. The total-count veto **is documented** in
  `man/filterByExpr.Rd`; this witness is a README omission, not a discrepancy
  between that part of the implementation and the manual.
* With `y = matrix(c(20,0),1,2)`, library sizes `[1000000,1000000]`,
  `min.sample.size = 1 + 2^-50`, and all other defaults, only one sample
  qualifies. Total count is 20. One is strictly less than the required
  `1.0000000000000009` samples, but the function returns `TRUE` because it
  subtracts `tol = 1e-14` from the required number. The rounded comparison
  threshold is `4503599627370455 / 2^52 < 1`.

These are failures of an **exact minimum-count/sample-count iff**. If R2 is
instead interpreted as precisely the implementation's floating-point CPM
comparison, extra total-count conjunct, and tolerance-adjusted sample comparison,
these cases are consistent with that weaker operational specification. No
universal proof of that different specification is claimed. The manual's
computed-CPM wording should be distinguished from the README's exact count rule.

`verification/filter.R` asserts each outcome while sourcing the shipped R files.
It uses the original Wasm for every CPM in these checks. `r2_total_veto`,
`r2_sample_gap`, and `r2_cpms` provide the additional exact-arithmetic certificates.

## Exact Lean statements

All declarations below are in namespace `Verification` in
`Proofs/Counterexamples.lean`, imported by `Proofs.lean`. Every theorem is proved
with `norm_num`; there are no `sorry`s, added axioms, `native_decide` calls, or
floating-point evaluation oracles. The statements and their definitions are:

```lean
def count : ℚ := 2 ^ 1020
def maxFinite : ℚ := (2 - 1 / 2^52) * 2^1023
def overflowMidpoint : ℚ := 2^1024 - 2^970

theorem r1_inputs : 0 < count ∧ count ≤ maxFinite
theorem r1_exact : count / count * 1000000 = 1000000
theorem r1_intermediate_overflow :
    overflowMidpoint < count * 1000000
theorem r1_target_representable :
    (1000000 : ℚ) = 8589934592000000 / 2^33 ∧
    2^52 ≤ (8589934592000000 : ℕ) ∧
    (8589934592000000 : ℕ) < 2^53

def actualCPM : ℚ := 1193046471111111 / 2^31
def divisionResult : ℚ := 2501999792983609 / 2^52
def actualCutoff : ℚ := 4772185884444445 / 2^33
def inRoundingCell (exact rounded spacing : ℚ) : Prop :=
  rounded - spacing/2 < exact ∧ exact < rounded + spacing/2

theorem r2_rounding_cells :
    inRoundingCell (10*1000000/18) actualCPM (1/2^33) ∧
    inRoundingCell (10/18) divisionResult (1/2^53) ∧
    inRoundingCell (divisionResult*1000000) actualCutoff (1/2^33)
theorem r2_integer_witness :
    (10 : ℚ) / 18 * 1000000 = 5000000/9 ∧
    (10 : ℚ) ≥ 10 ∧ (10+10 : ℚ) ≥ 15 ∧
    actualCPM < actualCutoff ∧
    actualCutoff - actualCPM = 1/2^33
theorem r2_total_veto :
    (10 : ℚ) / 1000000 * 1000000 = 10 ∧
    (1 : ℚ) ≥ 1 ∧ ¬ ((10 : ℚ) ≥ 15 - 1/10^14)

def required : ℚ := 1 + 1 / 2^50
def tolerance : ℚ := 6338253001141147 / 2^99
def roundedThreshold : ℚ := 4503599627370455 / 2^52

theorem r2_sample_gap :
    (1 : ℚ) < required ∧
    required - tolerance < 1 ∧
    roundedThreshold ≤ 1 ∧
    (20 : ℚ) ≥ 15
theorem r2_cpms :
    (20 : ℚ) * 1000000 / 1000000 = 20 ∧
    (0 : ℚ) * 1000000 / 1000000 = 0 ∧
    (10 : ℚ) / 1000000 * 1000000 = 10 ∧
    (20 : ℚ) ≥ 10 ∧ ¬ ((0 : ℚ) ≥ 10)
```

`r1_target_representable` supplies the significand arithmetic for the normal
binary64 representation with exponent -33. The interpretation of those numbers
as binary64 fields and of `overflowMidpoint` as the nearest-rounding overflow
threshold is ordinary IEEE-754 reasoning outside Lean. Execution independently
checks the actual R1 input/output bits. Similarly, `inRoundingCell` is an exact
rational interval predicate, not an axiomatized IEEE implementation.

## Connection to the shipped bytes

The executed artifact is exactly the unmodified `edgeR.so`, 96,558 bytes, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

`verification/inputs.sha256` also pins the R files, C source/header, README,
manuals, and CHECK.md. `wasm-tools validate` checks that the module is valid.
Node's WebAssembly engine instantiates the **whole original module** and calls
its exported `calc_cpm_raw`; it neither recompiles C nor extracts/replaces the
arithmetic. For inspection, `wasm-tools print edgeR.so` shows export
`calc_cpm_raw` pointing to function 160, whose inner computation contains
`f64.load`, `f64.const 1000000`, `f64.mul`, another `f64.load`, `f64.div`,
and `f64.store`. `get_row` is function 207 and also runs from the artifact.

The host harness supplies zeroed linear memory, a table, globals, and checked
zero-initializing allocation/free. It constructs full, double, column-major
`cmx` structs using the 32-byte Wasm32 layout described by `src/edgeR.h`.
Library vectors are expanded to full matrices of identical per-column values.
The output starts as a copy of counts, matching the in-place raw C contract.
Only `R_chk_calloc` and `R_chk_free` may be called from the host; every other
function import throws if reached. Scratch allocations must be freed. Dummy
globals are sufficient on this path, which does not use R objects, BLAS, LAPACK,
or constructors/relocations. This is a direct C-export call, not a full R/Wasm
dynamic-loader or SEXP-wrapper verification.

The complete edgeR R package is not installed in the native R runtime. The R
harness sources `R/cpm.R` and `R/filterByExpr.R` without editing their bodies.
It supplies `makeCompressedMatrix` as a checked logical library-vector carrier
and intercepts `.Call(.cxx_calculate_cpm_raw, ...)` to serialize counts/library
sizes to the Node harness and return the actual Wasm output as an R matrix.
There is no replacement `cpm` or `filterByExpr` implementation. R performs the
original S3 dispatch, default arguments, column sums, median, threshold,
comparisons, row sums, tolerance, and final conjunction. The serialization and
dependency bridge are trusted; the missing package's native `.Call` wrapper
itself is not verified. These limitations do not turn the arithmetic into a
source-only model: the Wasm inner computation is executed on every witness.

## Reproduction

From this directory, offline, run:

```sh
bash verification/check.sh
```

That script runs these exact commands in order:

```sh
sha256sum -c verification/inputs.sha256
wasm-tools validate edgeR.so
lake build
lake env lean Proofs/Counterexamples.lean
node verification/wasm.cjs
Rscript --vanilla verification/filter.R
```

Success means exit status zero, all hash lines `OK`, a successful Lake build,
and the final line `PASS: all proofs and counterexample checks completed`.
The Lean source is checked directly as well as through Lake. The nine
`#print axioms` results must contain only `[propext, Classical.choice,
Quot.sound]`; in particular, there is no `sorryAx`. Lines beginning `R1 FAIL`
or `R2 FAIL` describe **requirements failing**, and are expected. All four
counterexample assertion groups must pass. R may print the expected message
that all samples are assumed to belong to one group.

The checks were run successfully with Lean 4.35.0, Mathlib v4.35.0, Node
v26.11.1, R 4.6.1, and wasm-tools 1.262.0. The project uses the prebuilt local
Mathlib dependencies specified in `lakefile.toml` and `lake-manifest.json`;
no network, downloaded packages, or `lake update` are required. Wasmtime is
not needed by these checks; Node executes Wasm and transports the R matrix.

## Review and trust inventory

Review the definitions and proof statements as well as the executable harnesses.
The Lean results concern exact rational arithmetic; identifying the program
outputs with those rational values is checked by executable assertions, not by
a Lean proof of an interpreter. The trusted runtime/toolchain consists of the
Lean kernel and standard axioms listed above, the prebuilt Mathlib environment,
Node/V8's Wasm binary64 execution, R's numeric and language semantics, Node's
standard library/assertions, SHA-256 and the hashing/validation tools, and the
OS/file I/O. Mathlib tactics generate proof terms checked by Lean; they are not
extra theorem axioms. Hardware, runtime, and dependency binaries are external
toolchain dependencies, not small auditable proof files.

The following table gives line counts and byte sizes of the local material to
review. C files help review the ABI and intended operation order; runtime
counterexamples are bound to the artifact hash rather than to a compiler
correctness assumption. Full R source bodies must be reviewed for the bridge's
scope. Manuals and README determine what the requirements mean.

| File | Lines | Bytes |
|---|---:|---:|
| `Proofs/Counterexamples.lean` | 95 | 3758 |
| `Proofs.lean` | 1 | 30 |
| `verification/wasm.cjs` | 89 | 3925 |
| `verification/filter.R` | 59 | 3125 |
| `verification/check.sh` | 9 | 277 |
| `verification/inputs.sha256` | 9 | 708 |
| `README.md` | 13 | 1287 |
| `CHECK.md` | 8 | 784 |
| `R/cpm.R` | 114 | 3771 |
| `R/filterByExpr.R` | 115 | 3745 |
| `src/edgeR.h` | 381 | 14858 |
| `src/compute_cpm.c` | 266 | 6996 |
| `man/cpm.Rd` | 160 | 7280 |
| `man/filterByExpr.Rd` | 161 | 7329 |
| `lakefile.toml` | 12 | 264 |
| `lake-manifest.json` | 117 | 3536 |
| `lean-toolchain` | 1 | 25 |
| `VERIFICATION.md` | 265 | 12886 |
