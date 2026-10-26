# Verification results

Both requirements fail on their stated domains. The supplied software was not
modified. There are executable counterexamples against the original `edgeR.so`
and the supplied R functions, plus Lean proofs of the counterexamples' binary64
and rational arithmetic. These are refutations, not universal correctness proofs.

## R1: intermediate overflow

Use a one-row, one-column matrix with count and library size both equal to the
finite binary64 number `0x1p+1023` (exactly `2^1023`). The count is nonnegative,
the library size is positive, and the count equals the column's library size.

The specified exact result is

```
(2^1023 / 2^1023) * 1000000 = 1000000.
```

That result is exactly representable in binary64. Executing the exported
`calc_cpm_raw` in the shipped binary instead returns positive infinity, bits
`0x7ff0000000000000`. Its arithmetic sequence is `f64.mul` by one million,
followed by `f64.div` by the library size. The intermediate multiplication
overflows. Division first gives exactly one million, including in the logical
binary64 model.

Thus no finite absolute or relative rounding-error bound for the requested CPM
holds over the full stated domain. The error at this witness is unbounded
(positive infinity versus a finite result). A specification that explicitly
permits intermediate overflow would need a different conclusion; the checks
here establish the actual operation order and its consequence. No universal
error bound under additional range restrictions is claimed.

Evidence: `Verification/check.py` checks the artifact output bits;
`large_value`, `large_positive`, `r1_exact`, and `r1_overflow` in
`Proofs/Counterexamples.lean` prove the corresponding arithmetic statements.

## R2: cutoff boundaries

There are two independent counterexamples. Both satisfy the documented default
total-count condition, so the extra `min.total.count` filter is not the cause.

### Ordinary integer counts at the minimum

Run the supplied functions on the following matrix, with one group containing
both samples, no explicit library sizes, and all tuning arguments at defaults:

```r
y <- matrix(c(10, 26, 10, 26), nrow=2, ncol=2)
filterByExpr(y, group=c("a", "a"))
# FALSE TRUE
```

Each column sums to 36. The first gene has exactly `min.count = 10` in both
required samples, and total count 20 exceeds 15. With equal library sizes,
the documented scaling leaves that exact count boundary unchanged.
Nevertheless its computed CPM falls below the computed cutoff:

| Quantity | Exact value of the binary64 result | Hexadecimal floating value |
| --- | --- | --- |
| Artifact CPM, `(10 * 1000000) / 36` | `1193046471111111 / 4294967296` | `0x1.0f4471c71c71cp+18` |
| R cutoff, `(10 / 36) * 1000000` | `4772185884444445 / 17179869184` | `0x1.0f4471c71c71dp+18` |

The cutoff is one ULP above the CPM. Relative to the exact rational CPM
`2500000/9`, the signed errors are respectively `-1/38654705664` and
`5/154618822656`. These errors are proved exactly, not estimated using decimal
printing. The test demonstrates failure of README R2's exact count-boundary
interpretation. If the documentation's CPM comparison is interpreted strictly
as a comparison of these already rounded computations, it predicts rejection
for this example; the next example violates that comparison's stated sample
requirement as well.

### Sample-count tolerance versus the documented CPM rule

```r
y <- matrix(c(20, 0), nrow=1, ncol=2)
filterByExpr(y, lib.size=c(1e6, 1e6), min.sample.size=1 + 2^-50)
# TRUE
```

Explicit positive library sizes are supported by the interface. Here CPM is
exactly `(20, 0)`, the cutoff is exactly 10, and exactly one sample qualifies.
The documented required sample size is the exactly representable number
`1 + 2^-50`, strictly greater than one. It is below `large.n` and
`max.n.samples`, so neither adjustment changes it. The documented comparison
`1 >= 1 + 2^-50` is false, while the implementation subtracts `1e-14` from the
sample requirement and returns true. Total count is 20. This refutes the exact
documented rule even when CPM and cutoff arithmetic are exact.

Evidence: `Verification/check_filter.R` executes both supplied R files and
asserts these results. `r2_boundary_bits`, `r2_boundary_errors`,
`r2_count_boundary`, `r2_sample_tolerance`, and
`r2_required_strictly_above_one` prove the arithmetic in
`Proofs/Counterexamples.lean`.

## Exact Lean statements and definitions

All theorems below are in namespace `Counterexamples` in
`Proofs/Counterexamples.lean`. These are their exact source statements (proof
bodies omitted). Definitions are:

```lean
abbrev F := Float.Model
def value (f : F) : Option ℚ :=
  match f.unpack with
  | .finite s m e _ => some ((s.apply (Int.ofNat m) : ℚ) * (2 : ℚ) ^ e)
  | .zero _ => some 0
  | _ => none
def million : F := Float.Model.ofNat 1000000
def large : F := Float.Model.ofBits 0x7fe0000000000000
def raw (c L : F) : F := (c * million) / L
def cutoff (c L : F) : F := (c / L) * million
def ten : F := Float.Model.ofNat 10
def thirtySix : F := Float.Model.ofNat 36
def boundaryCPM : ℚ := 1193046471111111 / 4294967296
def boundaryCutoff : ℚ := 4772185884444445 / 17179869184
def required : F := Float.Model.ofNat 1 + Float.Model.ofBits 0x3cd0000000000000
def tolerance : F := Float.Model.ofBits 0x3d06849b86a12b9b
```

`Float.Model` is Lean 4.35's logical binary64 model with round-to-nearest,
ties-to-even arithmetic. `value` decodes finite values to exact rationals;
`none` means infinity or NaN. The explicit output bits in `r1_overflow`
distinguish positive infinity. `tolerance` is the binary64 encoding of `1e-14`.

```lean
theorem large_value : value large = some ((2 : ℚ) ^ (1023 : ℕ))

theorem large_positive : (0 : ℚ) < 2 ^ (1023 : ℕ)

theorem r1_exact :
    (2 : ℚ) ^ (1023 : ℕ) / 2 ^ (1023 : ℕ) * 1000000 = 1000000

theorem r1_overflow :
    (raw large large).toBits = 0x7ff0000000000000 ∧
    value (raw large large) = none ∧
    value (cutoff large large) = some 1000000

theorem r2_boundary_bits :
    (raw ten thirtySix).toBits = 0x4110f4471c71c71c ∧
    (cutoff ten thirtySix).toBits = 0x4110f4471c71c71d ∧
    value (raw ten thirtySix) = some boundaryCPM ∧
    value (cutoff ten thirtySix) = some boundaryCutoff

theorem r2_boundary_errors :
    boundaryCPM - (10 / 36 * 1000000 : ℚ) = -1 / 38654705664 ∧
    boundaryCutoff - (10 / 36 * 1000000 : ℚ) = 5 / 154618822656

theorem r2_count_boundary :
    (10 / 36 * 1000000 : ℚ) ≥ 10 / 36 * 1000000 ∧
    (2 : ℚ) ≥ 2 ∧ (10 + 10 : ℚ) ≥ 15 ∧
    ¬ (boundaryCPM ≥ boundaryCutoff)

theorem r2_sample_tolerance :
    value required = some (1 + 1 / (2 : ℚ) ^ (50 : ℕ)) ∧
    (required.toBits = 0x3ff0000000000004) ∧
    (decide (Float.Model.ofNat 1 ≥ required) = false) ∧
    (decide (Float.Model.ofNat 1 ≥ required - tolerance) = true) ∧
    ((20 : ℚ) ≥ 15)

theorem r2_required_strictly_above_one :
    (1 : ℚ) < 1 + 1 / 2 ^ (50 : ℕ)
```

## Connection to shipped bytes

The checked binary is exactly 96,558 bytes with SHA-256
`e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb`.
The checker verifies both size and digest before running anything. It also
checks pinned SHA-256 digests of the README, both R files, the filtering
documentation, the C header, and the C source; those digests are listed in
`INPUT_HASHES` in `Verification/check.py`.

The Python checker asks `wasm-tools` to validate and print the original module,
then generates separate host and test modules. Wasmtime preloads `edgeR.so`
directly from its original path. The artifact is never rewritten, extracted,
patched, or recompiled from C. Its export `calc_cpm_raw` is function 160;
the execution also uses its original `get_row` implementation.

The test module creates wasm32 `cmx` structures using `src/edgeR.h`'s eight
32-bit fields, initializes the caller-owned CPM array with the input counts,
and invokes the export with one thread. Library sizes use the supported
row-repeated representation, type 2. Shared memory contains the artifact's
static data below the test buffers; the test buffers begin at 65,536, stack
pointer at 524,288, and allocator storage at 1,048,576. The host supplies
zero-initializing, aligned allocation and a no-op free for fresh, short-lived
instances. All other imported functions trap if called. Unused imported
globals are zero. Every observed output is loaded as its exact 64-bit pattern.

Rscript sources the unchanged `R/cpm.R` and `R/filterByExpr.R`. The full edgeR
R package and its native R registration/bridge helpers are not supplied.
The test therefore supplies `makeCompressedMatrix` as a checked argument
container and `.Call` as a bridge that accepts only the two explicitly tested
matrix/library-size pairs. It returns the binary64 arrays previously obtained
by executing the original Wasm export. All supplied R validation, cutoff,
sample-size, total-count and final filtering expressions execute normally.
This bridge is an explicit integration assumption, not a proof of a complete
R package installation or of its unsupplied compiled wrapper.

Lean proves the arithmetic model only. There is no formal interpreter proof
for the whole Wasm module, ABI, allocator, or R runtime. The direct execution
checks connect these particular witnesses to the original software; they do
not establish correctness for other matrices, compression modes, or options.
No source-to-binary equivalence assumption is used for R1.

## Replay commands

From this directory, with the installed offline dependencies:

```sh
lake build
lake env lean Proofs/Counterexamples.lean
python3 Verification/check.py
```

Success requires all three commands to exit with status zero. `lake build`
reports successful completion. The second command prints the axioms of all
nine theorems: only `propext`, `Classical.choice`, and `Quot.sound` occur;
there must be no errors, `sorryAx`, or native-evaluation axiom. Proofs use
kernel reduction (`decide +kernel`) and ordinary checked tactics.

The execution checker must print:

```
overflow result bits: 7ff0000000000000
boundary result bits: 4110f4471c71c71c 41260a5c71c71c72 4110f4471c71c71c 41260a5c71c71c72
tolerance result bits: 4034000000000000 0000000000000000
R1 FAIL witness checked: finite c=L=2^1023; exact CPM=1000000; artifact=+infinity
R2 count-boundary witness: CPM=0x1.0f4471c71c71cp+18, cutoff=0x1.0f4471c71c71dp+18, keep=(FALSE,TRUE)
R2 sample-tolerance FAIL witness checked: required=0x1.0000000000004p+0, qualifying=1, documented=FALSE, actual=TRUE
PASS: all counterexample checks completed
```

`FAIL witness checked` means that a requirement's failure was successfully
reproduced; it is not a failed checker run. The checker requires Python
assertions enabled (use the command above without `-O`). It creates temporary
host modules and removes them afterward. No network is used. Tested tools:
Lean 4.35.0 with Mathlib v4.35.0, wasm-tools 1.262.0, Wasmtime 50.0.0, and
R 4.6.1 on x86-64 Linux.

## Review and trust

Read the following custom proof/model and checking code; sizes are source
lines and bytes, respectively:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexamples.lean` | 95 | 3556 | Model definitions, nine theorem statements and proofs, axiom audits |
| `Proofs.lean` | 1 | 30 | Library root import |
| `Verification/check.py` | 159 | 7796 | Hash checks, host/ABI harness generation, exact artifact execution and bit assertions |
| `Verification/check_filter.R` | 55 | 2498 | R bridge and actual filter executions/assertions |

Relevant original sources are `R/cpm.R` (114 lines, 3771 bytes),
`R/filterByExpr.R` (115 lines, 3745 bytes), `src/edgeR.h` (381 lines, 14858
bytes), and `man/filterByExpr.Rd` (161 lines, 7329 bytes). The C source
`src/compute_cpm.c` is 266 lines, 6996 bytes; it helps explain the operation
order but is not substituted for binary execution.

For the mathematical proofs, trust Lean's kernel and standard logical axioms,
and review the meaning of its `Float.Model` definitions against IEEE binary64.
The installed `Init/Data/Float/Model` source directory is approximately 71 KiB;
it defines packing/unpacking, rounding, multiplication, division, subtraction,
addition, and comparisons used here. Mathlib supplies the rational-number
theory and tactics; its installed `Mathlib` source tree is approximately
97 MiB, and the generated proof terms are checked by Lean.

For the concrete demonstrations, additionally trust Python's standard library
(including SHA-256 and binary packing), wasm-tools' parser/validator/printer,
Wasmtime's execution of the original Wasm, R's interpreter and binary64
arithmetic, the operating system, and the host hardware. The checker-generated
host and bridge code above is part of this trusted connection. The artifact's
96,558 bytes are the subject of the test, not an assumed-correct implementation.
