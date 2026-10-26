The stated requirements do not both hold as universal mathematical guarantees. The results below are counterexamples executed against the original WebAssembly and R sources, supplemented by Lean certificates for their exact arithmetic. There is no claim of a complete formal semantics or a universal correctness proof for WebAssembly, C, or R.

**R1: no finite rounding-error bound on the stated domain.**

Use a 1-by-1 matrix with count `c = 2^1023` and library size `L = 2^1023`, both finite, exactly representable binary64 values, with `0 <= c <= L`. Initialize the caller-owned CPM buffer with `c` and call the exported `calc_cpm_raw` with one thread. The original artifact returns positive infinity, bits `7ff0000000000000`. The exact required value `c / L * 1000000` is exactly representable as `1000000`, bits `412e848000000000`.

The compiled function evaluates `RN(RN(c * 1000000) / L)`. Its multiplication overflows before division. The executable assertions are in `verification/artifact.mjs`; `overflow_witness` and `overflow_target_is_exact_binary64` in `Proofs/Counterexamples.lean` certify the rational inequalities and exact target. Consequently no finite absolute or relative error bound against the mathematical CPM can hold for every finite count and positive finite library size in the README's domain. This witness does not rely on an unrepresentable final answer.

If “rounded as double-precision arithmetic allows” is intended to permit intermediate overflow in this particular operation sequence, this is an exhibited limitation of that interpretation, rather than an IEEE-754 violation. No universal finite-error theorem is asserted under that interpretation. A theorem restricted to safe intermediate ranges would be a different, weaker requirement and is not proved here.

One finite rounding error is certified exactly: at `c = 10, L = 18`, the artifact's result has absolute error `1 / 19327352832` and relative error `1 / 10737418240000000` against the exact CPM `5000000/9`. This is a correctly rounded result for that input. These are witness-specific errors, not bounds for all inputs.

**R2: the “exactly when” rule fails as stated; a separate rounding boundary also fails the ideal count criterion.**

Two explicit inputs are checked in `verification/filter.R`:

1. `y = matrix(10, 1, 1)`, `lib.size = 1000000`, `min.sample.size = 1`, other arguments default. CPM is exactly 10, the CPM cutoff is exactly 10, and one sample qualifies. Nevertheless the shipped `filterByExpr` returns `FALSE`: the total count is 10, below the default `min.total.count = 15`. Thus the README's sample criterion alone is not equivalent to keeping a gene. The manual does document the additional total-count condition; this witness is a discrepancy with the README's literal R2, not a claim that this total-count check contradicts the full manual.

2. All-default call on this numeric matrix (rows are genes, columns are samples):

   ```text
   10  10
    8   8
   ```

   Library sizes default to column sums `[18,18]`, their median is 18, the required number of samples is 2, and the first gene has total count 20. Both its samples reach `min.count = 10` exactly, including the documented scaling at the median library size. In exact arithmetic their CPM and the cutoff are the same number, `5000000/9`. But the actual values are:

   | Quantity | Exact binary64 value as a rational | Binary64 bits |
   |---|---|---|
   | Artifact CPM, `RN(10000000 / 18)` | `4772185884444444 / 8589934592` | `4120f4471c71c71c` |
   | R cutoff, `RN(RN(10 / 18) * 1000000)` | `4772185884444445 / 8589934592` | `4120f4471c71c71d` |

   The CPM is one ULP (`2^-33`) below the cutoff. Zero samples qualify in the implemented comparison; the first gene is rejected despite satisfying the ideal count threshold and the total-count condition. The returned vector is `[FALSE,FALSE]`. The code's `1e-14` tolerance applies to the number of qualifying samples and the total count; it does not adjust this CPM comparison. A control using one row `[11,11]` with library sizes `[18,18]` is retained.

The second witness concerns an exact count-threshold interpretation of R2. If R2 instead means comparing the already-rounded CPM against the already-rounded cutoff, with the extra total-count test included, this witness agrees with that operational rule. It exposes the difference between that rule and the ideal count threshold, not an incorrect Boolean comparison. No universal theorem for every design, group, preset, or input type is claimed.

All eight Lean theorem statements follow, exactly as declared in `Proofs/Counterexamples.lean` (inside namespace `Verification`; proof bodies omitted):

```lean
theorem boundary_raw_round :
    NormalRound ((10 : ℚ) * 1000000 / 18) 4772185884444444 (-33)

theorem boundary_first_cutoff_round :
    NormalRound ((10 : ℚ) / 18) 5003999585967218 (-53)

theorem boundary_second_cutoff_round :
    NormalRound (roundedCountOverLibrary * 1000000) 4772185884444445 (-33)

theorem boundary_disagreement :
    (10 : ℚ) / 18 * 1000000 = 5000000 / 9 ∧
    rawBoundary < cutoffBoundary ∧
    cutoffBoundary - rawBoundary = (2 : ℚ)^(-33 : ℤ) ∧
    |rawBoundary - (10 : ℚ) / 18 * 1000000| = 1 / 19327352832 ∧
    |rawBoundary - (10 : ℚ) / 18 * 1000000| /
      ((10 : ℚ) / 18 * 1000000) = 1 / 10737418240000000

theorem overflow_witness :
    0 < (2 : ℚ)^1023 ∧
    (2 : ℚ)^1023 < overflowThreshold ∧
    overflowThreshold ≤ (2 : ℚ)^1023 * 1000000 ∧
    (2 : ℚ)^1023 / (2 : ℚ)^1023 * 1000000 = 1000000

theorem overflow_target_is_exact_binary64 :
    (8589934592000000 : ℚ) * (2 : ℚ)^(-33 : ℤ) = 1000000 ∧
    NormalRound 1000000 8589934592000000 (-33)

theorem total_count_witness :
    (10 : ℚ) / 1000000 * 1000000 = 10 ∧
    (1 : ℚ) ≥ 1 ∧ ¬ filterTail 1 1 10 15

theorem boundary_filter_witness :
    (10 : ℚ) ≥ 10 ∧ (20 : ℚ) ≥ 15 ∧
    filterTail 2 2 20 15 ∧ ¬ filterTail 0 2 20 15
```

The definitions those statements use are also in that file:

```lean
def NormalRound (x : ℚ) (m : ℕ) (e : ℤ) : Prop :=
  2^52 < m ∧ m < 2^53 - 1 ∧ -1074 ≤ e ∧ e ≤ 971 ∧
  (m : ℚ) * (2 : ℚ)^e - (2 : ℚ)^e / 2 < x ∧
  x < (m : ℚ) * (2 : ℚ)^e + (2 : ℚ)^e / 2

def rawBoundary : ℚ := 4772185884444444 / 8589934592
def cutoffBoundary : ℚ := 4772185884444445 / 8589934592
def roundedCountOverLibrary : ℚ := 5003999585967218 / 9007199254740992
def overflowThreshold : ℚ := (2 : ℚ)^1024 - (2 : ℚ)^970

def filterTail (qualifyingSamples required total minTotal : ℚ) : Prop :=
  qualifyingSamples ≥ required - 1 / 10^14 ∧ total ≥ minTotal - 1 / 10^14
```

`NormalRound` is a strict midpoint certificate for an interior positive normal binary64 number `m * 2^e`: its two neighbors are spaced by `2^e`. All witnesses avoid ties, subnormals, and binade endpoints. It is a definition for rational arithmetic certificates, not an implementation of all IEEE-754 operations. `overflowThreshold` is the nearest-rounding overflow midpoint. Interpreting these definitions as binary64 rounding facts requires checking that correspondence. `filterTail` models only the final two comparisons, using exact rational `10^-14`; it is not a translation of the whole R program. The concrete witnesses are far enough from these two tolerance boundaries that rounding the R tolerance cannot change them. The R execution checks the actual double operations.

**Connection to the shipped bytes and execution environment.**

`edgeR.so` is unchanged: 96,558 bytes, SHA-256 `e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb`. `verification/artifact.mjs` checks both before instantiating those exact bytes with Node's WebAssembly engine. It calls the artifact's exported `make_cmx` to construct matrix descriptors, then its exported `calc_cpm_raw`; library descriptors have type 2 (a repeated row). Counts are installed in the caller-owned output buffer, matching the function's in-place interface. Neither the arithmetic nor `get_row` is replaced with a source model, and nothing is recompiled or patched.

The side module needs host imports. The harness supplies 16 memory pages, a function table, stack/memory/table-base globals, other imported globals, and a zeroing allocator with checked allocation/free pairing. Static data, the stack, and these small heap allocations occupy disjoint regions. All function imports except `R_chk_calloc` and `R_chk_free` throw if called. The tested `make_cmx`/`calc_cpm_raw`/`get_row` path needs no R objects, BLAS, libm, constructors, or GOT pointer contents. This is an isolated execution of the exported kernel in a compatible host environment, not a full R-universe installation.

`verification/filter.R` sources the unchanged `R/cpm.R` and `R/filterByExpr.R`. It supplies a restricted `makeCompressedMatrix` adapter for double library-size vectors and a `.Call` bridge that invokes the Node harness and reshapes its results as an R matrix. The bridge accepts only the raw CPM entry point and one thread. Thus the actual shipped `cpm.default` performs its validation and dispatch, the original WebAssembly computes CPM, and the actual shipped `filterByExpr.default` computes its cutoff and keep decision. No edgeR package is installed or assumed. The missing package's general compression and R SEXP wrapper are not verified or executed. Decimal transport uses 17 significant digits, which round-trips these binary64 inputs/results exactly; the boundary outputs are independently checked by bit assertions in Node.

`verification/inputs.sha256` pins the original artifact, both R sources, both C/header files, both manuals, README, and CHECK. The C source and header explain the interface but are not used as evidence that compilation preserved it. To inspect the artifact independently, run `wasm-tools print edgeR.so -o /tmp/edger-verification.wat`. In that printout, `calc_cpm_raw` is function 160 (142 lines), `make_cmx` is function 204 (26 lines), and `get_row` is function 207 (220 lines); the multiplication/division sequence is visible in function 160. This inspection is optional for reproduction but useful for auditing the host setup.

**Reproduction, from this directory, without network access.**

Run these commands, stopping on any nonzero exit status:

```sh
sha256sum -c verification/inputs.sha256
wasm-tools validate edgeR.so
lake build
lake env lean Proofs/Counterexamples.lean
node verification/artifact.mjs
Rscript --vanilla verification/filter.R
```

Success means all nine hashes report `OK`, validation exits zero, Lake reports a successful build, and the direct Lean command exits zero and prints axiom information for all eight theorems. Each theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; there must be no `sorryAx`. The two scripts must exit zero and end with `PASS: all artifact assertions` and `PASS: all shipped-R assertions (CPM supplied by the original WebAssembly)`, respectively. They print the counterexample values before those lines. R's messages about assuming one group are expected. A `PASS` confirms reproduction of the failures, not satisfaction of R1 or R2. No `sorry`, admitted theorem, native evaluation oracle, or extra axiom is used in the proofs.

The environment used is Lean 4.35.0, Mathlib v4.35.0 (manifest commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), Node v26.11.1, R 4.6.1, and wasm-tools 1.262.0. Lake uses the already-built packages specified in `lakefile.toml`; these commands do not update or download dependencies.

**Review and trust inventory.**

| Local material | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs/Counterexamples.lean` | 83 | 3536 | All arithmetic model definitions, proof bodies, and axiom queries |
| `Proofs.lean` | 1 | 30 | Imports the proof module into the Lake build |
| `verification/artifact.mjs` | 85 | 3816 | Hash check, Wasm host setup, direct kernel invocation, bit/value assertions |
| `verification/filter.R` | 48 | 2410 | Missing-package adapters, actual R execution, and witness assertions |
| `verification/inputs.sha256` | 9 | 708 | Original-input identity checks |
| `R/cpm.R` | 114 | 3771 | Shipped R CPM dispatch and validation |
| `R/filterByExpr.R` | 115 | 3745 | Shipped filter, including total-count and tolerance behavior |
| `src/edgeR.h` | 381 | 14858 | Interface/layout explanation; not a compilation certificate |
| `src/compute_cpm.c` | 266 | 6996 | Source-level explanation; direct artifact execution is the binary connection |
| `man/filterByExpr.Rd` | 161 | 7329 | Documented filtering criterion and total-count condition |
| `man/cpm.Rd` | 160 | 7280 | Documented CPM interface |
| `README.md` | 13 | 1287 | Requirements and artifact identity |
| `CHECK.md` | 8 | 784 | Requested reporting standard |
| `lakefile.toml` | 12 | 264 | Build configuration and dependency location |
| `lake-manifest.json` | 117 | 3536 | Pinned Lean package dependencies |
| `lean-toolchain` | 1 | 25 | Lean version |
| `edgeR.so` | binary | 96558 | Exact executed artifact |

The trusted computing base also includes the Lean kernel, its ordinary logical axioms, the installed Mathlib definitions and imported theorem environment, the Node/V8 WebAssembly and JavaScript implementation, base R and its numerical operations, subprocess/decimal transport, SHA-256 tooling, and the operating system/hardware. Mathlib is a large installed dependency, not an additional small handwritten model; no size claim for it or these external runtimes is made. Lean checks the arithmetic certificates; the execution harnesses and their correspondence to the interfaces require review. A universal kernel-checked refinement proof from the binary or full R program to the requirements has not been established. The concrete counterexamples suffice to preclude the stronger universal guarantees described above.
