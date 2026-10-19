# Verification

## Result and scope

R1 and R2 are proved in Lean 4.35.0 for a fixed-width operational model of the
unchanged `isqrt.c`, using the README's wasm32 data model: 32-bit `unsigned` and
64-bit `unsigned long long`. Only Lean's bundled standard library is used; no
Mathlib, downloads, external solver, or exhaustive input testing is needed.

The C-to-Lean transcription is manually reviewed, not produced by a verified C
frontend. The exact source is pinned by a checked equality. See **Trust boundary**
below; this is not an end-to-end proof about compiled WebAssembly execution.

## What is proved

The main theorem is `Isqrt.Machine.verified` in `Machine.lean`. For **every**
`n : UInt32`, it establishes a result `r : UInt32` and iteration count `k` such that:

- The modeled C loop executes from `lo = 0, hi = 65536` and returns `r`.
- **R1:** `r.toNat * r.toNat ≤ n.toNat`, and every natural number `q` with
  `q * q ≤ n.toNat` satisfies `q ≤ r.toNat`. Specification products use unbounded
  `Nat` arithmetic, so the claim cannot be weakened by overflow.
- **R2:** The execution is finite. Termination is proved by a strictly decreasing
  natural-number measure `hi - lo`, not by assuming a fuel limit.
- Additionally, `k ≤ 16`, and every execution has the same result and iteration
  count. `every_execution_correct` proves correctness and the bound for any
  execution derivation, not just the witness constructed by the termination proof.

`Isqrt.Machine.no_overflow` proves, at every reachable loop header:

- `lo ≤ hi < 2^32`, and the mathematical subtraction `hi - lo` fits in 32 bits;
- the mathematical midpoint addition fits in 32 bits;
- the mathematical midpoint square fits in 64 bits, as does the widened input.

Division is always by the nonzero literal `2`. Initialization and assignments
are in range. The lemmas `sub32_exact`, `midpoint_exact`, `cast64_exact`, and
`square64_exact` show that modular arithmetic agrees with unbounded arithmetic
under the invariant. Thus the proofs do not silently replace potentially
wrapping C operations with natural-number operations.

The maintained invariant is:

```text
0 ≤ lo < hi ≤ 65536
lo * lo ≤ n < hi * hi
```

The initial upper square is `65536² = 2^32`, strictly greater than every input.
When the guard is true the midpoint is strictly between the endpoints. On exit,
`hi = lo + 1`, which proves maximality. Each body execution reduces the interval
to at most its rounded-up half, yielding the 16-iteration bound.

## How the proofs connect to the code

`Machine.lean` mirrors each C expression using actual Lean `UInt32` and `UInt64`
operations, including modular subtraction, addition, division, and multiplication:

| C construct | Fixed-width Lean model |
| --- | --- |
| `unsigned n`, `lo`, `hi`, `mid` | `UInt32` input, fields, and midpoint |
| `lo = 0, hi = 65536` | `Machine.initial` |
| `hi - lo > 1` | `Machine.guard` |
| `lo + (hi - lo) / 2` | `Machine.mid` |
| `(unsigned long long)mid * mid <= n` | `m.toUInt64 * m.toUInt64 ≤ n.toUInt64` in `Machine.step` |
| `lo = mid` / `hi = mid` | The two state updates in `Machine.step` |
| `while (...) { ... }`, then `return lo` | `Machine.Executes` |

The C cast causes the second multiplication operand and the comparison's input
to be converted to `unsigned long long` by the usual arithmetic conversions;
these conversions are explicit in Lean. The input remains unchanged.

`Executes.done` is allowed only when the guard is false and returns `lo`.
`Executes.step` requires a true guard and a complete execution of the next state.
There is no arbitrary early-stop or fuel-exhaustion rule.

`Isqrt.lean` supplies a second model with explicit modular arithmetic on natural
numbers, the invariant, arithmetic bounds, and binary-search proofs.
`Machine.step_refines`, `execution_refines`, and `reachable_refines` prove that
the fixed-width model maps to that arithmetic model. These refinement results
are checked in Lean, not assumed.

`Check.lean` reads the actual `isqrt.c` with `include_str` and proves its equality
to the exact reviewed text by `rfl`. A source edit therefore invalidates the
check. **This is a source pin, not a semantic translation proof.** `verify.sh`
always re-elaborates this check, avoiding a stale Lake cache for the external C
file. The original C, README, and shipped Wasm are not modified.

## Exact checking commands

From the repository root, with the installed Lean 4.35.0 and Lake:

```sh
./verify.sh
```

The script runs these commands and stops on any failure:

```sh
lake build
lake env lean -DwarningAsError=true ./Isqrt.lean
lake env lean -DwarningAsError=true ./Machine.lean
lake env lean -DwarningAsError=true ./Check.lean
```

For a fresh build, run `lake clean` before `./verify.sh`. The package has no
external dependencies. `lean-toolchain` pins version 4.35.0. `lake build` alone
does not replace the final, uncached source-pin check.

`Check.lean` also prints the axioms of the main results. The source equality
uses none; the semantic proofs use only standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound` (some results use a subset). There are no
custom axioms, `sorry`, `admit`, or `native_decide` proofs. The final verification
script completed successfully, with warnings treated as errors.

## Trust boundary and unproved items

- The correspondence between ISO C semantics and the small operational model is
  a manual transcription/review obligation. No general C parser, typechecker, or
  verified C semantics is included. The source pin detects changes but cannot
  prove that this transcription is correct.
- The target's integer widths are assumed by the model, consistent with the
  README's wasm32 build. The installed Clang reports `__CHAR_BIT__ = 8`,
  `__SIZEOF_INT__ = 4`, and `__SIZEOF_LONG_LONG__ = 8` for that target. No claim is
  made for a target with different integer widths.
- Clang/linker correctness, the Wasm binary's semantics, and the Wasm execution
  engine are not formally verified. As a separate non-proof cross-check, the
  README build command was run with output redirected to
  `.lake/build/isqrt-rebuilt.wasm`; `cmp` confirmed it is byte-identical to the
  shipped `isqrt.wasm`. Both have SHA-256
  `0f1e2314be7a8379e735f525ef553d831f98a5b057f85ab1e0a334a6a1010d3e`.
- Lean's kernel and bundled logical definitions remain the proof-checking trust
  base. All stated obligations for the modeled function are discharged; there
  are no remaining proof holes.
