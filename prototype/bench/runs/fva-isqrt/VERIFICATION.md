# Integer square root verification

## Proven requirements

The Lean 4.35 project in this directory proves both requirements for every
`BitVec 32` input, including zero and `2^32 - 1`.

| Requirement | Specification | Kernel-checked proof |
| --- | --- | --- |
| R1 | `Isqrt.correctness` | `Isqrt.Proof.correctness_holds` |
| R2 | `Isqrt.termination` | `Isqrt.Proof.termination_holds` |

Read [Isqrt/Spec.lean](Isqrt/Spec.lean) for the complete specification.
R1 states that the exported function returns a 32-bit value `r`, that
`r.toNat * r.toNat ≤ n.toNat`, and that **every natural number** `s` with
`s * s ≤ n.toNat` satisfies `s ≤ r.toNat`. These products do not wrap.
R2 states that a finite, nontrapping execution returns a value.
There are no input preconditions beyond the unsigned 32-bit type.

The stronger helper theorem `Isqrt.Proof.isqrt_correct` provides the same
correct result with the uniform FVA fuel value `65585`. This is a bound in
FVA's execution semantics, not a CPU-time or total-instruction-count claim.

## Connection to the code

The proofs concern the **shipped `isqrt.wasm`**, not a separate implementation
of square root. FVA generated [Isqrt/Lifted.lean](Isqrt/Lifted.lean) directly
from its bytes. The specification mentions `Isqrt.Lifted.module` and uses
`FVA.Wasm.Returns` from `../../lean/FVA/Wasm/Semantics.lean`.

The shipped artifact has SHA-256:

```text
0f1e2314be7a8379e735f525ef553d831f98a5b057f85ab1e0a334a6a1010d3e
```

The README's compilation command, using installed Clang 23.1.1, produces a
byte-identical artifact. The unchanged C source has SHA-256:

```text
d9f87637f823a18f616229d6f8a1054b2be434ed301851cbb0ddbe986ec11559
```

[Isqrt/Proof.lean](Isqrt/Proof.lean) establishes these connections:

1. Bit-vector lemmas relate the compiled midpoint, subtraction, zero extension,
   square multiplication, and unsigned comparisons to natural-number arithmetic.
   The square comparison is exact: the midpoint is at most `65536`, so its
   square fits in 64 bits.
2. `loop_unfold` symbolically executes the actual loop instructions under FVA's
   semantics. Both compiled `select` branches and the loop back-edge are covered.
3. `loop_correct` uses strong induction on `hi - lo`. It maintains
   `lo < hi ≤ 65536` and `lo² ≤ n < hi²`; each iteration strictly reduces the
   interval width. Width one implies that `lo` is the largest valid root.
4. `isqrt_correct` executes the function prologue, applies the loop theorem,
   and checks the returned machine value. The two requirement theorems select
   the actual export and supply its finite execution witness.

The duplicated loop list in the proof is not an assumption: Lean checks its
definitional equality to the loop in the generated function when proving
`isqrt_correct`.

## Exact checking commands

All commands below run offline. Start at the repository root.

### Build and independent kernel replay

```sh
cd prototype/fva/examples/isqrt
lake build
lake env leanexport Isqrt -- \
  Isqrt.Proof.correctness_holds Isqrt.Proof.termination_holds \
  > .lake/isqrt-export.ndjson
lake check --from-export=.lake/isqrt-export.ndjson --paranoid
```

This environment does not permit the nested `bubblewrap` sandbox that the last
command requires. It fails before checking proofs, with
`bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted`.
Within this already restricted execution environment, the following command
checks the same export without that additional sandbox:

```sh
lake check --from-export=.lake/isqrt-export.ndjson --paranoid \
  --inadvisably-no-sandbox
```

**Result: exit 0.** All six checkers accepted: Lean paranoid, lean4lean, nanoda,
con-leche, con-ron, and Lean default. The only axioms are `propext`, `Quot.sound`,
and `Classical.choice`. The project has no Mathlib dependency, `sorry`, custom
axioms, native proof shortcuts, or skipped kernel checks. Lake warns that its
additional sandbox is disabled; kernel replay still runs. On a host that
supports `bubblewrap`, use the sandboxed command.

### Source/artifact equality and reproducible lifting

From the repository root, after `lake build`:

```sh
cd prototype/fva
clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all \
  -Wl,--export=isqrt -o examples/isqrt/.lake/isqrt.rebuilt.wasm \
  examples/isqrt/isqrt.c
cmp examples/isqrt/isqrt.wasm examples/isqrt/.lake/isqrt.rebuilt.wasm
uv run --offline fva lift examples/isqrt/isqrt.wasm \
  examples/isqrt/.lake/Isqrt.relifted.lean --ns Isqrt.Lifted
cmp examples/isqrt/Isqrt/Lifted.lean examples/isqrt/.lake/Isqrt.relifted.lean
```

**Result: exit 0; both comparisons are byte-identical.**

### FVA audit and differential check

From the repository root:

```sh
cd prototype/fva
uv run --offline fva trust examples/isqrt --paranoid
uv run --offline fva difftest examples/isqrt
```

The unmodified `fva trust` command reports **FAIL, exit 1**, solely because its
internal `lake check` cannot start the nested sandbox described above. Its
other checks pass: both claims have proofs and mention the implementation;
the pinned hash matches; re-lifting is identical; the specification has no
syntax extensions; and the axiom/override audit finds no issues. The separate
six-kernel replay above checks the exported proofs successfully. This is not
reported as an unqualified FVA PASS.

`fva difftest` returns **exit 0: 200 cases, zero mismatches** between FVA's Lean
semantics and the real binary in wasmtime. This test supports the
semantics/lifter connection; it does not replace the universal proofs.

## Trust boundary and remaining limits

Both R1 and R2 are proved for the pinned shipped WebAssembly under FVA's
semantics. No requirement is left as an assumption or admitted lemma.

The trusted base comprises the Lean kernels and standard axioms, Lean's core
definitions used in the specification, FVA's WebAssembly semantics, and FVA's
binary lifter. The specification remains a human-review obligation.
Equivalence between FVA's semantics and the official WebAssembly semantics
is not formally proved here; the differential check supplies testing evidence.

There is no formal C-language semantics proof, compiler-correctness proof, or
claim about other builds or targets. The source-to-artifact connection is the
reproducible byte comparison above. The compiler need not be trusted for the
proved behavior of this artifact. The nested-sandbox restriction is the only
incomplete tool check; independent kernel replay succeeds without that layer.
