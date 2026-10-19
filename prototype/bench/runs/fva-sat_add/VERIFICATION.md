# Verification of `sat_add`

## What is proven

Lean 4.35.0 proves all three README requirements for the shipped WebAssembly
function, for **every pair of 32-bit input patterns** (all 2^64 pairs):

| Requirement | Claim in `SatAdd/Spec.lean` | Proof in `SatAdd/Proof.lean` |
| --- | --- | --- |
| R1: return the mathematical sum when -2147483648 ≤ sum ≤ 2147483647 | `SatAdd.r1` | `SatAdd.Proof.r1_holds` |
| R2: return 2147483647 when sum > 2147483647 | `SatAdd.r2` | `SatAdd.Proof.r2_holds` |
| R3: return -2147483648 when sum < -2147483648 | `SatAdd.r3` | `SatAdd.Proof.r3_holds` |

Inputs are `BitVec 32`; `toInt` interprets them as signed two's-complement
integers. The specification adds those values in unbounded Lean `Int`.
R1's `BitVec.ofInt 32 sum` encodes that exact integer, because its hypotheses
put it within the signed range. The result pattern `2147483648#32` in R3
represents -2147483648, not positive 2147483648.

Every claim uses FVA's `Returns` for the exported function `"sat_add"` of
`SatAdd.Lifted.module`. Thus it proves termination without trapping and the
exact single i32 result, not merely a property conditional on termination.
`invoke_result` supplies the same sufficient fuel, 30, for every input.

## Connection to the C code

The original C, README, and shipped binary are unchanged. Rebuilding with the
README command and installed **clang 23.1.1** produced the identical 87-byte
`sat_add.wasm`. SHA-256 values:

```text
sat_add.c     ff1a119f0a6467fbb41fb27acd5d7bb8d63689d9bd7f32af1cf27fb8f3164550
sat_add.wasm  cd4ffd1bdffc619863f7e6c496a9952c9412c0534d66f1b0dc89000914bd8342
```

`SatAdd/Lifted.lean` was generated with `fva lift`, not handwritten. FVA
confirmed both the binary hash and byte-for-byte equality with a fresh lift.
The specifications refer directly to this generated module under
`../../lean/FVA/Wasm/Semantics.lean`.

The compiled function uses wrapping addition, signed comparisons, an arithmetic
shift, XOR, and `select`. The proof symbolically executes these instructions
with FVA's `wasm_sim`, proves the overflow test and saturation mask using
kernel-checked integer arithmetic, and equates the result with a clamp of a
sign-extended 33-bit sum. `wideSum_toInt` proves that this wider sum is exactly
the mathematical integer sum. The three requirement proofs then follow from
the corresponding bounds.

There is no Mathlib, network dependency, `sorry`, custom axiom, or native
decision procedure in the final proofs. The only axiom dependencies reported
by FVA are `propext`, `Classical.choice`, and `Quot.sound`.
The specification imports only FVA's semantics and the generated lift; it
does not import proof code or custom syntax.

## Exact checking commands

From the repository root, run:

```sh
cd prototype/fva/examples/sat_add
sh check-proofs.sh
```

This script stops on any failure. It recompiles the C using the README flags,
compares the binary, regenerates and compares the FVA lift, runs `lake build`,
and exports precisely the three requirement proofs and their dependencies:

```sh
lake env leanexport SatAdd -- \
  SatAdd.Proof.r1_holds SatAdd.Proof.r2_holds SatAdd.Proof.r3_holds \
  > .lake/verification/proofs.ndjson
```

It replays that export through all six installed checkers: Lean default
(`leanchecker`), Lean paranoid (`leanchecker-paranoid`), `lean4lean`, `nanoda`,
`con-leche`, and `con-ron`. **All six passed.** Exact invocations and nanoda's
standard-axiom allowlist are in `check-proofs.sh`; observed output is saved in
`kernel-replay-report.txt`. The script runs the checker executables directly
inside the existing task environment; it changes no sandbox or system setting.

To run the FVA audit and differential test, from the repository root:

```sh
cd prototype/fva
uv run --offline fva trust examples/sat_add --paranoid --json
uv run --offline fva difftest examples/sat_add --cases 1000 --seed 0 --json
```

The differential test passed: **1,000 cases, zero mismatches** between FVA's
Lean execution semantics and wasmtime. This is supporting evidence, not the
universal proof. Its result is saved in `difftest-report.json`.

**FVA wrapper limitation:** the unmodified `fva trust` command reports `FAIL`
in this environment solely because its `lake check` subprocesses cannot start
their additional bubblewrap sandbox:

```text
bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted
```

`trust-report.json` preserves this result. Its build, implementation hash,
re-lift, requirement/proof linkage, axiom, and syntax/override checks pass;
its only issue is replay process launch. The direct six-kernel replay above
checks the same three proof roots successfully. No FVA implementation was
modified and the failed wrapper result has not been relabeled as `PASS`.

## Trust boundary and things not proven

All R1–R3 obligations are proved for the pinned WebAssembly under FVA's
semantics. As documented by FVA, its WebAssembly semantics and binary-to-Lean
lifter remain trusted, along with the kernels and standard logical axioms.
The differential test is not a proof that the lifter or semantics implements
the entire WebAssembly standard correctly.

There is no formal ISO C semantics/compiler-correctness theorem here: the
source-to-artifact connection is the checked, reproducible byte equality,
not a verified compiler pass. Other compilation targets, future source or
binary revisions, actual runtime implementations, and resource/timing or
side-channel properties are outside these claims. FVA's nested-sandbox replay
wrapper could not be completed in this environment, as detailed above.
