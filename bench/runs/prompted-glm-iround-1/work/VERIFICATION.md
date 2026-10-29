# Verification result

**R1 is false for the shipped artifact.** Run everything, offline, from this directory:

```sh
./check.sh
```

Success is exit status 0 and the final line:

```text
PASS: R1 is FALSE; exact artifact counterexample, proofs, and rejection controls checked.
```

This means the counterexample and checking setup were verified; it does **not** mean R1 holds. Any failed artifact check, execution, compilation, proof replay, or rejection control makes the command fail.

## R1: exact counterexample

| Item | Value |
|---|---|
| Input binary64 bits | `0x3fdfffffffffffff` |
| Exact input | `9007199254740991 / 18014398509481984 = 1/2 − 2⁻⁵⁴` |
| Approximate decimal | `0.49999999999999994` |
| Actual exported `iround` result | `1` |
| Distance to `0` | `1/2 − 2⁻⁵⁴` |
| Distance to returned `1` | `1/2 + 2⁻⁵⁴` |

The input is finite and within `0 ≤ x ≤ 2147483647`. There is a **strictly closer integer**, so the tie allowance cannot rescue this result.

The following is the exact specification definition and theorem statement in [Proofs/Counterexample.lean](Proofs/Counterexample.lean). The denominator is positive; multiplying all distances and bounds by it preserves their comparisons. `Int.natAbs` is integer absolute value, so `Nearest` expresses nearest rounding of the exact rational `num / den`, allowing ties and considering every integer, including negative integers.

```lean
def Nearest (num den result : Int) : Prop :=
  ∀ n : Int, (num - result * den).natAbs ≤ (num - n * den).natAbs

theorem r1_counterexample :
    let num : Int := 9007199254740991
    let den : Int := 18014398509481984
    0 < den ∧ 0 ≤ num ∧ num ≤ 2147483647 * den ∧
      (num - 0 * den).natAbs < (num - 1 * den).natAbs ∧ ¬ Nearest num den 1
```

The proof uses `decide +kernel` and ordinary proof terms. It uses **no axioms**, `sorry`, native decision oracle, or external solver.

The check also generates and freshly compiles [.verification/Observation.lean](.verification/Observation.lean), using the exact rational decoded from the wrapper's input bits and the integer actually printed by Wasmtime. Its exact theorem statement on this artifact is:

```lean
theorem Observation.r1_failure :
    let num : Int := 9007199254740991
    let den : Int := 18014398509481984
    let output : Int := 1
    0 < den ∧ 0 ≤ num ∧ num ≤ 2147483647 * den ∧
      ¬ Verification.Nearest num den output
```

Its proof applies `Verification.r1_counterexample`. This compilation would fail if the observation did not match the proved witness. There are no other numbered requirements in README.md.

## Connection to the shipped implementation

The check requires the original **66 bytes** of `glm-iround.wasm`, with SHA-256:

```text
eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
```

It validates and disassembles that file, then loads that very file into Wasmtime using `--preload artifact=glm-iround.wasm`. [verification/witness.wat](verification/witness.wat) imports its `iround` export, constructs the input with `i64.const 0x3fdfffffffffffff; f64.reinterpret_i64`, and calls the imported function. No decimal input parser participates. Python's `struct.unpack` and `float.as_integer_ratio` check the exact finite input and supply the integers used in the generated theorem. Wasmtime must return exactly `1`.

The disassembly saved as [.verification/artifact.wat](.verification/artifact.wat) shows:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

The exact sum is `1 − 2⁻⁵⁴`, halfway between the adjacent binary64 numbers `1 − 2⁻⁵³` and `1`. Round-to-nearest, ties-to-even produces `1`, which the final conversion preserves.

**Scope:** this is an execution-backed refutation of a universal requirement, with kernel-checked arithmetic and a checked binding to the observed input/output. It is not a formalization of WebAssembly execution or a proof of the C++ compiler. The Wasm runtime and input-bit interpretation are explicit trusted components. No implementation model substitutes for the shipped artifact, and the C++ source, GLM headers, build script, and Wasm bytes were not changed or rebuilt.

## Independent replay and false-proof controls

`./check.sh` freshly compiles the proof and observation into `.verification/`, exports `Observation.r1_failure` and its full dependency closure, rejects **any axiom**, and replays the same export through:

- Lean's default C++ kernel, via `leanchecker --from-export`;
- `con-leche`, the separate checker implemented in Lean, in `--verified` mode;
- `con-ron`, the checker implemented in Rust, in `--verified` mode.

All three accepted the proof. Each checker also accepts a valid control proof of `(0 : Nat) = 0`, then rejects two well-formed exports carrying that same proof with its claimed type changed to `(0 : Nat) = 1` and to `False`. A control passes only with exit status **1 and an explicit type-mismatch diagnostic**; missing tools, parsing errors, crashes, and arbitrary nonzero statuses do not count as rejection. [verification/Controls.lean](verification/Controls.lean) and [verification/check.py](verification/check.py) contain the control construction.

Detailed execution, compilation, acceptance, and rejection logs, both false exports, and the actual proof export are regenerated under `.verification/`. The replay tools are taken from the installed Lean toolchain's `bin` directory. The command requires that toolchain, Lake's configured local packages, Python 3, `wasm-tools`, and `wasmtime`; it does not fetch dependencies.

## Review surface and sizes

The application-specific specification is **13 nonblank lines**: the two-line `Nearest` definition, the five-line original theorem signature, and the six-line observation theorem signature quoted above. There is no floating-point interpreter, hand-written implementation model, or additional application axiom to review. The entire original Lean proof file is **18 lines / 748 bytes**; the generated observation file is **12 lines / 494 bytes**.

These counts do not hide library definitions: the conservative **complete replay closure**, including proof dependencies, is **279,566 bytes** of NDJSON. It contains **113 definition records, 25 inductive blocks, 28 theorem records, and zero axioms, opaque definitions, or quotient declarations**. This upper-bounds the definitions needed by the statements. It includes the standard meanings of integers, naturals, arithmetic, order, absolute value, conjunction, and quantification from Lean's `Init`; no Mathlib definitions are used. All dependency bodies are present in [.verification/proof.ndjson](.verification/proof.ndjson); names and record counts are regenerated in [.verification/dependency-inventory.json](.verification/dependency-inventory.json). Library theorem proofs are replayed rather than assumed.

The artifact-to-statement bridge and checking orchestration must also be reviewed:

| File | Physical lines | Bytes |
|---|---:|---:|
| `check.sh` | 4 | 104 |
| `verification/check.py` | 146 | 6,576 |
| `verification/witness.wat` | 6 | 191 |
| `verification/Controls.lean` | 3 | 129 |

In addition to these files and the formal statements/definitions, the trust boundary includes the installed checker/exporter binaries, Wasmtime's WebAssembly execution, wasm-tools' wrapper assembly, Python's bit decoding and subprocess/file/hash operations, and the host OS/hardware. Independent kernels and rejection controls reduce reliance on any one proof checker; they do not eliminate these execution and tooling assumptions. GLM source correctness and the compiler are not assumptions of this counterexample.
