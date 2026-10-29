# Verification result

**R1 is false for the shipped `glm-iround.wasm`.** The counterexample is the
finite binary64 value with bits `0x3fdfffffffffffff`:

```text
x = 9007199254740991 / 18014398509481984
  = 0.499999999999999944488848768742172978818416595458984375
iround(x) = 1
```

It satisfies `0 ≤ x ≤ 2147483647`. Its unique nearest integer is `0`:

```text
|x - 0| = 9007199254740991 / 18014398509481984
|x - 1| = 9007199254740993 / 18014398509481984
```

The inequality is strict, so the allowance for halfway cases cannot rescue
this result. R1 is the only requirement listed in README.md.

## Machine-checked mathematics

All the following declarations are in `Proofs/Counterexample.lean`, inside
namespace `Counterexample`. Here are the exact definitions and theorem
statements (proof bodies are in that file):

```lean
noncomputable def input : ℝ := 9007199254740991 / 18014398509481984

def IsNearest (x : ℝ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |x - (n : ℝ)| ≤ |x - (m : ℝ)|

theorem input_binary64_value :
    input = (1 + (4503599627370495 : ℝ) / 4503599627370496) / 4

theorem input_in_domain : 0 ≤ input ∧ input ≤ 2147483647

theorem zero_strictly_nearer_than_one :
    |input - (0 : ℝ)| < |input - (1 : ℝ)|

theorem zero_unique_nearest (n : ℤ) (hn : n ≠ 0) :
    |input - (0 : ℝ)| < |input - (n : ℝ)|

theorem zero_is_nearest : IsNearest input 0

theorem one_not_nearest : ¬ IsNearest input 1

theorem r1_counterexample :
    0 ≤ input ∧ input ≤ 2147483647 ∧ ¬ IsNearest input 1
```

`IsNearest` compares against every mathematical integer and accepts ties.
The arithmetic uses exact real numbers, without floating point evaluation,
`sorry`, extra axioms, or `native_decide`. The binary64 identity is the
normal-number value formula for sign 0, biased exponent 1021 (exponent -2),
and fraction 4503599627370495. Finiteness and the actual bits are also checked
by the executable check below.

## Connection to the shipped bytes

`check_counterexample.py` reads the actual artifact and requires both its
66-byte length and the README SHA-256:

```text
eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
```

It additionally compares all 66 bytes against a literal hex string, so the
identification does not rely on collision resistance. It writes those checked
bytes to a temporary snapshot, validates it using `wasm-tools`, and executes
its `iround` export using Wasmtime. The argument is the full exact decimal
above. The script checks that this decimal equals the rational witness, that
its binary64 encoding is `0x3fdfffffffffffff`, and that its exact binary64
rational value agrees. It requires the execution result to be `1` and checks
the strict distance inequality using Python's exact `Fraction` arithmetic.
Failed checks or tool failures cause a nonzero exit status.

For inspection, `wasm-tools print glm-iround.wasm` shows this function body:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

The reason for the failure is that the exact sum `x + 0.5 = 1 - 2^-54`
is halfway between the binary64 predecessor of 1 and 1. The addition rounds
to 1 under ties-to-even, and integer truncation then returns 1.

This is an executed counterexample to the exact artifact, together with
kernel-checked mathematics for the specification violation. The execution
result and binary64 decoding are **not** proved inside Lean; no formal Wasm
interpreter or compiler correctness theorem is claimed. The GLM headers and
C++ build recipe are not needed for the result, and the artifact is not rebuilt
or modified.

## Reproduction (offline, from this directory)

Run:

```sh
lake build
lake env lean Proofs/Counterexample.lean
python3 check_counterexample.py
```

All three commands must exit with status 0. `lake build` reports successful
completion. The direct Lean invocation rechecks the proof source and prints
axioms for `input_binary64_value`, `zero_is_nearest`, and `r1_counterexample`;
each list contains only the standard axioms `propext`, `Classical.choice`,
and `Quot.sound` (order may vary), with no `sorryAx`. The Python output is:

```text
PASS: exact 66 artifact bytes match README; Wasm validates
PASS: finite binary64 input bits = 0x3fdfffffffffffff
PASS: x = 9007199254740991/18014398509481984; iround(x) = 1
PASS: distance to 0 = 9007199254740991/18014398509481984 < distance to 1 = 9007199254740993/18014398509481984
R1 FAILS: returned integer 1 is strictly farther away than integer 0
```

The last line means the counterexample was successfully reproduced; the
software requirement fails. Wasmtime caching is disabled by the script to
avoid writes to the read-only home directory. No network access is needed.

Optional artifact inspection:

```sh
sha256sum glm-iround.wasm
wasm-tools print glm-iround.wasm
```

## Review and trust boundary

The task-specific files to review are:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 60 | 2162 | Exact definitions, proofs, and axiom reports |
| `Proofs.lean` | 1 | 29 | Imports the proof into the default build |
| `check_counterexample.py` | 55 | 2501 | Byte identification, input decoding, actual execution, exact inequality check |
| `glm-iround.wasm` | binary | 66 | The artifact being refuted |
| `lakefile.toml` | 12 | 264 | Build configuration and Mathlib dependency |
| `lean-toolchain` | 1 | 25 | Lean 4.35.0 selection |
| `lake-manifest.json` | 117 | 3536 | Resolved dependency revisions |
| `README.md` | 11 | 1042 | Requirement and artifact identity |
| `CHECK.md` | 8 | 784 | Reporting requirements |

The remaining trust is in Lean 4.35.0's kernel and its standard foundations,
the installed Mathlib v4.35.0 dependencies and compiled imports, Lake's build
selection, Python's standard library (exact fractions, decimal-to-binary64
conversion, byte packing, file and subprocess operations), and Wasmtime's
decimal argument parsing and WebAssembly execution. `wasm-tools` supplies
validation and disassembly; the falsification itself depends on actual
Wasmtime execution. As with any runtime demonstration, the host tools and
machine must execute correctly. Their full implementations are external
dependencies, not small task-specific models to audit here.

Checked tool versions: Lean 4.35.0, Mathlib v4.35.0, Python 3.14.8,
Wasmtime 50.0.0, wasm-tools 1.262.0. File sizes can be rechecked with
`wc -l -c Proofs/Counterexample.lean Proofs.lean check_counterexample.py
lakefile.toml lean-toolchain lake-manifest.json README.md CHECK.md` and
`wc -c glm-iround.wasm`.
