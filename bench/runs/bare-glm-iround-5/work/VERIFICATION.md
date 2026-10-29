# Verification result

**R1 is false for the shipped artifact.** The actual module returns `1` for the
finite binary64 input with bits `0x3fdfffffffffffff`, namely

```text
x = 0x1.fffffffffffffp-2
  = 9007199254740991 / 18014398509481984
  = 1/2 - 2^-54
  ≈ 0.49999999999999994.
```

This input satisfies `0 ≤ x ≤ 2147483647`. Its distance to `0` is
`1/2 - 2^-54`, while its distance to the returned integer `1` is
`1/2 + 2^-54`. Thus `1` is strictly worse than `0`; R1's allowance for ties
does not apply. R1 is the README's only requirement.

## Machine-checked results

`Proofs/Counterexample.lean` contains the following exact definitions and theorem
statements, all in namespace `Counterexample`. Proof bodies are in that file.
`ℚ` is used for exact values and distances, without floating-point approximation;
ordering these rational distances also orders their real values.

```lean
def inputBits : ℕ := 0x3fdfffffffffffff
def input : ℚ := 1 / 2 - 1 / 2 ^ 54
def Nearest (x : ℚ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |x - (n : ℚ)| ≤ |x - (m : ℚ)|

theorem input_fields :
    inputBits / 2 ^ 63 = 0 ∧
    inputBits / 2 ^ 52 % 2048 = 1021 ∧
    inputBits % 2 ^ 52 = 2 ^ 52 - 1

theorem input_is_normal :
    0 < inputBits / 2 ^ 52 % 2048 ∧
    inputBits / 2 ^ 52 % 2048 < 2047

theorem input_decoding :
    input =
      (1 + ((inputBits % 2 ^ 52 : ℕ) : ℚ) / 2 ^ 52) *
        (2 : ℚ) ^ (((inputBits / 2 ^ 52 % 2048 : ℕ) : ℤ) - 1023)

theorem input_in_range : 0 ≤ input ∧ input ≤ 2147483647

theorem zero_strictly_closer : |input - (0 : ℚ)| < |input - (1 : ℚ)|

theorem one_not_nearest : ¬ Nearest input 1

theorem r1_counterexample :
    (0 ≤ input ∧ input ≤ 2147483647) ∧ ¬ Nearest input 1
```

`Nearest` accepts either integer in a tie by using a non-strict inequality.
`one_not_nearest` disproves this predicate by choosing integer `0` as a strictly
better candidate. `input_fields`, `input_is_normal`, and `input_decoding` connect
the rational input to the finite positive normal binary64 encoding used by the
execution harness.

The separately checked execution result is:

```text
iround(f64.reinterpret_i64(0x3fdfffffffffffff)) = i32 1
```

This is an execution-based counterexample to the artifact's universal R1 claim,
supported by kernel-checked arithmetic. The execution result is not introduced
as a Lean axiom, and this report does not claim a Lean proof of Wasmtime or of
a general WebAssembly interpreter.

## Connection to the shipped bytes

The subject is the original, unchanged `glm-iround.wasm`: exactly 66 bytes,
SHA-256 `eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`.
`verify.py` compares the entire binary against a literal copy of all 66 bytes
as well as checking its hash. It writes those verified bytes into a temporary
snapshot and preloads that snapshot as module `shipped` in Wasmtime.

`witness.wat` imports `shipped.iround`; it constructs the input using an integer
constant followed by `f64.reinterpret_i64` and calls that import. Thus the test
uses exact bits and does not depend on decimal argument parsing. It does not
reimplement the target function. The script checks successful execution and
that the returned output is exactly `1`.

For inspection, `wasm-tools print glm-iround.wasm` shows the function body:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

The failure is explained by binary64 rounding of the addition: the exact sum
`x + 1/2 = 1 - 2^-54` is halfway between `1 - 2^-53` and `1`, and ties-to-even
rounds it to `1`. Truncating that value returns `1`. This explanation is not a
separate formal floating-point semantics proof; the actual result is checked
by executing the original bytes. Neither rebuilding the C++ source nor trusting
`build.sh` or the GLM headers is needed for the counterexample.

## Reproduction

From this directory, with the provided offline tools and built Mathlib:

```sh
python3 verify.py
lake build
```

The first command validates both WebAssembly modules with `wasm-tools`, executes
the harness with Wasmtime's cache disabled, independently checks the exact
rational arithmetic in Python, and directly elaborates
`Proofs/Counterexample.lean` with `lake env lean`. Any failed check or subprocess
exits nonzero. Success includes these lines:

```text
PASS: exact 66 artifact bytes; sha256 eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
PASS: actual artifact returns i32 1 for f64 bits 0x3fdfffffffffffff
PASS: exact x = 9007199254740991/18014398509481984; distance to 0 < distance to 1
PASS: Lean checked the certificate; R1 is FALSE
```

It also prints the axiom dependencies of `r1_counterexample` and
`input_decoding`: `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom
axiom, or native evaluation oracle is used. The second command checks the Lake
library entry point and ends with `Build completed successfully`.

Versions used: Lean 4.35.0, Mathlib v4.35.0, Wasmtime 50.0.0, and wasm-tools
1.262.0. No network or C++ compiler is required.

## Review and trust

The local review surface, excluding this report, is:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 54 | 1789 | Definitions, binary64 decoding formula, exact arithmetic proofs |
| `Proofs.lean` | 1 | 29 | Imports the proof module |
| `witness.wat` | 7 | 265 | Supplies the exact input to the imported artifact |
| `verify.py` | 62 | 2859 | Pins bytes, runs tools, checks execution, invokes Lean |
| `glm-iround.wasm` | binary | 66 | Original subject; complete contents pinned in the script |
| `lakefile.toml` | 12 | 264 | Project and dependency configuration |
| `lean-toolchain` | 1 | 25 | Lean version selection |
| `lake-manifest.json` | 117 | 3536 | Dependency resolution |

A reviewer must check that the binary64 field interpretation and `Nearest`
definition express the README's intended mathematics, and that the harness and
script connect the same input and output to the pinned artifact. The rational
decoding is an explicit mathematical interpretation of this one normal finite
input, not a model of all WebAssembly instructions.

The external trusted infrastructure comprises Lean's kernel and standard axioms
listed above, the meanings of the imported Mathlib rational/integer definitions,
the provided Lean/Mathlib installation and build machinery, Python and its
standard library, wasm-tools' parser/validator, Wasmtime's linker/execution and
result printing, and the host system. These are external tool distributions,
not additional project proof files; their implementations are not verified here.
Mathlib tactics produce kernel-checked proofs. Wasmtime's faithful execution of
the pinned module is a trust assumption of the concrete counterexample. No
unproved universal compliance claim remains: R1 is refuted by the witness above.
