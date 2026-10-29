# Verification result

**R1 fails.** There is one requirement in README.md. The shipped artifact returns
`1` for the finite binary64 input `0x1.fffffffffffffp-2` (bit pattern
`0x3fdfffffffffffff`, decimal display `0.49999999999999994`). Its exact value is

```text
x = 9007199254740991 / 18014398509481984 = 1/2 - 2^(-54).
```

This satisfies `0 ≤ x ≤ 2147483647`. Integer `0` is strictly closer than the
returned integer `1`:

```text
|x - 0| = 9007199254740991 / 18014398509481984
|x - 1| = 9007199254740993 / 18014398509481984.
```

Thus R1's permission to choose either integer at a tie does not apply.

## Machine-checked results

In [Proofs/Counterexample.lean](Proofs/Counterexample.lean), the exact definitions
are (inside namespace `IRound`):

```lean
def input : ℚ := (1 + (4503599627370495 : ℚ) / 2 ^ 52) / 2 ^ 2

def Nearest (x : ℚ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |x - (n : ℚ)| ≤ |x - (m : ℚ)|
```

All theorem statements in that file are:

```lean
theorem input_exact : input = 9007199254740991 / 18014398509481984

theorem input_in_range : 0 ≤ input ∧ input ≤ 2147483647

theorem zero_strictly_closer : |input - (0 : ℚ)| < |input - (1 : ℚ)|

theorem one_not_nearest : ¬ Nearest input 1

theorem r1_counterexample :
    0 ≤ input ∧ input ≤ 2147483647 ∧ ¬ Nearest input 1
```

These are kernel-checked proofs without `sorry`, added axioms, or native
evaluation. The reported axioms for `IRound.r1_counterexample` are
`[propext, Classical.choice, Quot.sound]`. Rational arithmetic is sufficient:
the input and integer competitors are exact rational numbers, and their
distances and strict comparison are preserved when interpreted as real numbers.

[verify_artifact.py](verify_artifact.py) checks the complementary execution fact:
the actual module returns `i32.const 1` at precisely this input. It also checks
that the encoding is positive, finite, and normal, and decodes it with exact
rational arithmetic to match Lean's `input`.

## Connection to the artifact

The target is the original, unchanged `glm-iround.wasm`, 66 bytes, SHA-256
`eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`.
The checker compares its complete bytes to this literal, as well as checking
the README digest:

```text
0061736d0100000001060160017c017f030201000503010001071302066d
656d6f727902000669726f756e6400000a12011000200044000000000000
e03fa0fc020b
```

The checker validates the artifact with `wasm-tools`, then creates a temporary
WAST script containing `(module $artifact binary "…")` with these actual bytes.
Wasmtime executes an `assert_return` on its exported `iround`, with argument
`(f64.const 0x1.fffffffffffffp-2)` and expected result `(i32.const 1)`.
A separate WAST assertion reinterprets that same input literal as `i64` and
checks its bits are `0x3fdfffffffffffff`. No rebuilt C++ code or replacement
implementation supplies the observed output.

For inspection, `wasm-tools print glm-iround.wasm` shows the function body:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

The failure is caused by rounding during the addition of `0.5`: the exact sum
`1 - 2^(-54)` is halfway between the two adjacent binary64 values below and at
`1`. Ties to even selects `1`, which is then converted to integer `1`.

This deliverable is a concrete execution counterexample plus a formal proof
of its arithmetic violation. It is not a Lean formalization of WebAssembly or
a kernel proof of Wasmtime's execution. A single such counterexample refutes
the universal R1; no claim about all other inputs is needed or made.

## Reproduction

From this directory, with the installed offline dependencies:

```sh
python3 verify_artifact.py
lake build
lake env lean Proofs/Counterexample.lean
```

All three commands must exit with status zero. The Python checker prints three
`PASS` lines, ending with:

```text
PASS: shipped iround(input) = 1; 0 is strictly closer. R1 FAILS.
```

`lake build` reports `Build completed successfully` (job counts and cache
messages may vary). The direct Lean command rechecks the proof source and
prints the axiom list above. Here `PASS` means successful verification of the
counterexample, **not** conformance to R1. Any byte mismatch, validation failure,
wrong execution result, or rejected proof makes the corresponding command fail.

Optional independent inspection:

```sh
sha256sum glm-iround.wasm
wasm-tools print glm-iround.wasm
wasmtime -C cache=n --invoke iround glm-iround.wasm 0.49999999999999994
```

The last command prints `1`; the WAST check is the primary execution evidence
because it avoids decimal argument conversion. Caching is disabled so Wasmtime
does not need to write to a user cache directory.

## Review and trust surface

Review these delivered sources and their correspondence to the statements above:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 37 | 1351 | Exact value, requirement predicate, arithmetic proofs |
| `Proofs.lean` | 1 | 29 | Imports the proof into the Lake build |
| `verify_artifact.py` | 62 | 2558 | Complete byte identity, bit decoding, generated WAST, tool invocation |
| `glm-iround.wasm` | binary | 66 | Original execution target |
| `lakefile.toml` | 12 | 264 | Build and Mathlib dependency configuration |
| `lean-toolchain` | 1 | 25 | Lean version pin |
| `lake-manifest.json` | 117 | 3536 | Offline dependency resolution |

The specifications reviewed are `README.md` (11 lines, 1042 bytes) and `CHECK.md`
(8 lines, 784 bytes). The proof/checking code is 100 lines, 3938 bytes in total.

Trust Lean 4.35.0's kernel and the standard axioms listed above for the formal
arithmetic result. Mathlib v4.35.0 provides definitions and tactics; tactic
output is checked by Lean's kernel. For the artifact execution and linkage,
trust Python 3's byte/file handling, integer/rational arithmetic and subprocess
handling, Wasmtime 50.0.0's WAST parser and WebAssembly execution, and
wasm-tools 1.262.0's validation/printing. Also trust the installed toolchain,
operating system, and hardware. The script and the small definitions are the
application-specific review surface; the installed checking tools are external
trusted infrastructure. The original C++ source, GLM headers, and compiler used
by `build.sh` are not needed to establish this counterexample.
