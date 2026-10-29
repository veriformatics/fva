R1 is **false** for the shipped `glm-iround.wasm`. There are no other numbered requirements in README.md.

The counterexample input is the finite binary64 value with bits `0x3fdfffffffffffff`:

```text
x = 9007199254740991 / 18014398509481984 = 1/2 - 2^-54
iround(x) = 1                         (execution of the shipped artifact)
distance to 0 = 9007199254740991 / 18014398509481984
distance to 1 = 9007199254740993 / 18014398509481984
```

It satisfies `0 ≤ x ≤ 2147483647`. Integer 0 is strictly closer than the returned integer 1, so the allowance for halfway cases does not apply.

The mathematical part is checked by Lean 4.35.0 with Mathlib v4.35.0 in `Proofs/Counterexample.lean`, imported by `Proofs.lean`. These are the exact definitions and theorem statements, with proof bodies omitted below. All names are in namespace `IRound`.

```lean
noncomputable def x : ℝ := 9007199254740991 / 18014398509481984

def IsNearest (v : ℝ) (n : ℤ) : Prop :=
  ∀ m : ℤ, |v - (n : ℝ)| ≤ |v - (m : ℝ)|

theorem input_fields :
    (0x3fdfffffffffffff : ℕ) / 2^63 = 0 ∧
    ((0x3fdfffffffffffff : ℕ) / 2^52) % 2^11 = 1021 ∧
    (0x3fdfffffffffffff : ℕ) % 2^52 = 4503599627370495

theorem input_value :
    (1 + (4503599627370495 : ℝ) / 2^52) / 4 = x

theorem input_in_R1_domain : 0 ≤ x ∧ x ≤ (2147483647 : ℝ)

theorem zero_strictly_closer_than_one :
    |x - (0 : ℝ)| < |x - (1 : ℝ)|

theorem one_is_not_nearest : ¬ IsNearest x 1

theorem R1_counterexample :
    0 ≤ x ∧ x ≤ (2147483647 : ℝ) ∧ ¬ IsNearest x 1
```

`IsNearest` compares with every mathematical integer and accepts ties. The last theorem establishes the domain bounds and that the observed output is unacceptable. `input_fields` and `input_value` establish the arithmetic used to interpret the chosen binary64 representation. Under IEEE-754 binary64 decoding, sign 0, biased exponent 1021, and fraction `2^52 - 1` give the finite normal value `(1 + (2^52 - 1)/2^52) * 2^-2`.

The artifact connection is an execution demonstration, not a Lean formalization of the WebAssembly interpreter. `check_counterexample.py` checks all 66 bytes against an embedded byte string, checks SHA-256, validates the module, and uses Wasmtime to call its actual `iround` export. The expected SHA-256 is:

```text
eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
```

`counterexample.wat` imports `artifact.iround`. Its `observed` function constructs the exact input with `i64.const 0x3fdfffffffffffff; f64.reinterpret_i64` and calls that import directly. Wasmtime's `--preload artifact=glm-iround.wasm` binds the import to the shipped module. There is no decimal parsing of the input and no replacement implementation. The script requires the returned value to be exactly `1` and independently checks the input bounds and strict distance comparison using Python's exact rational arithmetic.

For context, `wasm-tools print glm-iround.wasm` shows the function body:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

Binary64 addition rounds the exact sum `1 - 2^-54` to `1`, which truncates to `1`. This explains the observed failure; the evidence does not depend on rebuilding C++ or on the correctness of the compiler, GLM headers, or build.sh. The artifact is left unchanged.

From this directory, run these commands without network access:

```sh
lake build
python3 check_counterexample.py
```

Success requires both commands to exit with status 0. Lake reports `Build completed successfully` (possibly without rebuilding cached targets). The replay prints:

```text
Artifact: 66 bytes, SHA-256 eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
Input: 0x3fdfffffffffffff = 9007199254740991/18014398509481984
Observed iround result: 1; integer 0 is strictly closer.
PASS: R1 is FALSE for the shipped artifact.
```

Here PASS means successful reproduction of a requirement violation. Missing tools, different artifact bytes, an unexpected return value, or a failed arithmetic check cause a nonzero exit. Wasmtime caching is disabled to avoid writing outside the workspace.

The theorem axioms can additionally be inspected after building:

```sh
lake env lean --stdin <<'LEAN'
import Proofs
#print axioms IRound.input_fields
#print axioms IRound.input_value
#print axioms IRound.input_in_R1_domain
#print axioms IRound.zero_strictly_closer_than_one
#print axioms IRound.one_is_not_nearest
#print axioms IRound.R1_counterexample
LEAN
```

The project adds no axioms, `sorry`, or native evaluation shortcuts. The arithmetic proofs use `norm_num` to produce proof terms checked by Lean. The expected axiom reports contain only standard Lean axioms (`propext`, `Classical.choice`, and `Quot.sound`), or no axioms.

The project-specific material a reviewer must read to assess the claims and the connection between execution and mathematics is:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 42 | 1446 | Real-valued specification, bit-field arithmetic, and proofs |
| `Proofs.lean` | 1 | 29 | Library root importing the proofs |
| `counterexample.wat` | 7 | 272 | Exact input construction and direct artifact call |
| `check_counterexample.py` | 54 | 2121 | Exact artifact identity, execution, and rational checks |

This is 104 lines / 3868 bytes of definitions, proofs, harness, and checker. The binary under test is 66 bytes. Project configuration is `lakefile.toml` (12 lines / 264 bytes), `lean-toolchain` (1 line / 25 bytes), and `lake-manifest.json` (117 lines / 3536 bytes). Sizes can be checked with `wc -l -c`.

External trusted infrastructure is the installed Lean kernel and imported Lean/Mathlib definitions and compiled libraries, Lake's build machinery, Python 3 and its standard library, and Wasmtime's WAT parser, linker, and execution engine implementing WebAssembly/IEEE-754 semantics. `wasm-tools` supplies the binary validity check and optional disassembly. Tested versions are Lean 4.35.0, Mathlib v4.35.0, Wasmtime 50.0.0, and wasm-tools 1.262.0. These installed dependencies were not audited or reverified here. In particular, the artifact-to-return-value claim relies on Wasmtime, while the exact mathematical violation is proved in Lean; no complete formal semantics of floating-point addition or WebAssembly is claimed.
