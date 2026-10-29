# Verification result

**R1 fails for the shipped `glm-iround.wasm`.** There are no other numbered
requirements in `README.md`.

The counterexample is the finite, positive, normal binary64 value with bits
`0x3fdfffffffffffff`:

```text
x = 9007199254740991 / 18014398509481984
  = 1/2 - 2^(-54)
  = 0.499999999999999944488848768742172978818416595458984375
```

The artifact returns the signed integer **1**. The integer **0** is strictly
closer: its distance is `x`, while the distance to 1 is `1 - x`. This input is
within `0 ≤ x ≤ 2147483647`, and is not a halfway case. Thus accepting either
integer at ties does not excuse the failure.

## Machine-checked statements

All four theorems are in `Proofs/Counterexample.lean`, in namespace
`Verification`. These are their exact statements (with proof bodies omitted):

```lean
def witnessBits : ℕ := 0x3fdfffffffffffff

noncomputable def witness : ℝ :=
  (9007199254740991 : ℝ) / 18014398509481984

def IsNearest (x : ℝ) (r : ℤ) : Prop :=
  ∀ n : ℤ, |x - (r : ℝ)| ≤ |x - (n : ℝ)|

theorem witness_fields :
    witnessBits / 2^63 = 0 ∧
    (witnessBits / 2^52) % 2^11 = 1021 ∧
    witnessBits % 2^52 = 4503599627370495

theorem witness_decode :
    witness = (1 + (4503599627370495 : ℝ) / 2^52) / 2^2

theorem witness_below_half :
    witness = (1 : ℝ) / 2 - 1 / 2^54

theorem r1_counterexample :
    0 ≤ witness ∧ witness ≤ 2147483647 ∧
    |witness - (0 : ℝ)| < |witness - (1 : ℝ)| ∧
    ¬ IsNearest witness 1
```

`IsNearest` uses a non-strict comparison, so it permits both answers at a tie.
`witness_fields` identifies sign 0, biased exponent 1021, and fraction
4503599627370495. The standard binary64 interpretation of these normal fields
is `(1 + fraction / 2^52) * 2^(1021 - 1023)`, exactly the expression in
`witness_decode`. This establishes that the runtime input corresponds to the
real number in `r1_counterexample`.

The second machine-checked result is the executable counterexample:
`check_counterexample.py` checks the artifact's exact bytes, validates it, and
executes `counterexample.wat` linked to its `iround` export. It requires the
result to be exactly 1. The wrapper takes no arguments: it constructs the input
with `i64.const 0x3fdfffffffffffff; f64.reinterpret_i64`, avoiding decimal input
parsing. The script also independently checks the input's exact rational value,
domain, and strict distance comparison with Python's `Fraction`.

## Connection to the shipped artifact

The tested artifact is the original 66-byte file, SHA-256:

```text
eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
```

Its complete bytes, also pinned in the replay script, are:

```text
0061736d0100000001060160017c017f030201000503010001071302066d656d
6f727902000669726f756e6400000a12011000200044000000000000e03fa0fc020b
```

`wasm-tools print glm-iround.wasm` shows that the exported function executes:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

The exact sum before binary64 rounding is `1 - 2^(-54)`, the midpoint between
`1 - 2^(-53)` and `1`. Round-to-nearest, ties-to-even produces 1, and the integer
conversion returns 1. The runtime replay confirms the result directly on the
shipped bytes; it does not depend on rebuilding the C++ source or trusting its
compiler. The artifact and original source have not been modified.

The Lean theorems certify the mathematical counterexample. They do **not**
formalize a WebAssembly interpreter or prove Wasmtime correct. The connection
from artifact bytes to observed return value is an execution demonstration,
which is sufficient to refute R1 when combined with the proved distance
comparison. There is no claim of a universal correctness proof.

## Reproduction

Run these commands from this directory, without network access:

```sh
lake build
lake env lean Proofs/Counterexample.lean
python3 check_counterexample.py
```

All three must exit with status 0. `lake build` must report
`Build completed successfully`. The direct Lean invocation rechecks the proof
source and prints these axiom dependencies:

```text
'Verification.witness_fields' depends on axioms: [propext]
'Verification.witness_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verification.witness_below_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verification.r1_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There must be no `sorryAx` and no errors. The replay script must print:

```text
PASS: exact artifact (66 bytes), sha256 eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
PASS: input bits 0x3fdfffffffffffff, exact value 9007199254740991/18014398509481984
PASS: shipped iround returns 1; integer 0 is strictly closer. R1 FAILS.
```

Here `PASS` means the counterexample was successfully verified; the requirement
itself fails. The script disables Wasmtime's compilation cache, so it does not
need to write to the user's home directory. For manual inspection and replay:

```sh
wasm-tools print glm-iround.wasm
wasmtime run -C cache=n --preload artifact=glm-iround.wasm --invoke counterexample counterexample.wat
```

The last command must print `1` (Wasmtime may additionally emit invocation
warnings on stderr).

## Review and trust boundary

Local material to review, with sizes in lines and bytes:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 46 | 1538 | Definitions, exact field/rational equalities, domain and failure proof |
| `Proofs.lean` | 2 | 78 | Imports the proof into the default Lake target |
| `counterexample.wat` | 7 | 269 | Links the shipped export and supplies the exact input bits |
| `check_counterexample.py` | 54 | 2068 | Pins all bytes and digest, validates, runs, checks output and exact distances |
| `lakefile.toml` | 12 | 264 | Library target and Mathlib v4.35.0 dependency |
| `lean-toolchain` | 1 | 25 | Lean v4.35.0 selection |
| `lake-manifest.json` | 117 | 3536 | Installed dependency revisions |
| `glm-iround.wasm` | binary | 66 | The artifact under test, fully pinned above |

The proof relies on Lean 4.35.0's kernel, the displayed standard logical axioms,
and Mathlib's real numbers, integer casts, absolute value, and order definitions
matching the mathematical reading above. Tactics produce kernel-checked proof
terms; there are no added axioms, admitted proofs, or `native_decide` calls.
The reviewer must check that `IsNearest` and the field interpretation express
the README requirement for this particular input.

The execution evidence additionally trusts Python and its standard library
(`Fraction`, `struct`, hashing, file and subprocess operations), wasm-tools'
WAT encoding/module validation, and Wasmtime's module linking, binary64
reinterpretation, and execution on the host. Tested versions: Lean 4.35.0,
Mathlib v4.35.0, Python 3.14.8, wasm-tools 1.262.0, Wasmtime 50.0.0. The C++
headers, `iround.cpp`, and `build.sh` are background provenance, not premises
of this counterexample. No external service or downloaded data is used.
