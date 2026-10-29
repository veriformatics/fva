**R1 fails.** The shipped `glm-iround.wasm` returns `1` for the finite binary64
input with bits `0x3fdfffffffffffff`:

```text
x = 0x1.fffffffffffffp-2
  = 9007199254740991 / 18014398509481984
  = 0.499999999999999944488848768742172978818416595458984375
```

This input satisfies `0 ≤ x ≤ 2147483647`. The distances to integers `0` and `1`
are respectively `9007199254740991/18014398509481984` and
`9007199254740993/18014398509481984`. Thus `0` is strictly closer than the
returned `1`; R1's permission for halfway cases does not apply. R1 is the only
requirement listed in README.md.

The exact machine-checked statements and all three project definitions they
use are in [Proofs/Counterexample.lean](Proofs/Counterexample.lean):

```lean
namespace Verification

def bits : Nat := 0x3fdfffffffffffff
def p : Nat := 9007199254740991
def q : Nat := 18014398509481984

theorem binary64_encoding :
    bits / 2^63 = 0 ∧ (bits / 2^52) % 2048 = 1021 ∧
    2^52 + bits % 2^52 = p ∧ 2^(1023 + 52 - 1021) = q := by
  decide +kernel

theorem counterexample_arithmetic :
    0 < p ∧ p < q ∧ p ≤ 2147483647 * q ∧ p < q - p := by
  decide +kernel

end Verification
```

The first theorem checks the binary64 fields: sign zero, normal finite exponent
1021, significand `p`, and denominator `q = 2^(1023+52-1021)`. By the IEEE binary64
interpretation, the input is exactly `p/q`. The second theorem checks the domain
and the strict comparison of distances after multiplying by positive `q`.
Because `p < q`, natural subtraction `q - p` is the exact positive distance
numerator. A strictly closer competing integer suffices to refute R1.

**Artifact connection.** [verify.py](verify.py) compares the entire module with
an embedded 66-byte literal before executing it. Its SHA-256 is
`eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`, matching
README.md. [counterexample.wat](counterexample.wat) imports `iround` from that
actual module, reinterprets the exact integer bit pattern as `f64`, and calls
the export. Wasmtime loads the shipped file through `--preload`; the harness
contains no rounding implementation. The script checks the harness text against
the witness constant read from the Lean file, independently decodes the bits
using Python's exact `Fraction.from_float`, and requires the observed result `1`.
No decimal argument conversion is involved in the artifact call.

The disassembly saved by the check has this function body:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

This explains the failure: the exact sum `x + 0.5 = 1 - 2^-54` is halfway
between adjacent binary64 values and rounds to `1` under ties-to-even; truncation
then returns `1`. The failure result is established by execution, independently
of this explanation. Neither the C++ source, GLM headers, nor shipped module was
rewritten or rebuilt.

**Run every check, offline, from this directory:**

```sh
./check.sh
```

Exit status zero and the final line below mean the verification experiment
succeeded, including demonstrating that R1 fails:

```text
PASS: R1 counterexample reproduced; fresh proofs accepted by 3 kernels; both false proofs rejected by all 3. Logs: .verification/
```

The command compiles the proof source afresh into `.verification/olean`, exports
only the two results and their transitive dependencies, rejects any exported
axiom, and replays the same certificate through Lean's C++ kernel
(`leanchecker --from-export`), Lean4Lean (`lean4lean --import`), and the Rust
Con-Ron kernel (`con-ron --verified --jobs=2`). It uses the executables in the
installed Lean prefix. These are distinct kernel implementations; the initial
Lean elaboration alone is not counted as independent checking. Proofs use
kernel reduction, with no native computation axiom or admitted proof.

For each kernel, the command also accepts a freshly compiled control proof of
`(0 : Nat) = 0`. It then retains that proof term but changes its claimed type
to `False`, and separately to `(0 : Nat) = 1`, in the exported certificates.
All three kernels must return exactly exit status `1` and diagnose a type
mismatch at `KernelControl.reflexivity` for both forgeries. An arbitrary
nonzero exit is insufficient. These controls bypass elaboration and exercise
the same replay commands as the actual proofs. The certificates, disassembly,
execution output, and all checker diagnostics remain in `.verification/`.

**Review and trust size.** The project-specific formal statements and their
definitions occupy 8 physical lines; the whole proof file, including proofs,
comments, and spacing, is 18 lines / 567 bytes. They use standard natural
number arithmetic and conjunction, avoiding an implementation model or a
custom floating-point library. The complete exported proof dependency closure
is 207 declaration records: 132 definitions, 47 theorems, and 28 inductive
blocks, with zero axioms. This includes standard library definitions and
proof machinery, not just the project declarations. The replay input is
7,738 JSON lines / 421,717 bytes; `.verification/dependency-declarations.txt`
lists all definitions, theorems, inductive types, constructors, and recursors.
The kernel checks the proof terms; the interpretation of standard `Nat`
operations and IEEE binary64 remains part of the mathematical review.

| Project file to review | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 18 | 567 | Complete formal certificate |
| `Proofs.lean` | 1 | 29 | Library root import |
| `counterexample.wat` | 6 | 201 | Exact input and call to shipped export |
| `verify.py` | 176 | 8,228 | Artifact binding, execution, fresh compilation, replay, controls |
| `check.sh` | 4 | 97 | Lake environment and single command entry point |

The total above is 205 lines / 9,122 bytes, including proofs and automation.
The existing Lake configuration selects Lean 4.35.0 and the installed packages;
the certificate needs only Lean's core library, although the project retains
its Mathlib dependency. The execution demonstration trusts Wasmtime, the
wasm-tools harness assembler, Python and its standard library, and the
OS/hardware. Proof replay additionally trusts the exporter to convey the
reviewed statements and the independent kernels' implementations. Tested tool
versions were Lean 4.35.0, Wasmtime 50.0.0, and wasm-tools 1.262.0.

This result is a concrete execution counterexample supported by kernel-checked
encoding and arithmetic. It does not claim a mechanized proof of Wasmtime's
WebAssembly semantics or a universal characterization of all inputs. Those
are unnecessary to demonstrate this failure, but the execution-engine trust
boundary is explicit. No C++ compiler or GLM source-to-binary correspondence
is needed for the result about the shipped artifact.
