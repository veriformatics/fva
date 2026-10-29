# Verification result

R1 is **false** for the shipped `glm-iround.wasm`.

The input is the finite, positive binary64 value with bits
`0x3fdfffffffffffff`, written exactly as `0x1.fffffffffffffp-2`:

```
x = 9007199254740991 / 18014398509481984
  = 0.499999999999999944488848768742172978818416595458984375
```

It satisfies `0 ≤ x ≤ 2147483647`. The artifact returns `1`, but `0` is
strictly closer: their respective distances, multiplied by `2^54`, are
`9007199254740993` and `9007199254740991`. This is not a tie.

## Exact machine-checked statement

In `Proofs/Counterexample.lean`, namespace `Iround`, the complete application
definitions and theorem statement are:

```lean
def numerator : Int := 9007199254740991
def denominator : Int := 18014398509481984
def inDomain : Prop :=
  0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator
def nearest (result : Int) : Prop :=
  ∀ candidate : Int,
    (numerator - result * denominator).natAbs ≤
    (numerator - candidate * denominator).natAbs
theorem r1_counterexample : 0 < denominator ∧ inDomain ∧ ¬ nearest 1
```

For positive `denominator`, this definition of `nearest` is exactly the
nearest-integer distance condition for `numerator / denominator`, including
acceptance of ties. The proof uses candidate `0` to refute nearestness of `1`.
There are no axioms, `sorry`, native evaluation certificates, or additional
assumptions. Only `Init` is imported; Mathlib is not needed for this witness.

## Connection to the shipped implementation

`check.py` requires the entire artifact to be 66 bytes with SHA-256
`eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`,
matching README. It validates and disassembles those bytes. The function body is
`local.get 0; f64.const 0.5; f64.add; i32.trunc_sat_f64_s`.

`witness.wat` imports that actual module's `iround` export. Its zero-argument
`witness` function pushes the exact hexadecimal f64 constant and calls the
import. No decimal command-line float parsing is involved. The script checks
the generated constant's eight bytes, verifies that their decoded exact
integer ratio equals the numerator and denominator read from the Lean file,
checks the finite positive normal encoding, and requires Wasmtime's result
to be `1`. The harness text is also checked against its expected five lines.

This is an execution counterexample plus an exact mathematical proof, not a
formalization of general WebAssembly or floating-point semantics. The artifact
execution is trusted through Wasmtime. There is no handwritten replacement
implementation and no claim of a kernel proof of Wasmtime's execution.
The original source, headers, build script, and artifact are unchanged; the C++
compiler and correspondence to GLM source are not needed for this result.

## Reproduce everything offline

From this directory, run:

```sh
python3 check.py
```

The command forces Lean to elaborate the proof source, exports the theorem and
its transitive dependencies, rejects any export containing an axiom record,
and replays the same export through three kernels: Lean's default kernel
(`leanchecker --from-export`), Nanoda, and Con-ron (`--verified`). The latter two
are independent Rust implementations, not invocations of Lean's default kernel.
The tools are found under `lean --print-prefix`/`bin`; all are already installed.

Each kernel must accept the proof and reject two forged exports that replace
the final theorem's proposition with `False` and `(0 : Nat) = 1`, retaining
its original proof term. These are well-formed exports with invalid proofs.
The command checks specific type-checking diagnostics and exit codes, rather
than counting missing tools, malformed input, or unsupported features as
successful rejection. Nanoda signals these type mismatches with a checked
`self.def_eq` assertion and exit 101. On the valid proof it reports no
typechecker errors; its separate `Unable to print axioms` pretty-printer warning
does not indicate a proof failure.

Success is exit status zero, nine ACCEPT/REJECT verdicts (one acceptance and
two rejections per kernel), and the final line:

```
PASS: R1 is false; artifact witness, three kernel replays, and rejection controls checked
```

The run leaves the disassembly, proof export, forged exports, and checker logs
under `.verification/`. It requires Python 3, Lake/Lean 4.35.0, wasm-tools,
Wasmtime, leanexport, leanchecker, nanoda_bin, and con-ron. No downloads or
recompilation of the artifact occur.

## Human review and trust size

The application-specific mathematical review surface is **9 nonblank lines,
406 UTF-8 bytes**, counting the four definitions and theorem header as written
in the Lean source, including the header's `:= by`. The entire proof file is
27 lines / 838 bytes. The kernel checks the proof body, so it need not be
trusted as an argument.

The artifact-to-statement bridge and checking orchestration must also be read:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexample.lean` | 27 | 838 | Definitions, statement, proof, axiom report |
| `Proofs.lean` | 1 | 29 | Library import |
| `witness.wat` | 5 | 173 | Calls the shipped export on the exact input |
| `check.py` | 148 | 6711 | Artifact pin, execution, input bridge, replay, controls |
| **Total custom executable material** | **181** | **7751** | Includes proof body |

The exported dependency closure is 5,153 JSON lines / 324,932 bytes, containing
116 definitions, 25 inductive blocks, and 23 theorem records, with zero axiom
records. It is replayed, not manually assumed correct. Standard Lean logic,
integer arithmetic, inductive semantics, and the kernels' implementations
remain foundational dependencies; their source sizes are not included in the
custom-material count. Also trusted are the OS/tool execution, Python's byte
and integer-ratio operations, SHA-256 identity check, Lean's export extraction,
wasm-tools' assembly/validation, and Wasmtime's execution. Independent proof
replay and false-proof controls reduce checker dependence but do not formally
verify this infrastructure. The existing Lake configuration and toolchain
files select the installed offline environment.
