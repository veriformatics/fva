R1 is **false**. The shipped module returns `1` for the finite, positive binary64 input
`0x1.fffffffffffffp-2` (bits `0x3fdfffffffffffff`), whose exact value is
`9007199254740991 / 18014398509481984 = 1/2 - 2^-54`.
The unique nearest integer is `0`: its distance is `9007199254740991 / 2^54`,
whereas the distance to `1` is `9007199254740993 / 2^54`.
This input is inside R1's interval, and the distances are strictly different,
so the permission to choose either integer at a tie does not apply.
R1 is the only numbered requirement in README.md.

Run everything from this directory with:

```sh
./check.sh
```

Success is exit status zero and the final line:

```text
PASS: R1 is REFUTED; arithmetic proofs replayed; false-proof controls rejected.
```

This means verification successfully reproduced a specification violation;
it does not mean the software satisfies R1. No network or rebuild of the
implementation is needed. Required tools are Python 3, Lake/Lean 4.35.0,
`wasm-tools`, `wasmtime` with Cranelift and Winch, and the installed
`leanexport`, `leanchecker-paranoid`, and `nanoda_bin` in Lean's `bin` directory.
The runs here used wasm-tools 1.262.0, Wasmtime 50.0.0, lean4export 3.1.0,
and Nanoda 0.4.19.

The exact formal statements are in [Proofs/Counterexample.lean](Proofs/Counterexample.lean).
They use scaled integer distances to avoid a rational-number library:
for positive `d`, minimizing `|n - d*r|` is exactly minimizing `|n/d - r|`,
because the latter distance is the former divided by the same positive `d`.
`Int.natAbs` is the nonnegative absolute value of an integer. All definitions
introduced for the statements, followed by the three theorem statements, are:

```lean
def numerator : Int := 9007199254740991
def denominator : Int := 18014398509481984
def nearest (n d r : Int) : Prop :=
  ∀ z : Int, (n - d * r).natAbs ≤ (n - d * z).natAbs

theorem input_encoding :
    (0x3fdfffffffffffff : Nat) = 1021 * 2^52 + 4503599627370495 ∧
    numerator = 2^52 + 4503599627370495 ∧ denominator = 2^54

theorem r1_counterexample :
    0 < denominator ∧ 0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator ∧
    ¬ nearest numerator denominator 1

theorem strictly_closer :
    (numerator - denominator * 0).natAbs < (numerator - denominator * 1).natAbs
```

`input_encoding` certifies the bit decomposition and the corresponding integer
numerator and denominator. Under the standard IEEE binary64 encoding, the sign
is zero, the exponent field is 1021, and the fraction field is 4503599627370495.
Thus the represented value is `(2^52 + fraction) * 2^(1021-1023-52)`.
`r1_counterexample` certifies the domain conditions and that the observed return
value fails the nearest-integer predicate. `strictly_closer` gives the explicit
strict comparison with `0`. These are closed theorems, with no hypotheses about
program behavior. Their proof terms have **no axioms**, including no `sorryAx`,
`Classical.choice`, or `Lean.trustCompiler`.

The implementation evidence is direct execution of the original artifact,
not execution of a handwritten implementation model. The check pins its length
to 66 bytes and its SHA-256 to
`eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`,
the hash in README.md. `wasm-tools validate` checks the module, and its printed
instructions are saved as `.verification/artifact.wat`. The body is:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

[verification/call.wat](verification/call.wat) imports `iround` from that same
module. It creates the input by `i64.const 0x3fdfffffffffffff` followed by
`f64.reinterpret_i64`, then calls the import. There is no decimal-input parser
in this path. Both Cranelift and Winch executions return the `i32` value `1`.
The implementation, headers, build script, and shipped Wasm are unchanged.
The explanation is that the exact sum with `0.5` is `1 - 2^-54`, halfway between
the two adjacent binary64 values below/at `1`; ties-to-even addition produces
`1.0`, which converts to `1`.

The execution result is runtime evidence, **not a Lean proof of WebAssembly
operational semantics**. The formal proofs certify the input arithmetic and
specification violation for the observed result. Their connection to the
artifact requires trusting the binary64 encoding, the import harness, and
Wasmtime's execution of these instructions. Two compiler backends provide
additional execution checks but share Wasmtime infrastructure. No claim is
made about all other inputs or about the C++ compilation provenance.

[verification/check.py](verification/check.py) compiles the proof source afresh,
exports only the three theorem roots and their dependencies, and replays the
same export using two distinct kernels:

- Lean 4.35's C++ kernel through `leanchecker-paranoid --from-export`.
- Nanoda's independently implemented Rust kernel through `nanoda_bin`, with
  an empty axiom allowlist and rejection of unpermitted axioms.

The ordinary Lean compilation and the C++ replay are not counted as two
independent kernel implementations. Nanoda also prints the definitions and
theorem statements into `.verification/positive-nanoda.log`, ending with
`Checked 319 declarations with no errors`. The Lean replay log says
`Lean default kernel accepts the solution`.

The check then creates two well-formed forged exports. In one it replaces the
declared type of `r1_counterexample` with `False`; in the other it does so for
`strictly_closer`. Both retain the original proof terms and dependencies.
Both kernels must reject both exports. The script requires the actual type
error diagnostics: Lean's `declaration type mismatch` and Nanoda's failed
definitional-equality assertion in its type checker. A missing tool, parse
error, or unrelated failure cannot pass these controls. This demonstrates
rejection of false certificates; it is not a proof that either kernel has no bugs.
All exports and execution/checker logs are regenerated under `.verification/`.

The review surface and its size are:

| File or dependency | Size | What to review or trust |
| --- | ---: | --- |
| `Proofs/Counterexample.lean` | 24 lines, 919 bytes | 3 definitions and 3 theorem statements occupy 12 nonblank lines; the remaining lines contain imports, namespace, and checked proofs. |
| `verification/call.wat` | 6 lines, 202 bytes | The bit-exact input and direct call to the artifact import. |
| `verification/check.py` | 105 lines, 5018 bytes | Artifact pinning, commands, export-root/axiom checks, and positive/negative acceptance conditions. |
| `verification/nanoda.json` | 10 lines, 394 bytes | Kernel extensions, empty axiom allowlist, and printed declarations. |
| `check.sh` | 4 lines, 100 bytes | The single check entry point. |

These files total **149 lines / 6633 bytes**, including proof code and comments.
The 12-line statement/definition count excludes standard Lean definitions;
it does not count those as free. The complete sliced dependency export is
**481076 bytes / 8807 JSON lines**, containing 165 definitions, 60 theorems,
30 inductive blocks, no opaque declarations, and no axioms. Expanding the
inductive blocks gives the 319 kernel declarations checked by Nanoda. This is
a conservative bound on the dependency review surface, including proof-only
dependencies. The semantic foundations include Lean's standard `Nat`, `Int`,
arithmetic, order, absolute value, and logical connectives, imported through
`Init.Data.Int.Basic`; their definitions and the kernels' primitive natural
arithmetic must carry their usual meanings. Mathlib is not used by the proofs.

Other trusted plumbing is the Lean parser/elaborator and exporter preserving
the displayed statements, the independent kernel executables, Python and its
hash/subprocess libraries, `wasm-tools`, Wasmtime, and the host environment.
The generated JSON is replayed rather than trusted as a proof, and its absence
of axioms is checked both by the driver and Nanoda. [Proofs.lean](Proofs.lean)
is a one-line, 29-byte library import scaffold; it is not used to replace the
fresh compilation in `check.sh`. README.md supplies the requirement being
interpreted, and CHECK.md supplies the reporting instructions.
