# Verification result

**R1 fails.** The shipped `glm-iround.wasm` returns `1` on the finite binary64 input

```
bits: 0x3fdfffffffffffff
x:    9007199254740991 / 18014398509481984
      = 0.499999999999999944488848768742172978818416595458984375
```

This input satisfies `0 ≤ x ≤ 2147483647`. Its distance from `0` is
`9007199254740991 / 18014398509481984`; its distance from the returned `1` is
`9007199254740993 / 18014398509481984`. Thus `0` is strictly closer. This is not a tie.
R1 is the only numbered requirement in README.md.

## Exact machine-checked statements

[Proofs/Counterexample.lean](Proofs/Counterexample.lean) contains these definitions and theorem statements:

```lean
def numerator : Int := 9007199254740991
def denominator : Int := 18014398509481984
def output : Int := 1

def Nearest (n d r : Int) : Prop :=
  ∀ m : Int, (n - r * d).natAbs ≤ (n - m * d).natAbs

theorem domain_and_strictly_closer :
    0 < denominator ∧ 0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator ∧
    (numerator - 0 * denominator).natAbs < (numerator - output * denominator).natAbs

theorem r1_counterexample :
    0 < denominator ∧ 0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator ∧
    ¬ Nearest numerator denominator output
```

These declarations are in namespace `Counterexample`. `Int` is unbounded;
`Int.natAbs` is absolute value as a natural number. For positive `d`, multiplying
all distances from `n/d` by `d` preserves their comparisons. Consequently
`Nearest n d r` expresses exactly that integer `r` minimizes distance, allowing
ties. This is a mathematical specification, not a model of `iround`.

The checker generates [.verification/Observation.lean](.verification/Observation.lean)
from the actual input bits and observed output, compiles it, and includes this
additional theorem in every proof replay:

```lean
theorem observation_link :
    (4602678819172646911 : Nat) = 1021 * 2^52 + (2^52 - 1) ∧
    (0 : Nat) < 1021 ∧ (1021 : Nat) < 2047 ∧
    Counterexample.numerator = Int.ofNat (2^52 + (2^52 - 1)) ∧
    Counterexample.denominator = Int.ofNat (2^(1075 - 1021)) ∧
    Counterexample.output = 1 := by decide +kernel
```

This connects the certificate to the normal binary64 encoding: sign zero,
stored exponent `1021`, fraction `2^52 - 1`. A positive normal binary64 number
has exact value `(2^52 + fraction) * 2^(exponent - 1075)`. The exponent is
strictly between zero and 2047, so this input is finite.

## Connection to the shipped artifact

[check.py](check.py) requires the artifact to have exactly 66 bytes and SHA-256
`eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a`,
matching README.md. It validates those bytes and loads that file directly into
Wasmtime using `--preload artifact=…`.

The generated [.verification/invoke.wat](.verification/invoke.wat) imports the
original module's `iround` export. It passes `i64.const 4602678819172646911`
through `f64.reinterpret_i64` and calls the imported function. There is no
decimal-input conversion and no replacement implementation. The observed
result is `1`; the generated `observation_link` theorem checks that this is the
same output used by the mathematical certificate. The script also verifies
that the artifact's bytes remain unchanged after checking.

For explanation, `wasm-tools print` produces:

```wat
local.get 0
f64.const 0x1p-1
f64.add
i32.trunc_sat_f64_s
```

Adding `0.5` to this input has exact real value `1 - 2^-54`, halfway between
the adjacent binary64 values `1 - 2^-53` and `1`. Ties-to-even addition yields
`1`, and truncation returns `1`. This explanation is not an assumption of
the Lean proofs: the artifact result is obtained by execution.

The delivered result is an execution counterexample with a kernel-checked
mathematical certificate. It does not claim a formalized Wasm operational
semantics or a proof about all executions. No C++ source or artifact was
rewritten, rebuilt, or substituted; neither the C++ compiler nor GLM source
translation is needed for this result.

## One checking command

From this directory, with the supplied offline Lean installation and tools:

```sh
python3 -I check.py
```

The script locates checker executables under `lean --print-prefix` and uses
`lake env` for the existing project configuration. It always recompiles both
proof sources, exports the three theorems and their transitive dependencies,
and replays the same export from empty environments through:

1. `leanchecker`: Lean's C++ kernel.
2. `leanchecker-paranoid`: the installed paranoid Lean checker variant.
3. `nanoda_bin`: the independent Rust implementation, nanoda 0.4.19.

The first two are not claimed to be independent implementations of each
other. Independence is supplied by Lean's C++ kernel versus nanoda's Rust
kernel. Neither checker is allowed any axioms for this certificate. The
export has **zero axioms**, including no `sorryAx` or `Lean.trustCompiler`.
The proofs use `decide +kernel`, not native computation accepted as an axiom.

Each checker must also accept an unmodified positive control, then reject
both deliberately false proofs. The script exports `True.intro : True` and
`rfl : (0 : Nat) = 0`, then changes only the claimed types to `False` and
`(0 : Nat) = 1`, respectively. These are structurally valid export files with
ill-typed proof terms. Rejection must include a type-equality failure
diagnostic, not merely a nonzero exit status. All six negative checks passed.

Success requires exit status zero and ends with:

```text
leanchecker: proof and positive control ACCEPT; False and 0=1 proofs REJECT
leanchecker-paranoid: proof and positive control ACCEPT; False and 0=1 proofs REJECT
nanoda_bin: proof and positive control ACCEPT; False and 0=1 proofs REJECT
PASS: R1 is refuted for the pinned shipped artifact; all kernel controls passed.
```

Generated exports, controls, the input wrapper, disassembly, and checker logs
are retained in `.verification/` and regenerated on every run. Nanoda currently
also reports one pretty-printer diagnostic, `Unable to print axioms`; it
reports **no typechecker errors** and exits zero on the valid exports. Its
negative controls fail in the type checker. The script checks these outcomes.

## Human review and size

Review the definitions and theorem statements above, the interpretation of
scaled distances and binary64 encoding, and [check.py](check.py), especially
the byte pin, imported call, observed-output linkage, export targets, axiom
check, and positive/negative controls. The execution evidence additionally
trusts Wasmtime's execution of these bytes and ordinary host I/O/process
handling. The kernels check mathematical proof validity; they do not prove
the runtime or checking script correct.

The project-specific formal surface is four definitions and two theorem
statements, **11 nonblank declaration lines**, plus the generated link
statement, **6 lines**. Including imports, namespaces, comments, and proof
terms, the two Lean files total **36 lines / 1,374 bytes**. The runner is
**143 lines / 6,310 bytes**; its generated Wasm wrapper is **6 lines / 192
bytes**. No handwritten floating-point or Wasm execution model is introduced.

Underlying Lean definitions are also part of the semantic review: natural
and integer constructors, arithmetic, order, absolute value, and logical
connectives must have their usual meanings. They are not hidden behind the
project-specific count. The complete exported dependency closure, including
proof dependencies, is **6,580 NDJSON records / 362,480 bytes**, comprising
**140 definition declarations, 28 inductive groups, and 37 theorems**
(**265 declarations** counting individual constructors and recursors).
Every declaration in this conservative closure is replayed by the kernels;
no imported proof library is simply accepted as a trusted collection of
theorems. Mathlib is available but unnecessary for this small certificate.
