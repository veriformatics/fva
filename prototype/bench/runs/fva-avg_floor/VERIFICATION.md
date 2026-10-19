# Verification of `avg_floor`

## Verdict: R1 and R2 are false

The C source, README requirements, and shipped `avg_floor.wasm` are unchanged.
There cannot be a sound proof that this artifact satisfies the requirements:
it adds in 32 bits **before** taking the arithmetic right shift.

Both failures are proved in Lean, not merely observed in tests:

| Signed inputs `(a, b)` | Required floor average | Shipped binary returns |
| --- | ---: | ---: |
| `(2147483647, 2147483647)` | `2147483647` | `-1` |
| `(-2147483648, -2147483648)` | `-2147483648` | `0` |

`AvgFloor/Requirements.lean` states the original obligations as `Requirements.R1`
and `Requirements.R2`. `AvgFloor/Spec.lean` states the findings below; it is
explicitly **not** a replacement or weakening of those requirements.

## What is machine-checked

The proofs are in `AvgFloor/Proof.lean`, checked with Lean **4.35.0**, without
Mathlib, network access, `sorry`, custom axioms, or `native_decide`.
Every input is a `BitVec 32`, interpreted as signed by `.toInt`; the sum and
average in the mathematical specification use unbounded `Int` arithmetic.

| Proven claim in `AvgFloor/Spec.lean` | Meaning |
| --- | --- |
| `machine_behavior` | For every input pair, execution terminates without trapping and returns `(a + b).sshiftRight 1`, where the addition wraps at 32 bits. |
| `exact_result` | Characterizes **every** possible i32 return value by its signed integer value, including overflowing inputs. |
| `correct_iff_sum_fits` | The required mathematical average is returned **if and only if** `-2147483648 ≤ a.toInt + b.toInt ≤ 2147483647`. Thus every overflowing sum is incorrect. |
| `positive_overflow`, `negative_overflow` | The two counterexamples above return the stated wrong answers and cannot return the required answers. |
| `r1_false`, `r2_false` | Formal negations of the original README obligations. |

Writing `s = a.toInt + b.toInt`, the exact signed result is

```text
floor((s + 4294967296) / 2)   if s < -2147483648
floor((s - 4294967296) / 2)   if s >  2147483647
floor(s / 2)                 otherwise
```

Additional checked lemmas establish:

- `invoke_exact`: for every input and **every fuel value**, invocation returns
  the specified result at fuel ≥ 6, and `none` below 6. This rules out obtaining
  a different result by choosing another fuel witness in `Returns`.
- `floorMean_is_floor`: for the specified average `q`, `2*q ≤ s < 2*(q+1)`.
  In particular, negative odd sums round down, not toward zero.
- `floorMean_fits`: the mathematical average itself always fits in signed
  32 bits, so encoding the expected answer does not hide an overflow.

## Connection to the actual code

1. Recompiling `avg_floor.c` with the README command and installed Clang 23.1.1
   produced a byte-for-byte identical copy of the shipped WebAssembly.
2. FVA generated `AvgFloor/Lifted.lean` directly from those bytes. Its pinned
   SHA-256 is
   `551d0f840db799ed5ff513d8c47b0d2eaf2f01f662ff408e8f5df41b152c93ba`.
3. The lifted body is `local.get 1; local.get 0; i32.add; i32.const 1;
   i32.shr_s`. The proof symbolically executes this body using FVA's
   `FVA.Wasm.invoke`/`Returns` semantics, then proves its signed arithmetic
   properties. It is not a proof about a separately hand-written C model.
4. `fva trust` recomputes the binary hash and regenerates the lift, checking
   both for identity. It found a proof for each of the seven findings, all
   connected to `AvgFloor.Lifted`, with only the standard axioms `propext`,
   `Classical.choice`, and `Quot.sound`. No syntax or implementation override
   issues were reported. Human review is `Spec.lean`, `Requirements.lean`,
   and `Def.lean`; proofs are imported only downstream of the specification.
5. FVA's differential test compared the Lean interpreter against wasmtime on
   200 deterministic edge/random cases (seed 0), with zero mismatches. This
   supports the lifter/semantics connection; it is not the universal proof.

The trusted base includes Lean's kernel and core definitions, the standard
axioms above, FVA's lifter, and `../../lean/FVA/Wasm/Semantics.lean`.
The source-to-binary link is a reproducible byte comparison, not a formal
compiler-correctness proof.

## Exact checking commands

Run from the repository root. All Python invocations use the existing offline
FVA environment, and the Lean project has only a local FVA dependency.

### Build the proofs and check the source/artifact connection

```sh
cd prototype/fva/examples/avg_floor
lake build
clang --target=wasm32 -O2 -nostdlib \
  -Wl,--no-entry -Wl,--strip-all -Wl,--export=avg_floor \
  -o avg_floor.rebuilt.wasm avg_floor.c
cmp avg_floor.wasm avg_floor.rebuilt.wasm
rm avg_floor.rebuilt.wasm
```

### Regenerate the lift (optional)

```sh
cd prototype/fva
uv run --offline --frozen fva lift \
  examples/avg_floor/avg_floor.wasm \
  examples/avg_floor/AvgFloor/Lifted.lean --ns AvgFloor.Lifted
```

### FVA audits and differential test

```sh
cd prototype/fva
uv run --offline --frozen fva trust examples/avg_floor --paranoid --json
uv run --offline --frozen fva difftest examples/avg_floor --cases 200 --seed 0 --json
uv run --offline --frozen fva trust examples/avg_floor \
  --spec-module AvgFloor.Requirements --json
```

The last command is **expected to exit 1**: R1 and R2 are unproved because they
are false. Their negations are proved in the findings module. A successful
audit of the findings must never be described as satisfaction of R1/R2.

Saved command output is in `trust-report.json`, `difftest-report.json`, and
`requirements-report.json`.

### Independent kernel replay in this container

The ordinary FVA audit above exits 1 here solely at its replay stage: all six
checker processes fail to start under nested `bwrap`, reporting
`Failed to create NETLINK_ROUTE socket: Operation not permitted`. This is an
environmental launch failure, not a mathematical rejection. The saved trust
report retains this FAIL; FVA itself has not been modified.

To run the same bundled checkers inside the already restricted outer container,
export the seven findings plus the mathematical-floor/representability lemmas
and use Lake's explicit no-*nested*-sandbox option:

```sh
cd prototype/fva/examples/avg_floor
lake env leanexport AvgFloor -- \
  AvgFloor.Proof.machine_behavior_holds \
  AvgFloor.Proof.exact_result_holds \
  AvgFloor.Proof.correct_iff_sum_fits_holds \
  AvgFloor.Proof.positive_overflow_holds \
  AvgFloor.Proof.negative_overflow_holds \
  AvgFloor.Proof.r1_false_holds \
  AvgFloor.Proof.r2_false_holds \
  AvgFloor.Proof.floorMean_is_floor \
  AvgFloor.Proof.floorMean_fits > proof-export.ndjson
lake check --from-export=proof-export.ndjson --paranoid --inadvisably-no-sandbox
rm proof-export.ndjson
```

This disables only Lake's nested sandbox, not the outer execution restrictions.
Lake prints a sandbox-disabled warning: this replay does not provide Lake's
usual isolation against hostile project/toolchain code. The project uses no
custom executable Lake configuration or proof-checker overrides.

**Observed result:** all six kernels accepted the exported proof closure:
Lean paranoid, lean4lean, nanoda, con-leche, con-ron, and Lean default.
The replay reported only `propext`, `Quot.sound`, and `Classical.choice` as axioms.
Thus the independent replay succeeded, despite the normal FVA command's
nested-sandbox launch failure.

## Not established

- **Neither R1 nor R2 holds.** Their failure is proved, rather than left as an
  unresolved proof gap. No source fix or replacement binary is supplied.
- No universal ISO C source-level correctness is claimed. Signed addition
  overflow is undefined in C, and right shift of negative signed values is
  implementation-defined for the usual C dialect used here. FVA verifies the
  pinned compiled WebAssembly, whose wrapping addition and arithmetic shift
  are explicit.
- FVA's normal nested-sandbox replay did not run in this container. The
  separate replay command above and ordinary Lean checking are distinguished
  from that failed launch; differential testing is not a proof of the trusted
  lifter or semantics.
