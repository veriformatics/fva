# Verification

## Check everything

From this directory, run:

```sh
./check.sh
```

Observed result: **`ALL CHECKS PASSED` (exit 0)**, including all three kernel
replays, six false-export rejections, the frontend rejection, and the artifact
mutation control.

No network, Mathlib, package installation, or previously built proofs are used.
Requires Python 3, Clang with the wasm32 linker, Lean **4.35.0**, and
`leanexport`, `leanchecker`, `leanchecker-paranoid`, and `lean4lean` in
`$(lean --print-prefix)/bin`. Missing tools and failed controls are fatal.
Generated inputs, exported proof terms, diagnostics, and a machine-readable
size/hash report are in `.verification/`; this directory is recreated each run.

## What is proved

`SatAdd.artifact_correct : SatAdd.Requirements SatAdd.artifact`
in `verification/Proof.lean` proves, for **all 2^64 pairs** of 32-bit input
words, that calling the exported function terminates successfully with a
32-bit result satisfying all three README requirements:

- R1: an in-range mathematical signed sum is returned exactly.
- R2: a sum above 2147483647 returns 2147483647.
- R3: a sum below -2147483648 returns -2147483648.

`BitVec 32` represents every possible input bit pattern; `toInt` interprets
it as a signed two's-complement integer. The additions in `Requirements` are
**unbounded integer addition**, not wrapping machine addition. Success is an
explicit `some r`, not an implication conditional on successful execution.
The arithmetic proof handles wrapping addition, sign comparisons, arithmetic
right shift, XOR, and selection in the actual optimized implementation.

## Connection to the shipped code

Neither `sat_add.c` nor `sat_add.wasm` was rewritten.

1. The checker rebuilds C using exactly the README command, with only the
   output path changed, and requires byte-for-byte equality with the shipped
   Wasm module. A different compiler output is rejected, not silently substituted.
2. It reads **every byte** of the shipped module and regenerates
   `Artifact.lean`; this must equal the committed byte embedding. The regenerated
   file, not a cached `.olean`, is compiled for the proof.
3. `Semantics.lean` checks the complete 55-byte module envelope and total
   87-byte length. This identifies the type `(i32, i32) -> i32`, the single
   function, memory, both exports (including `sat_add` at function index 0),
   code/body sizes, and its one zero-initialized local. There are no imports,
   start function, other functions, or unchecked trailing bytes.
4. The remaining bytes are executed by a small fail-closed Wasm stack
   interpreter. It interprets individual opcodes; it does **not** recognize
   the implementation and replace it with a saturation formula. Unsupported
   instructions/encodings, bad locals/stacks, and exhausted fuel return `none`.
   The proof reduces this byte execution to a bitwise expression and proves
   that expression satisfies the integer requirements.
5. An automatic mutation control changes the supported `i32.add` opcode at
   byte 59 to `i32.xor`, regenerates the embedding, and requires recompiling
   the *unchanged proof* to fail. Merely checking a source hash would not
   exercise this semantic link.

Original SHA-256 values (also recomputed in the check report):

| File | SHA-256 |
| --- | --- |
| `sat_add.c` | `ff1a119f0a6467fbb41fb27acd5d7bb8d63689d9bd7f32af1cf27fb8f3164550` |
| `sat_add.wasm` | `cd4ffd1bdffc619863f7e6c496a9952c9412c0534d66f1b0dc89000914bd8342` |

## Human-review boundary and size

The project-specific meaning boundary is only:

- `verification/Semantics.lean`: `Word`, `execute`, `envelope`, `invoke`, and
  `Requirements` (41 nonblank, non-comment source lines, including boilerplate).
- `verification/Artifact.lean`: the literal 87-byte module (4 such source lines).
- The single final theorem statement above (1 line).

**Total: 46 code lines, 2,694 UTF-8 bytes** using the counting rule implemented
in `review_size` in `verification/check.py`. Comments and blank lines are
excluded; the complete module data and module/import boilerplate are included.
The two semantic source files including comments/whitespace occupy 3,178 bytes.
Proof helpers in `Arithmetic.lean` and the proof bodies add no assumptions and
are not part of this meaning boundary.

This does not hide the standard-library definitions behind the short line
count. The checker additionally exports the conservative **entire transitive
statement/definition closure**, rooted at `Requirements` and `artifact`, to
`.verification/review.ndjson`, and lists every declaration in
`.verification/review-declarations.txt`. It includes generated matchers, core
integer/bitvector/list definitions, inductives, and proofs used by those
definitions. On this toolchain that closure has **912 declarations**:
387 definitions, 359 theorems, 51 inductive types, 58 constructors, 51 recursors,
4 quotient primitives, and 2 logical axioms. The full serialized closure is
approximately **2.13 MB** (the exact serialized byte count is recomputed in
`.verification/report.json`; export ordering can affect that count). These
are conservative export sizes, not a claim that the standard library is only
46 lines.

The critical review is that this small interpreter/envelope implements the
relevant Wasm instructions, and that `Requirements` correctly expresses R1–R3.
No hand-written C model is an assumption of the theorem.

The disk-to-proof binding also requires reviewing the ordinary orchestration
code, particularly `embed`, its equality check, and the fresh build/export
commands in `verification/check.py`. This is not a verified Python program.
Separately from the formal-statement size, the complete driver and shell entry
point occupy **220 physical lines / 10,765 bytes**, including comments, audit
code, and negative-control generation.

## Independent checking and false-proof controls

The checker exports the final theorem and **all 2,431 transitive declarations**
used in its proof. It replays that export from an empty environment with:

```sh
P=$(lean --print-prefix)
"$P/bin/leanchecker" --from-export .verification/proofs.ndjson
"$P/bin/leanchecker-paranoid" --from-export .verification/proofs.ndjson
"$P/bin/lean4lean" --import .verification/proofs.ndjson
```

Lean4Lean is a separately implemented Lean kernel. Default and paranoid Lean
are additional checks of the C++ kernel family, not two further independently
implemented kernels. Export replay avoids trusting imported `.olean` proofs
or just checking the last project declaration.

The complete exported proof is audited to allow only `propext`, `Quot.sound`,
and `Classical.choice`. There is no `sorryAx`, application-specific axiom,
`native_decide`, or native `bv_decide` evaluation axiom. No SAT solver is needed.

Each replay checker must first accept a valid control export, then reject
**both** of these deliberately forged, well-formed exports with a proof-type
error and exit status 1:

- `False := True.intro`;
- `(0 : Nat) = 1 := Eq.refl 0`.

The driver changes theorem types in actual exported proof terms, retaining
valid dependencies and JSON ordering. An unavailable checker, parser failure,
timeout, or process crash does not count as successful rejection. The Lean
frontend must also reject `theorem falseSource : False := True.intro`.
Lean4Lean's installed build can emit pretty-printer diagnostics on type errors;
the control requires its final explicit kernel type-mismatch diagnostic.
Full outputs are retained in `.verification/*.log`.

The exact fresh compilation commands, run inside `.verification/` with
`LEAN_PATH` set to that directory, are:

```sh
lean -o Artifact.olean Artifact.lean
lean -o Semantics.olean Semantics.lean
lean -o Arithmetic.olean Arithmetic.lean
lean -o Proof.olean Proof.lean
lean -o Controls.olean Controls.lean
P=$(lean --print-prefix)
"$P/bin/leanexport" Proof -- SatAdd.artifact_correct > proofs.ndjson
```

`./check.sh` additionally performs the rebuild, embedding checks, closure
and axiom audits, all positive/negative kernel controls, and artifact mutation.

## Scope and limitations

- This is a proof of the shipped Wasm function under the explicit instruction
  semantics, not a formalization of all of ISO C or a proof of Clang/linker
  correctness. Exact reproduction links the current C build to the proved
  artifact without needing compiler correctness for the binary claim.
- The instruction semantics and fixed module-envelope interpretation are
  manually specified and must be reviewed against Wasm semantics. There is
  no machine-checked refinement to the official Wasm specification, an
  external runtime, or a general-purpose Wasm parser/type validator.
- Only the instructions/encodings present here are supported. Interpreter fuel
  bounds this straight-line invocation; this is not a general loop verifier.
- Successful module instantiation and a conforming Wasm runtime are assumed;
  host resource exhaustion, runtime/compiler bugs, and other C targets/builds
  are not proved. No claim is made about performance or memory allocation.
