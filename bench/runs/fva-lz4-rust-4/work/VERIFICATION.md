**Verification is incomplete. R1, R2, and R3 have not been proved or refuted.**
No counterexample to a README requirement was found. The machine-checked results below
cover initialization, the artifact layout, and two decoder branches. The 17 additional
executions are regression tests, not universal proofs. A FVA PASS here applies only to
the four explicit claims in `Proofs/Spec.lean`.

| Requirement | Result and remaining gap |
| --- | --- |
| R1 | **Unproved.** `zeroLengthRejected_holds` and `emptyBlockDecoded_holds` prove an unchanged final store on their respective branches. They do not state a trace property about reads or intermediate writes. The runtime samples compare every byte of caller memory outside the destination before and after the call, but cannot detect forbidden reads or writes that are subsequently undone. No general access invariant for the decoder loops and bulk memory instructions was proved. |
| R2 | **Unproved in full.** `emptyBlockDecoded_holds` proves the valid single-zero-byte empty block with `cap = 0`, for every state and source address satisfying its explicit hypotheses. It returns zero, so the decoded-content assertion is empty. Other valid blocks are tested below. There is no complete Lean formalization of the LZ4 sequence relation or proof that arbitrary valid blocks follow the decoder loops and produce that relation's content. |
| R3 | **Unproved in full.** `zeroLengthRejected_holds` proves rejection of zero compressed bytes for every argument bit pattern and every call state satisfying its code hypothesis. Several malformed blocks are also tested. Neither this rejection result nor those tests proves that every nonnegative return has a valid sequence decomposition, valid offsets, and the required decoded content. |

The full requirements are not silently replaced by the partial claims. There is no
`R1_holds`, `R2_holds`, or `R3_holds` theorem, and no claimed demonstration of their failure.
The missing work is general input-dependent invariants and a connection to a formal LZ4
format/decoding relation, rather than a missing installation or a network dependency.

The exact proved statements are the following definitions, with `FVA.Wasm` and
`FVA.Wasm.Exec` open, as in `Proofs/Spec.lean`:

```lean
/-- The decoded artifact's decoder export, function body, and fixed memory layout. -/
def artifactProfile : Prop :=
  Lifted.module.imports = [] ∧ Lifted.module.start = none ∧
  Lifted.module.mems = [⟨32, some 32⟩] ∧
  Lifted.module.exports[2]? = some ⟨"lz4_decompress", .func 7⟩ ∧
  Lifted.module.funcs[7]? = some Lifted.func7 ∧ Lifted.func7.type = 4 ∧
  Lifted.module.types[4]? = some
    ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩

/-- The artifact has a successfully initialized fresh instance under every host semantics. -/
def artifactInitializes : Prop := Instantiable Lifted.module

/-- The shipped decoder's zero-input-length branch always terminates, returns -1, and
leaves the entire store unchanged. This holds for arbitrary argument bits and any store
containing the decoded function at address 7; it does not require buffer preconditions. -/
def zeroLengthRejected : Prop :=
  ∀ (H : HostSem) (s : Store) (inst : ModuleInst) (src dst cap : BitVec 32),
    s.funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7) →
    Must H (fun o => o = .returned s [.i32 4294967295])
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap])

/-- The valid empty block (a single zero byte) decodes to zero bytes with cap = 0,
without modifying the store, at every readable source address. The hypotheses describe
the decoder function and memory in the call state; instantiation is not asserted here. -/
def emptyBlockDecoded : Prop :=
  ∀ (H : HostSem) (s : Store) (inst : ModuleInst) (src dst : BitVec 32) (mem : MemInst),
    s.funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7) →
    inst.mems = [0] → s.mems[0]? = some mem →
    src.toNat + 1 ≤ mem.size → mem.byte src.toNat = 0 →
    Must H (fun o => o = .returned s [.i32 0])
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 1, .i32 0])

```

Their exact theorem declarations, in `Proofs/Proof.lean`, are:

```lean
theorem artifactProfile_holds : artifactProfile
theorem artifactInitializes_holds : artifactInitializes
theorem zeroLengthRejected_holds : zeroLengthRejected
theorem emptyBlockDecoded_holds : emptyBlockDecoded
```

`Must` is FVA's total-correctness execution relation: all executions allowed by the
WebAssembly semantics terminate with the stated outcome. `4294967295` denotes the i32
bit pattern for -1. Outcome equality here includes equality of the entire store.
The two branch theorems are conditional on the actual call state's function instance;
the empty-block theorem additionally states its memory hypotheses. They are not claims
about every initialized instance or arbitrary prior calls. `artifactInitializes` separately
establishes existence of a successfully initialized fresh instance under every host
semantics; it does not establish a decoder invariant across subsequent calls.

All four claims concern `lz4-flex.wasm`: exactly 7,161 bytes, SHA-256
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.
`Proofs/Lifted.lean` was generated using:

```sh
lake exe fva lift lz4-flex.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

Its kernel-checked `Proofs.Lifted.decode_eq` states
`FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len = .ok Proofs.Lifted.module`.
The generated file was not edited. FVA's link check compares its packed numeral to the
actual artifact bytes and independently replays `decode_eq`. `artifactProfile` ties the
export to function 7 and its four-i32-to-i32 signature. The branch proofs symbolically
execute that decoded function under FVA's WebAssembly semantics, not a Rust source model.
`Proofs/Init.lean` proves that an explicit expansion of the data bytes is equal to the
decoded module, checks successful FVA instantiation, and uses FVA's instantiation soundness
theorem. Neither the Wasm file nor the Rust software was modified or rebuilt.

From this directory, the complete reproduction command is:

```sh
bash Verification/check.sh
```

It validates the Wasm with `wasm-tools`, builds an external copy of FVA using the installed
offline package cache, builds the Lean project, runs:

```sh
"$task_verifier/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 60
```

and runs `python3 Verification/run_samples.py`. The script creates and removes its own
temporary verifier directory; only its package-cache paths are adjusted, and its executable
is relinked outside this project. No FVA implementation, specification, pin, verdict rule,
or canary is changed. No network is needed. The complete command succeeds with exit code
zero, `fva trust: PASS`, acceptance of all four claims by both default kernels, an artifact
link marked `matches`, and `PASS: 17 samples`. A final message explicitly limits success
to the partial claims. The recorded run is `Verification/check-output.txt`.
The recorded audit passed: Lean's checker and con-leche both accepted all four claims,
the artifact link matched, and all 17 runtime samples passed. FVA measured 27 reviewed
code lines in `Proofs.Spec`.

For quicker separate checks, `lake build` checks the Lean source proofs and
`python3 Verification/run_samples.py` checks only the runtime samples. Neither alone
performs the external FVA trust audit. Reproduction of the proof checks does not require
rebuilding the Rust crate.

`Verification/samples.json` lists the exact inputs, capacities, results, output prefixes,
and addresses for all runtime samples. The harness embeds the unchanged artifact as a
binary Wasm module, imports its memory and decompressor into a separate helper module,
writes the input, and fills the destination with 0xAA. Every case uses a fresh subject
instance and satisfies the README buffer preconditions. The helper compares every byte
from 131072 through 2097151 outside the destination against a snapshot after setup.
It also checks the exact return value and listed output prefix. In particular:

| Cases | Checked behavior |
| --- | --- |
| `emptyBlock`, `oneLiteral`, `fiveLiterals`, `literalExtension` | Returns 0, 1, 5, and 15 respectively, with exact content and capacity. |
| `overlapMatch`, `matchExtension`, `fastPath`, `nonoverlapMatch` | Returns 13, 25, 23, and 20 respectively; checks overlapping copying, length extension, spare capacity, and the optimized path. |
| `upperBoundary` | Source bytes are at 2097150 and 2097151; returns the single literal at destination 131072. |
| `emptyInput`, `truncatedLength`, `truncatedOffset`, `zeroOffset`, `offsetUnderflow` | Returns -1. Offset examples include input `[16,65,0,0,80,66,67,68,69,70]` and `[16,65,2,0,80,66,67,68,69,70]`. |
| `shortLiteralBuffer`, `shortMatchBuffer` | Returns -1 for insufficient output capacity. |
| `relaxedEnding` | `[16,65,1,0,0]` returns five copies of byte 65. Its empty final literal sequence breaks an end condition; R3 explicitly allows this relaxation. This is not a counterexample. |

These tests have a finite input set and use Wasmtime as a trusted executor. They are not
Lean certificates, a proof that the LZ4 parser is correct, a proof of read confinement,
or evidence for arbitrary destination contents, addresses, or previous invocation histories.

The primary formal review surface is `Proofs/Spec.lean`: **42 physical lines, 2082 bytes**.
FVA counts 27 code lines; the standard axiom closure is in the trust output. A reviewer
must compare these claims with the README and observe their limited scope. The runtime
checks additionally require reading `Verification/run_samples.py` (64 lines, 3183 bytes)
and `Verification/samples.json` (19 lines, 2786 bytes). The reproduction orchestration is
`Verification/check.sh` (33 lines, 1264 bytes). The requirements documents are `README.md`
(18 lines, 2402 bytes) and `lz4_Block_format.md` (244 lines, 10683 bytes).

The shared FVA trusted specification base is `fva/FVA/Spec/**/*.lean`: 23 files,
3606 physical lines, 161903 bytes. Its trusted fact-collection/replay/verdict glue in
`fva/FVA/Trust/*.lean` is 4 files, 887 lines, 40918 bytes; FVA also relies on its CLI,
link/file checks, exporter, and external kernel invocation code, including
`fva/FVA/Tool/Trust.lean` (309 lines, 16031 bytes), `fva/FVA/Lifted.lean` (35 lines,
1672 bytes), `fva/FVA/Tool/BaseManifest.lean` (263 lines, 13706 bytes),
`fva/FVA/Cli.lean` (120 lines, 6763 bytes), and `fva/FVA/Tool/Lift.lean`
(217 lines, 11159 bytes). FVA checks its library source files against compiled-in pins.
The usual residual trust is the Lean toolchain and its bundled independent kernels,
Mathlib at the installed v4.35.0 revision, and the correspondence between FVA's WebAssembly
specification and deployed Wasm engines. The trust output reports the kernels' canary
results and pinned known exceptions; it must not be read as saying every bundled checker
rejects every canary.

The proof implementations and generated lifting are kernel-checked rather than manually
trusted models: `Proofs/Proof.lean` (39 lines, 1498 bytes), `Proofs/Init.lean` (31 lines, 3855 bytes), and
`Proofs/Lifted.lean` (82 lines, 97882 bytes). The large generated lines do not make them
small to read; they are excluded from the human review surface only because the independent
proof replay and byte-link checks validate them. There are no project-added axioms,
`sorry`, `native_decide`, or alternative source-code models.
