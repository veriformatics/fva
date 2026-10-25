All three requirements in `README.md` fail for the shipped artifact. The results
below are counterexamples, with machine-checked execution proofs; they are not
claims that the codec is correct on other inputs. No shipped software or format
document was changed.

| Requirement | Result | Witness |
|---|---|---|
| R1 | Fails | Encoding the 13-byte input below returns an invalid block with only four final literals. |
| R2 | Fails | A valid block decoding to 13 bytes produces return value 1 and the wrong output. |
| R3 | Fails | A valid one-byte empty block causes a read at the first address beyond the block. |

**Exact machine-checked statements.** All four theorems are in
[`Proofs/Proof.lean`](Proofs/Proof.lean):

```lean
theorem Proofs.fresh_instance_holds : Proofs.fresh_instance
theorem Proofs.r1_counterexample_holds : Proofs.r1_counterexample
theorem Proofs.r2_counterexample_holds : Proofs.r2_counterexample
theorem Proofs.r3_counterexample_holds : Proofs.r3_counterexample
```

Their proposition definitions are reproduced exactly below, in namespace
`Proofs` with `FVA.Wasm` and `FVA.Wasm.Exec` open. The accompanying byte arrays,
caller stores, memory observer and active-load observer are defined in
[`Proofs/Spec.lean`](Proofs/Spec.lean). The format specification is
[`Proofs/Format.lean`](Proofs/Format.lean).

```lean
def fresh_instance : Prop :=
  Instantiable Lifted.module ∧ ∀ H, Instance Lifted.module H allocation.1 allocation.2

/-- R1 fails: from the required hash-table setup, encoding these 13 bytes always
returns 13 and writes encoderOutput, which violates the supplied LZ4 end conditions. -/
def r1_counterexample : Prop :=
  (∀ H, CallReturns H encoderStore allocation.2 "lz4BlockEncode"
    [.i32 262144,.i32 13,.i32 300000]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 300000 13 = some encoderOutput)) ∧
  Format.decode encoderOutput = none

/-- R2 fails: validBlock decodes to decodedBlock in the format specification,
but the shipped decoder returns 1 and writes only its first literal A.
All buffers fit, are disjoint, and no memory growth is needed. -/
def r2_counterexample : Prop :=
  Format.decode validBlock = some decodedBlock ∧ decodedBlock.length = 13 ∧
  ∀ H, CallReturns H decoderStore allocation.2 "lz4BlockDecode"
    [.i32 100,.i32 10,.i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 13 = some (65 :: List.replicate 12 0))

/-- R3 fails even on the valid empty block 00: an execution reaches a byte load
at address 201, outside [200,201), and takes its next step. Additionally, varying
only that outside byte changes the call's return value from 0 to 4. -/
def r3_counterexample : Prop :=
  Format.decode [0] = some [] ∧
  (∀ H, ∃ c c', Steps H (invokeConfig (emptyStore 1) 3 [.i32 200,.i32 1,.i32 300]) c ∧
    nextByteRead 20 c.instrs = some 201 ∧ Step H c c') ∧
  (∀ H, CallReturns H (emptyStore 0) allocation.2 "lz4BlockDecode"
    [.i32 200,.i32 1,.i32 300] (fun _ vs => vs = [.i32 0])) ∧
  (∀ H, CallReturns H (emptyStore 1) allocation.2 "lz4BlockDecode"
    [.i32 200,.i32 1,.i32 300] (fun _ vs => vs = [.i32 4]))

```

`CallReturns` is FVA's total-correctness claim: for every execution under the
chosen host semantics, the call terminates without trapping and its result and
final store satisfy the postcondition. These claims quantify over every host
semantics. `fresh_instance_holds` proves the named allocation really is a fresh
instance; the caller stores change only its memory. The decoder buffers fit the
initial 65,536-byte memory. The encoder setup grows it to five pages.

**R1 witness.** Initialize all 65,536 hash-table words at address 0 to −65536,
as required by the README. Write these hexadecimal bytes at address 262144:

```text
00 01 02 03 41 41 41 41 41 42 43 44 45
```

Call `lz4BlockEncode(262144, 13, 300000)`. It returns 13 and writes exactly:

```text
50 00 01 02 03 41 01 00 40 42 43 44 45
```

The first token describes five literals followed by an offset-1 match of length
4. The final token `40` describes only four literals. The decoded input has
length 13, so the short-input exception to the five-final-literal rule does not
apply. The match also starts at decoded index 5, only 8 bytes before the end;
the required distance is at least 12. Either violation refutes R1's validity
conjunct. The format checker rejects this exact output. No round-trip failure is
needed to refute the conjunction. All hash words are initialized with byte pattern
`00 00 ff ff`; the input and output buffers are separate and large enough.

**R2 witness.** Write this valid block at address 100:

```text
13 41 01 00 50 42 43 44 45 46
```

Its decoded content is eight copies of `41` followed by `42 43 44 45 46`, for
13 bytes total. Its only match starts at decoded index 1 (exactly 12 bytes before
the end); its final sequence has five literals. Call
`lz4BlockDecode(100, 10, 0)` with the rest of memory initially zero. It returns 1.
The proof also checks the final output region: `41` followed by twelve zero
bytes, which differs from the required content. The compressed input `[100,110)`
and output `[0,13)` are disjoint. Inspection of the decoder explains the early
exit: it compares the match's destination address 0 against the compressed
input's end address 110.

**R3 witness.** Put `00` at address 200, representing the valid empty LZ4 block,
and call `lz4BlockDecode(200, 1, 300)`. Initialize bytes 201 and 202 to `01 00`.
The execution proof constructs a state after 35 unique FVA steps, proves it is
reachable by the Wasm `Steps` relation, and proves it has an active byte load at
address 201 with a succeeding Wasm step. This address is outside `[200,201)`.
`nextByteRead 20` only traverses the active stack/labels/frame to identify that
load; its fuel bounds this observation, not the program execution.

The same theorem additionally proves that changing only byte 201 from 0 to 1
changes the returned length from 0 to 4. Both calls receive the same block byte,
pointer, length, and separate output buffer. These are reads within Wasm linear
memory but outside the caller's block; a Wasm bounds check cannot prevent them.
This is also an additional R2 counterexample on the valid empty block.

**Connection to the shipped bytes.** The verified subject is
`lz4-block-codec.wasm`, 1,226 bytes, SHA-256:

```text
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

[`Proofs/Lifted.lean`](Proofs/Lifted.lean) was generated with:

```sh
lake exe fva lift lz4-block-codec.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It contains the exact packed bytes and decoded Wasm syntax. Its `decode_eq`
theorem is checked by the kernel against FVA's decoder. The execution proofs use
this decoded module, not a translation of the WAT source. FVA's link check binds
the packed bytes to the current `.wasm` file and checks the generated file.
The decoder's format reference is a separate, reviewed specification, never a
replacement for the artifact's implementation.

**Reproduction from this directory, without network access.** Run:

```sh
python3 verification/check.py
```

This creates a temporary copy of the unchanged FVA package outside this project,
points it at the existing dependency cache, recompiles its entry point and links
its executable there, builds the proofs, validates the Wasm, runs FVA trust, and
runs the Wasmtime witnesses. It cleans up only its private temporary directory.
The manifest's package-directory warning is harmless; no `lake update` or network
access is required. Success means exit status 0, FVA `PASS` with all four claims
proven and both default replay kernels accepting, followed by:

```text
PASS: shipped bytes match; all Wasmtime counterexample assertions passed
PASS: Lean build, FVA trust, artifact validation, and Wasmtime assertions
```

Individual checks, also from this directory:

```sh
lake build
wasm-tools validate lz4-block-codec.wasm
python3 verification/check_wast.py
```

With an externally built, unchanged FVA executable at `$FVA_VERIFIER`, the exact
auditing command is:

```sh
"$FVA_VERIFIER" trust . --spec-module Proofs.Spec --root-module Proofs --surface-budget 150 --kernel-limit 300
```

`lake build` must report success; Wasm validation succeeds silently. The Wasmtime
script checks that its embedded binary is byte-for-byte the shipped artifact
before executing its assertions. The formal proofs use kernel reduction and
FVA's proven `runDet_must`, `steps_of_walk`, and `step_sound` lemmas. Finite fuel
is used to construct terminating witnesses, then discharged into unfueled Wasm
execution claims. There are no `sorry`, custom axioms, or `native_decide` proofs.

**Review and trust.** The project-specific semantic review consists of
`Proofs/Spec.lean` (89 physical lines, 4,566 bytes) and `Proofs/Format.lean`
(48 lines, 2,265 bytes): 137 physical lines, 6,831 bytes total. FVA measures this as 80 code lines
(49 in `Proofs.Spec`, 31 in `Proofs.Format`). Review their
interpretation of the English requirements, the buffer setup, and the format's
end conditions. The format checker is a specification of the supplied document;
there is no separate theorem equating that English document with the checker.
For these witnesses, the format judgments can also be inspected directly from
the tokens and end conditions described above.

`Proofs/Proof.lean` is 108 lines / 4,394 bytes; its proof text does not need to be
trusted because it is kernel-checked and independently replayed. The generated
lift is 67 lines / 20,377 bytes and is checked by FVA rather than manually
trusted. Optional runtime reproduction adds `verification/check_wast.py`
(17 lines / 758 bytes) and `verification/reproduce.wast` (44 lines / 5,954 bytes).
The offline orchestration script `verification/check.py` is 34 lines / 1,508
bytes. These scripts are not premises of the Lean execution proofs.

The shared trust boundary is FVA's reviewed Wasm/claim/format vocabulary, its
artifact-link and fact-collection glue, the kernel/export/replay tools, the Lean
compiler, and the pinned Mathlib dependency environment. The unchanged FVA spec
tree has 23 Lean files / 3,606 physical lines / 161,903 bytes. Its seven principal
trusted-glue modules (`Trust/{Collect,Replay,Canary}` and
`Tool/{Trust,Lift,Pack,BaseManifest}`) total 1,559 lines / 77,249 bytes; see
`fva/AGENT.md` and the audit report for the precise boundary. FVA's implementation
proofs establish the stepper/decoder contracts and are checked rather than
manually assumed. Wasmtime is a separate corroborating implementation, not part
of the proof's trust base.

The saved audit output is [`verification/fva-trust.txt`](verification/fva-trust.txt).
The recorded audit is `PASS`: all four claims are proven, the artifact link
matches, and both replay kernels accepted (`leanchecker`: 88 s; `con-leche`:
63 s). The axiom closure is exactly the standard `propext`, `Classical.choice`,
and `Quot.sound`.

The audit also reports all 72 pinned known-false canaries: Lean's checker rejected
71 and accepted one already listed in FVA's pinned known-acceptance set;
`con-leche` rejected 69 and declined three, accepting none. These existing FVA
canary exceptions are visible in the saved report. FVA's verdict permits them;
no project-specific exemption was added.

FVA's `PASS` certifies the counterexample claims above, not that the README
requirements hold. The end-to-end command's output is also saved in
[`verification/check.log`](verification/check.log).
