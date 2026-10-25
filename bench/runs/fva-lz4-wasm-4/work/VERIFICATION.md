All three README requirements fail on the shipped artifact. The counterexamples below have Lean proofs of their Wasm execution behavior using FVA, and independently reproduce in Wasmtime. These are proofs of failures on specific inputs, not proofs of universal codec correctness.

The artifact is `lz4-block-codec.wasm`: **1,226 bytes**, SHA-256
`4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf`.
Neither the artifact nor its WAT source was changed.

**R1 fails: the encoder emits an invalid block.** Initialize all 65,536 hash words at address 0 to −65536, as the README requires. Grow memory from one to five pages. Put these 13 input bytes at 262144 and use output address 262208:

```text
61 62 63 64 65 61 62 63 64 65 66 67 68    abcdeabcdefgh
```

The encoder returns 13 and writes exactly:

```text
50 61 62 63 64 65 05 00 40 65 66 67 68
```

Token `50` introduces five literals, `abcde`, followed by offset 5 and match length 4. Token `40` introduces the final four literals, `efgh`. The decoded length is 13 and the last match starts at decoded offset 5. Thus only four final bytes are literals, and the last match starts only eight bytes before the decoded end. This violates end-of-block conditions 2 and 3 in `lz4_Block_format.md`. A validity failure alone refutes R1's conjunction; this example does not claim a separate encoder round-trip failure. The input is above the minimum encoding size, and table, input, and output buffers are disjoint and fit in memory.

**R2 fails: a valid block decodes to the wrong length and content.** In a fresh instance, put this ten-byte block at address 100 and decode to address 0:

```text
17 61 01 00 50 62 63 64 65 66
```

Its first token specifies one literal `a`, offset 1, and match length 11. The overlapping copy produces twelve `a` bytes in total. The final token specifies five literals `bcdef`. The required decoded content is therefore twelve `a` bytes followed by `bcdef`, length **17**. This is a valid independent block: positive offset into prior decoded content, five final literals, and the last match starts 16 decoded bytes before the end. Both buffers fit and are disjoint.

The shipped decoder instead returns **1**. Its first 17 output bytes are `61` followed by sixteen zero bytes. The decoder compares the match address against the compressed input's end address and exits early when the output buffer precedes the input buffer. The README imposes no buffer-order constraint.

**R3 fails: the decoder reads beyond even a valid empty block.** The format explicitly permits the one-byte block `00` to encode empty content. Put it at address 0 and call `lz4BlockDecode(0, 1, 1024)` in fresh memory:

| Bytes at addresses 0, 1, 2 | Bytes within the supplied block | Return value |
|---|---|---|
| `00 00 00` | `00` | 0 |
| `00 01 00` | `00` | 4 |

Only byte 1 changes, outside the supplied interval `[0,1)`. The arguments and input block are identical. FVA proves both return values under every host semantics. This is a differential witness of dependence on an out-of-block byte. The decoder treats bytes after the final empty token as a match offset.

There is also a boundary witness: place `00` at address **65535** in the fresh one-page memory and call `lz4BlockDecode(65535, 1, 0)`. FVA proves this call traps. Wasmtime identifies the fault as a read at **65536**, immediately beyond both the block and linear memory. Empty decoded content needs no output capacity. This also independently demonstrates an R2 failure.

**Exact machine-checked statements.** The following theorems are in `Proofs/Proof.lean`; each statement is exactly the named definition in `Proofs/Spec.lean`:

```lean
theorem r1_counterexample_holds : r1_counterexample
theorem r2_counterexample_holds : r2_counterexample
theorem r3_counterexample_holds : r3_counterexample
theorem empty_boundary_traps_holds : empty_boundary_traps
theorem initialization_holds : initialization
```

Their claim definitions, in namespace `Proofs` with `FVA.Wasm` and `FVA.Wasm.Exec` open, are:

```lean
def r1_counterexample : Prop :=
  ∀ H, CallReturns H encoderStore allocation.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 262208]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 262208 13 = badBlock)

def r2_counterexample : Prop :=
  ∀ H, CallReturns H (allocation.1.withBytes 100 validBlock) allocation.2
    "lz4BlockDecode" [.i32 100, .i32 10, .i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 17 = 97 :: List.replicate 16 0)

def r3_counterexample : Prop :=
  ∀ H,
    CallReturns H (allocation.1.withBytes 0 [0,0,0]) allocation.2
      "lz4BlockDecode" [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 0]) ∧
    CallReturns H (allocation.1.withBytes 0 [0,1,0]) allocation.2
      "lz4BlockDecode" [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 4])

def empty_boundary_traps : Prop :=
  ∀ H, CallTraps H (allocation.1.withBytes 65535 [0]) allocation.2
    "lz4BlockDecode" [.i32 65535, .i32 1, .i32 0] (fun _ => True)

def initialization : Prop :=
  (∀ H, Instance Lifted.module H allocation.1 allocation.2) ∧
  ((memory0 allocation.1).grow 4).isSome = true ∧
  (memory0 encoderStore).pages = 5
```

`allocation` is FVA's fresh allocation of `Lifted.module`; the initialization theorem proves it is an actual fresh instance under every host semantics. `encoderStore` grows its memory by four pages, initializes every table word, and writes `encodeInput`. `bytesAt` reads exported memory 0. These setup and observation definitions, and the exact byte lists, are all in `Proofs/Spec.lean`.

`CallReturns` proves termination without traps, the exact return values, and the stated memory effects, for every execution allowed by FVA's Wasm semantics. `CallTraps` proves every execution terminates with a trap. The proofs compute concrete deterministic executions in the Lean kernel, then use FVA's proved `runDet_must` connection to the declarative Wasm execution semantics. Fuel is only a proof computation bound, not an assumption in the claims. There are no admitted proofs, custom axioms, or native-decision proofs.

The LZ4 format has **not** been replaced by an asserted general correctness predicate or a new codec model. The formal statements establish concrete artifact executions; the direct token interpretations and their comparison with the supplied format document above are the reviewable demonstration that those executions violate the requirements. In particular, the report does not claim a machine-checked formalization of the entire English LZ4 specification or a formal general noninterference theorem for R3.

**Connection to the bytes.** `Proofs/Lifted.lean` is unedited output of:

```sh
lake exe fva lift lz4-block-codec.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It embeds all artifact bytes and proves:

```lean
Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len =
    .ok Proofs.Lifted.module
```

FVA's trust check compares the embedded numeral and length with the actual file, verifies that the generated file regenerates exactly, and independently replays `decode_eq` along with the counterexample proofs. No equivalence assumption about the hand-written WAT source is used. The separate runtime witnesses import the shipped `.wasm` directly.

**Reproduction, offline, from this directory.** Run:

```sh
bash witnesses/check.sh
```

This pins both artifact and supplied checker hashes, snapshots the supplied prebuilt FVA executable into a temporary directory outside the project, copies its package pins and pinned canary corpus, validates the Wasm, runs `lake build`, and runs:

```sh
"$checker_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 100
python3 witnesses/runtime.py
```

The script creates `checker_dir`; no external downloads are needed. The checker executable is the unmodified supplied prebuilt binary, SHA-256 `5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407`, copied outside the project, not a newly compiled checker. For an independently supplied FVA installation, run its external executable with the same `trust` arguments instead.

Success means exit status 0, a successful Lean build, FVA `PASS` for all five counterexample/setup claims with accepted kernel replays and a checked artifact link, followed by:

```text
r1: 1 (expected)
r2: 1 (expected)
r3_zero: 0 (expected)
r3_one: 4 (expected)
boundary: out-of-bounds read at 65536 (expected)
All artifact counterexamples reproduced.
```

For `r1`, runtime result 1 means the wrapper checked both the returned length and every output byte against the invalid block above. The boundary invocation is expected to fail inside the runtime; the Python script checks its failure and fault address, then exits successfully. `-C cache=n` avoids writing to the environment's read-only Wasmtime cache directory.

Recorded results are `witnesses/trust.txt` and `witnesses/runtime.txt`. The completed trust run returned **PASS**, with `leanchecker` accepting the proof export in 126 seconds and the independent `con-leche` kernel accepting it in 89 seconds. The artifact link matched, and the review surface was **40 code lines**, all in `Proofs.Spec`.

The pinned 72 known-false canaries produced: Lean checker, 71 rejections and one known acceptance; con-leche, 69 rejections and three declines. FVA accepts this combination because the other kernel rejects the known false export that Lean's checker accepts; the complete status counts are recorded in the report. A `PASS` here validates the counterexample claims; it does **not** mean R1–R3 hold.

**Review and trust surface.** A reviewer must read the claims and setup definitions in `Proofs/Spec.lean` (75 physical lines, 3,710 bytes), the token interpretations in this report against `lz4_Block_format.md` (244 lines, 10,683 bytes), and the README's interface assumptions. No full LZ4 model is hidden in proof code. The optional independent execution path consists of `witnesses/runtime.wat` (33 lines, 1,658 bytes) and `witnesses/runtime.py` (29 lines, 1,310 bytes). The reproduction driver is `witnesses/check.sh` (16 lines, 904 bytes).

`Proofs/Proof.lean` (127 lines, 5,599 bytes) is kernel-checked proof code; `Proofs/Lifted.lean` (67 lines, 20,377 bytes) is generated and linked to the artifact. Their contents need not be assumed true on inspection. Their checks still rely on FVA's reviewed Wasm semantics and claims vocabulary (`fva/FVA/Spec/`: 23 Lean files, 3,606 physical lines, 161,903 bytes), its verified decoder/stepper and proofs, its trusted collection/link/export/replay/canary orchestration (`FVA/Trust/{Collect,Replay,Canary}.lean` and `FVA/Tool/Trust.lean`: four files, 1,036 lines, 50,676 bytes), the supplied toolchain and prebuilt checker, and the Lean kernel with independent kernel replay. Mathlib and its dependencies are pinned by the supplied Lake manifests. FVA's standard permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Wasmtime is an additional independent execution check, not part of the Lean proof's assumptions.
