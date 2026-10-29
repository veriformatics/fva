# Verification of lz4-flex.wasm

**Status: incomplete. R1, R2 and R3 remain unproved; no counterexample was found.** The results below are narrower, machine-checked facts about the actual WebAssembly artifact, plus explicitly identified runtime tests. They do not establish that all README requirements hold.

## Artifact and proof connection

The subject is the unchanged `lz4-flex.wasm`: 7,161 bytes, SHA-256
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.

`Proofs/Lifted.lean` was generated with:

```sh
lake exe fva lift lz4-flex.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

Its `Proofs.Lifted.decode_eq` proves that FVA's decoder applied to the embedded byte numeral gives `Proofs.Lifted.module`. FVA's trust audit also compares the numeral and generated file with the on-disk artifact. Decoder proofs execute function 7 of this module. The Rust source is neither substituted for the module nor assumed to have compiled correctly. No decoder or artifact modification was made.

`Proofs/Initialization.lean` proves that FVA's reference instantiator succeeds, and uses `instantiate_sound` to obtain a genuine `Instance` under every host semantics. Replay proofs then use `runDet` and `must_returned_of_runDet`, so their conclusions assert termination and no traps for every semantic execution from the selected initial state, rather than merely the existence of an interpreter trace. Fuel is only a proof-search bound; it does not appear in the claimed execution semantics. No `sorry`, custom axioms, `native_decide`, or `bv_decide` are used.

## Requirement results

| Requirement | Verdict | Evidence and remaining obligation |
| --- | --- | --- |
| R1: caller-buffer read/write confinement for arbitrary input | **Unproved** | `emptyInputPreservesStore_holds` proves an unchanged final store for zero input length. It does not specify an access trace, so it does not prove read confinement or exclude transient writes. Runtime canaries cover sampled writes only. No general invariant proving confinement through the decoder's slow and optimized copy paths was completed. |
| R2: all valid independent blocks decode correctly when capacity suffices | **Unproved** | The `emptyBlock`, `literalBlock`, and `overlappingBlock` cases prove exact returns and output bytes on three concrete inputs. They do not quantify over all valid blocks, pointers, capacities, or caller memory. A formal general LZ4 decoding relation, its equivalence to the supplied format, and a decoder loop invariant remain necessary. |
| R3: every nonnegative return implies a valid sequence decomposition and the correct content | **Unproved** | Concrete rejection results cover offset zero, an offset beyond the decoded prefix, insufficient capacity, and a truncated extension. Runtime tests compare successful returns against an independent sequence parser. No general soundness theorem relating every successful artifact execution to such a decomposition was completed. |

None of these open obligations is a demonstrated defect. In particular, passing tests, Wasm type validity, and a trust PASS for narrower claims must not be interpreted as a proof of R1–R3.

## Exact machine-checked statements

The reviewed statements are the definitions in `Proofs/Spec.lean`. These are the exact top-level theorem types (in namespace `Proofs`):

```lean
theorem artifactLayout_holds : artifactLayout
theorem wasmValid_holds : wasmValid
theorem emptyInputPreservesStore_holds : emptyInputPreservesStore
theorem emptyBlock_holds : emptyBlock
theorem literalBlock_holds : literalBlock
theorem overlappingBlock_holds : overlappingBlock
theorem zeroOffset_holds : zeroOffset
theorem excessiveOffset_holds : excessiveOffset
theorem insufficientCapacity_holds : insufficientCapacity
theorem truncatedLength_holds : truncatedLength
```

The first three are in `Proofs/Proof.lean`; each remaining theorem is in the correspondingly named file, e.g. `Proofs/EmptyBlock.lean`. `Proofs.lean` imports all of them.

`artifactLayout` states that imports are empty, the sole memory has minimum and maximum 32 pages, exports are `memory` at memory 0, `lz4_compress` at function 6 and `lz4_decompress` at function 7, function 7 equals `Lifted.func7`, and its signature is four `i32` parameters and one `i32` result. `wasmValid` is exactly `FVA.Wasm.Valid.ModuleValid Lifted.module`; it is proved using FVA's verified validator. Neither is a proof of the LZ4 requirements.

`emptyInputPreservesStore` is exactly:

```lean
∀ (H : HostSem) (s : Store) (inst : ModuleInst) (src dst cap : BitVec 32),
  s.funcs[7]? = some (.wasm
    ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7) →
  Must H (fun
    | .returned s' vs => s' = s ∧ vs = [.i32 (-1)]
    | .trapped _ => False)
    (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap])
```

This is conditional on the explicit binding of the actual artifact code in the store; it applies even to arbitrary stores, pointers and capacities, without relying on an empty-buffer bounds premise.

Each concrete case has the exact type `Replay input cap result output`, with all byte lists written in decimal:

| Claim | Input | Capacity | Return | Output prefix |
| --- | --- | ---: | ---: | --- |
| `emptyBlock` | `[0]` | 0 | 0 | `[]` |
| `literalBlock` | `[80,65,66,67,68,69]` | 5 | 5 | `[65,66,67,68,69]` |
| `overlappingBlock` | `[19,65,1,0,80,66,67,68,69,70]` | 13 | 13 | `[65,65,65,65,65,65,65,65,66,67,68,69,70]` |
| `zeroOffset` | `[16,65,0,0,80,66,67,68,69,70]` | 13 | -1 | `[]` |
| `excessiveOffset` | `[16,65,2,0,80,66,67,68,69,70]` | 13 | -1 | `[]` |
| `insufficientCapacity` | `[80,65,66,67,68,69]` | 4 | -1 | `[]` |
| `truncatedLength` | `[240,255]` | 64 | -1 | `[]` |

`Replay` expands to:

```lean
∀ H, ∃ s inst, Instance Lifted.module H s inst ∧
  Fits s 131072 input.length ∧ Fits s 1048576 cap ∧
  CallReturns H (s.withBytes 131072 input) inst "lz4_decompress"
    [.i32 131072, .i32 1048576, .i32 (BitVec.ofNat 32 input.length),
     .i32 (BitVec.ofNat 32 cap)]
    (fun s' vs => vs = [.i32 result] ∧ ∃ mem, s'.mems[0]? = some mem ∧
      (List.range output.length).map (fun k => mem.byte (1048576 + k)) = output)
```

Thus it chooses an initialized instance under every host semantics, writes the source bytes at 131072, and calls the actual export with destination 1048576. All listed buffers are disjoint and within the README region. It does **not** quantify over every fresh instance or arbitrary initial destination bytes. An empty output observation on error imposes no condition on partial output writes. The labels “valid” and “invalid” in the case explanations are checked against the supplied format by reading the listed bytes; these theorems prove the execution observations, not a separately formalized general LZ4 grammar.

## Runtime search

`verification/search.mjs` checks the original bytes with Node's WebAssembly engine. It enumerates every 0-, 1-, and 2-byte input at capacities 0, 4, 34, and 80; then generates 20,000 deterministic valid blocks, tests tight and excess capacities and memory-boundary layouts, and tests mutations/truncations. Successful returns are compared with a separate LZ4 sequence parser that permits relaxed end conditions for R3. It checks source preservation and 32-byte destination canaries.

Observed result:

```text
PASS 343169 original-artifact calls; 61972 nonnegative returns agree with independent parser.
```

These tests found no counterexample. They are not exhaustive over the README domain, do not observe reads or transient writes, and canaries cannot detect stores that write the original byte value. They are not Lean proofs. The generated valid corpus uses a final literal sequence of at least 12 bytes after matches, which satisfies the specified end restrictions.

## Reproduction

From this directory, with the installed offline toolchain and dependencies:

```sh
bash verification/check.sh
```

The script checks the pinned SHA-256, validates the binary with `wasm-tools`, builds each concrete proof sequentially to limit memory use, builds the full project, rebuilds FVA's executable in a temporary directory outside the project, runs `fva trust . --spec-module Proofs.Spec --root-module Proofs`, and runs the runtime search. It uses only local files. Success requires exit status 0, successful Lean builds, `fva trust: PASS` with matching artifact links and accepted independent kernel replays, and the runtime PASS count above. The FVA PASS refers only to the ten explicitly listed claims.

For an already-built project, the independent verifier used during this verification can also be run as:

```sh
/tmp/fva-verifier/.lake/build/bin/fva trust . --spec-module Proofs.Spec --root-module Proofs
node verification/search.mjs
```

The temporary verifier is recreated by `verification/check.sh`; the fixed `/tmp/fva-verifier` path is not needed for reproducibility.

## Review and trust surface

Read `Proofs/Spec.lean` for the actual meaning and limits of all claims, together with this report, `README.md`, and `lz4_Block_format.md`. FVA excludes generated lifted code and proof implementation from the manual statement-review surface because the bytes, decoder equality, axiom closure and proof exports are checked mechanically. The execution helper and its soundness proof are in `Proofs/ReplayCore.lean`; initialization and concrete proof files are also kernel checked.

The runtime results additionally trust Node's WebAssembly implementation, `verification/search.mjs`, its parser/generator and assertions. `verification/check.sh` is reproduction orchestration, not part of the LZ4 semantics. Artifact identification additionally uses SHA-256 and the trusted FVA link checker.

FVA's residual trust is its reviewed WebAssembly semantics, binary grammar, claim definitions and validity judgment; its trust-audit/export/process glue; the installed Lean compiler and kernel; Mathlib v4.35.0 and dependencies; and the independent replay kernel. This verifies FVA's core WebAssembly profile, rather than proving agreement of every installed WebAssembly engine with that profile. The vendored FVA sources were not edited. Their recognized files must match the base manifest compiled into the external verifier.

Source sizes (physical lines, including comments and blanks; FVA's code-line count is reported separately by the audit):

| Material | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Spec.lean` | 76 | 3,828 | Manual statement review |
| `README.md` | 18 | 2,402 | Requested requirements |
| `lz4_Block_format.md` | 244 | 10,683 | Required format interpretation |
| `verification/search.mjs` | 42 | 3,327 | Trust only for the runtime-test evidence |
| `verification/check.sh` | 20 | 879 | Reproduction orchestration |
| `Proofs/Lifted.lean` | 82 | 97,882 | Generated, checked against artifact bytes |
| Project proof sources, excluding Spec and Lifted | 204 | 7,402 | Kernel checked; 12 files including import aggregators |
| FVA reviewed specifications, `fva/FVA/Spec/**/*.lean` | 3,606 | 161,903 | Reviewed-once semantic base; 23 files |
| All supplied FVA Lean sources | 24,215 | 1,106,254 | 129 files, including specification, proofs, implementation and tool glue |

The FVA source total is not an additional manual proof-review requirement: the audit identifies byte-identical base files, checks proof axiom closures, and independently replays the exported proof closure. It remains necessary to trust the intended interpretation of the reviewed base and the toolchain/glue listed above. `VERIFICATION.md` is an explanatory report, not an input to the proof checker.

## Recorded audit result

`bash verification/check.sh` completed with exit status **0**. The complete output is saved in `verification/check.log` (169 lines, 9,270 bytes).

- **FVA verdict: PASS**, for the ten scoped claims listed above.
- Independent replay: `leanchecker` accepted in 663 seconds; `con-leche` accepted in 516 seconds.
- Artifact link: `Proofs.Lifted (lz4-flex.wasm) [lifted]: matches`.
- FVA's project review surface: **44 code lines**, all in `Proofs.Spec` (76 physical lines).
- Proof axiom closures contain only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with some claims using fewer.
- The 72 known-false canaries produced: Lean checker, 71 rejected and one documented acceptance; independent checker, 69 rejected and three declined, with none accepted. Neither checker crashed or timed out. The documented Lean acceptance is the replaced-prelude canary in `fva/trust/canaries/known.tsv`: FVA's prelude-origin check and independent kernel guard that assumption. These are the actual audit results, not a claim that every checker rejected every canary.
- The runtime search again passed **343,169** calls, including **61,972** nonnegative returns agreeing with the independent parser.

This successful scoped audit leaves the R1, R2 and R3 verdicts **unproved**, as stated at the beginning of this report.
