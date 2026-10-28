# Verification report

**Partial verification. R1, R2, and R3 remain unproved in their full generality. No counterexample to them is established here.** The results below are machine-checked properties of the shipped WebAssembly artifact, with explicit limitations. An FVA PASS applies to the stated Lean claims; it does not mean all README requirements have been proved.

## Requirement coverage

| Requirement | Result | Remaining obligation |
| --- | --- | --- |
| R1: reads and writes stay within the permitted buffers | **Unproved.** `zeroCapacity_holds` and `emptyBlock_holds` prove equality of the final and initial stores in their stated domains. | Final-state equality does not establish an access footprint: a program could read elsewhere, or temporarily write and restore bytes. No theorem here bounds every intermediate access, including the decoder's copying shortcuts, malformed-input paths, and helper loops. |
| R2: every valid independent block decodes correctly | **Partially proved.** `zeroCapacity_holds` covers the empty-block exception for arbitrary pointers and memory, subject to its explicit premises. `emptyBlock_holds` covers an initialized instance. Four additional concrete valid blocks have the exact successful returns and output bytes listed below. | There is no mechanized general definition of LZ4 block validity or decoding here, and no simulation invariant relating all decoder iterations to that format. Extended lengths, all match offsets, all capacities and placements, and arbitrary sequence counts remain open. |
| R3: every nonnegative return has the permitted decoded interpretation | **Partially proved.** The zero-capacity branch succeeds exactly for size one and byte zero. The concrete zero-offset example produces seven zero bytes despite an initial destination filled with `A5`. | No universal converse from a successful execution to an LZ4 sequence decomposition is proved. The two allowed departures from the format have not been formalized generally. |

The gaps are proof obligations left unfinished, not evidence that the requirements are false. In particular, inspection of the C code and successful examples cannot replace the missing invariants and format correspondence.

## Exact machine-checked statements

All declarations below are in `Proofs/Proof.lean`; their exact named propositions and all supporting state definitions are in `Proofs/Spec.lean`:

```lean
theorem initialization_holds : initialization
theorem emptyBlock_holds : emptyBlock
theorem zeroCapacity_holds : zeroCapacity
theorem literalCase_holds : literalCase
theorem overlapCase_holds : overlapCase
theorem longMatchCase_holds : longMatchCase
theorem zeroOffsetCase_holds : zeroOffsetCase
theorem shortcutCase_holds : shortcutCase
theorem validModule_holds : validModule
```

All these names are in namespace `Proofs`. These are exact declaration types, with the following meanings; the specification file supplies their full expansions.

`initialization` is exactly:

```lean
∀ H, Instance Lifted.module H initialStore initialInst
```

`initialInst` is the artifact's allocated module instance. `initialStore` includes its global initialized to 65536, its 32-page memory, and its active 64-byte data segment copied to 65536 and dropped. The proof uses FVA's verified instantiator to establish that this explicitly described state really is a successful fresh instance, under every host semantics. It does not prove uniqueness of fresh instances.

`validModule` is exactly `FVA.Wasm.Valid.ModuleValid Lifted.module`. FVA's verified validator proves the WebAssembly typing judgment. This is an infrastructure result; it proves neither LZ4 correctness nor caller-buffer safety.

`emptyBlock` calls `LZ4_decompress_safe(131072, 196608, 1, 0)` after writing `[0]` at 131072 in `initialStore`. Under every host semantics, the call terminates, never traps, returns `[.i32 0]`, and its final store equals its pre-call store. The empty output needs no destination-byte assertion.

The general boundary theorem `zeroCapacity` is exactly:

```lean
∀ H (mem : MemInst) (src dst n : BitVec 32),
  src ≠ 0 → src.toNat < mem.size →
  CallReturns H (callerStore mem) initialInst "LZ4_decompress_safe"
    [.i32 src, .i32 dst, .i32 n, .i32 0]
    (fun s vs => s = callerStore mem ∧
      vs = [.i32 (if n = BitVec.ofNat 32 1 ∧ mem.byte src.toNat = 0
                  then 0 else -1)])
```

Here `callerStore mem` replaces memory 0 of `initialStore` with the arbitrary `MemInst mem`; functions and the other store fields retain their initialized values. Thus the theorem quantifies over arbitrary memory contents, sizes, destination pointers, and all source-size bit patterns. Its source-pointer premises are explicit, including the requirement that the first source byte be in memory even when `n ≠ 1`. The theorem is about this store family, not an unproved quantification over every fresh instance or arbitrary prior-call state. `-1` is the 32-bit two's-complement value `FFFFFFFF`.

Each concrete `*Case` proposition uses `caseStore input capacity`: begin with `initialStore`, fill the destination with `capacity` bytes of `A5`, then write the compressed input. It asserts, under every host semantics, a terminating, nontrapping `CallReturns` for `(src, dst, srcSize, dstCapacity) = (131072, 196608, input.length, capacity)`, with exactly the return value and complete output prefix below. Its postcondition is the result equality together with existence of memory 0 whose listed output bytes equal that prefix. These claims impose no assertion about other final bytes or intermediate accesses.

| Theorem | Compressed bytes (hex) | Capacity | Signed return | Output bytes |
| --- | --- | ---: | ---: | --- |
| `literalCase_holds` | `1041` | 1 | 1 | `41` (`A`) |
| `overlapCase_holds` | `13410100504243444546` | 13 | 13 | Eight `41` bytes followed by `4243444546` (`BCDEF`) |
| `longMatchCase_holds` | `1f41010001504243444546` | 26 | 26 | Twenty-one `41` bytes followed by `4243444546` |
| `zeroOffsetCase_holds` | `030000504243444546` | 12 | 12 | Seven `00` bytes followed by `4243444546` |
| `shortcutCase_holds` | `8341424344454647480800f0006162636465666768696a6b6c6d6e6f` | 64 | 30 | `4142434445464748414243444546476162636465666768696a6b6c6d6e6f` |

The literal, overlap, long-match and shortcut inputs illustrate R2. The zero-offset input illustrates the exception allowed by R3. Their classification against the English block-format document is a reviewer interpretation, not a separate machine-checked format-validity theorem. The exact artifact behavior and output bytes are machine-checked.

## Connection to the shipped bytes

The subject is the unchanged `lz4-c.wasm`, 8,469 bytes, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`Proofs/Lifted.lean` was generated by:

```sh
fva/.lake/build/bin/fva lift lz4-c.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

Its theorem `Proofs.Lifted.decode_eq : decode bytes len = .ok module` is kernel-checked. FVA's trust check compares the numeral and length to the actual file, requires the generated file to regenerate exactly, and includes `decode_eq` in independent replay. All claims above depend on this decoded module. There is no substitute C model or assumed source-to-binary compiler-correctness theorem. The C sources, build script, and shipped binary were not edited.

For concrete executions the proofs use kernel-evaluated `runDet` equalities and FVA's `must_returned_of_runDet`. The execution bounds (100 or 4000) occur only in proofs. The resulting `CallReturns` claims are total-correctness statements, not fuel-bounded testing statements. The universal zero-capacity proof uses FVA's symbolic stepping lemmas and case splits. The proofs use no `sorry`, custom axioms, `native_decide`, or `bv_decide`.

## Reproduction

From this directory, run:

```sh
./verify.sh
```

The script uses only the supplied files and built dependencies; it makes no network requests. It checks the README hash, runs `wasm-tools validate`, builds the Lean project, copies FVA into a fresh directory under `/tmp`, configures that copy to use the existing package cache, relinks its executable outside the project, runs its trust check, and runs the Wasmtime cross-check. The copy is removed on exit. The formal report is saved as `verification/FVA-REPORT.txt`.

Success requires all of the following:

- `lz4-c.wasm: OK` from the hash check; `wasm-tools validate` exits zero.
- `lake build` completes successfully, checking all theorems above.
- FVA prints **PASS**, all nine claims have proofs, the Wasm link checks succeed, and both `leanchecker` and the independent `con-leche` kernel accept the proof export. FVA also checks its pinned false-proof canaries.
- Wasmtime prints `0` and exits zero. The harness traps if any return or output comparison fails. Its CLI may also print an experimental `--invoke` warning.

Observed check results are saved in `verification/FVA-REPORT.txt`: **FVA PASS**, nine proved artifact-linked claims, and a matching Wasm link. `leanchecker` accepted the export in 327 seconds and independent `con-leche` in 239 seconds. Both checked the same exported dependency closure; `con-leche` reported acceptance of 14,532 declarations. The Lean build succeeded, the artifact hash and Wasm validation matched, and the Wasmtime harness returned `0`.

The canary verdict follows FVA's documented policy, rather than requiring every kernel to reject every canary: of 72 known-false exports, `leanchecker` rejected 71 and accepted one documented exception; `con-leche` rejected 69 and declined three, accepting none. Neither crashed nor timed out. The pinned exception policy is in `fva/trust/canaries/known.tsv`; this limitation is part of the trust report.

The principal commands, if inspecting the steps separately, are:

```sh
sha256sum lz4-c.wasm
wasm-tools validate lz4-c.wasm
lake build
# After the external FVA build performed by verify.sh:
/path/to/external/fva trust . --spec-module Proofs.Spec --root-module Proofs
XDG_CACHE_HOME=/tmp/lz4-wasmtime-cache \
  wasmtime run --preload lz4=lz4-c.wasm --invoke check checks.wat
```

`checks.wat` imports the unmodified shipped memory and decoder through Wasmtime's `--preload`. It checks the same five concrete outputs at disjoint buffer placements; it is an independent runtime cross-check, not additional formal proof or a counterexample.

## Review and trust

The project-specific semantic review surface is `Proofs/Spec.lean`: **98 physical lines, 5,893 bytes**. A reviewer must check that its state definitions, premises, and postconditions mean what this report describes. In particular, its claims deliberately cover only the subsets and examples stated above. FVA measures this as **58 non-comment code lines**, all in `Proofs.Spec`.

Other delivered files:

| File | Size | Role |
| --- | --- | --- |
| `Proofs/Proof.lean` | 130 lines, 6,586 bytes | Kernel-checked proofs; no additional semantic assumptions |
| `Proofs/Lifted.lean` | 67 lines, 135,649 bytes | Generated artifact encoding; protected by decoder, regeneration, and link checks |
| `Proofs.lean` | 1 line, 20 bytes | Imports the proof module |
| `checks.wat` | 58 lines, 3,644 bytes | Optional runtime cross-check; inspect it if relying on that runtime result |
| `verify.sh` | 43 lines, 1,536 bytes | Reproduction orchestration; inspect it or run its commands directly |

Beyond the project specification, the formal results rely on FVA's reviewed WebAssembly syntax, binary grammar, execution and instantiation semantics, integer semantics, validity judgment and claim vocabulary; its verified decoder, stepper, instantiator and validator; and its trust-checking glue, artifact-link checks and canary mechanism. The FVA specification tree has 3,606 physical lines. FVA treats its byte-identical pinned base separately from project review lines. All 3,192 originally supplied FVA files were checked against the initial workspace hash manifest and were unchanged when preparing this report.

Residual trust includes Lean 4.35.0, Mathlib v4.35.0 and its pinned dependencies, the proof exporters and external kernels (with their canaries), and the toolchain that built FVA. Wasmtime and `wasm-tools` are needed only for the additional runtime and validation checks. The English README and `lz4_Block_format.md` must be read to assess requirement coverage; no theorem here establishes that the nine propositions exhaust those requirements.
