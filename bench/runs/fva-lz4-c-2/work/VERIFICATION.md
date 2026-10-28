Verification status: **incomplete**. The results below are machine-checked partial coverage of the shipped artifact. None of README's three universal requirements has been fully proved or refuted. No counterexample to R1, R2, or R3 was established. A PASS for the restricted claims in `Proofs/Spec.lean` must not be interpreted as a PASS for R1–R3.

1. Requirement-by-requirement results

| Requirement | Result and remaining obligation |
| --- | --- |
| R1 | **Unproved.** The seven `DecodeCase` results establish final equality of the two bytes immediately adjacent to the destination. They do not establish absence of out-of-range reads, absence of intermediate writes, or preservation of every other address. No access-trace invariant covering every load/store and every loop iteration was proved. There is no R1 theorem. |
| R2 | **Partially checked; universal statement unproved.** Six concrete valid-block/capacity pairs have total-correctness proofs, including empty output, literals, overlapping matches, and length extensions. The empty block at zero capacity is also covered by a theorem quantifying over every possible one-byte input. These results do not cover every valid block, every capacity, or every allowed buffer placement. A formal LZ4 grammar and its general correspondence to the artifact's loops have not been established. |
| R3 | **Partially checked; universal statement unproved.** The offset-zero example proves the specified zero-filled content despite a destination prefilled with 0xA5. Empty-source rejection and all one-byte inputs at zero capacity are proved. There is no proof characterizing all nonnegative returns, all accepted sequence decompositions, or their offsets and output contents. |

The exact statements of the nine coverage theorems are:

```lean
-- Proofs/Proof.lean, inside namespace Proofs:
theorem emptyBlock_holds : emptyBlock
theorem emptyBlockPositive_holds : emptyBlockPositive
theorem literalBlock_holds : literalBlock
theorem overlappingMatch_holds : overlappingMatch
theorem extendedLiterals_holds : extendedLiterals
theorem extendedMatch_holds : extendedMatch
theorem zeroOffset_holds : zeroOffset

-- Proofs/Boundary.lean, inside namespace Proofs:
theorem emptySource_holds : emptySource
theorem zeroCapacityByte_holds : zeroCapacityByte
```

These names abbreviate the exact propositions in [Proofs/Spec.lean](Proofs/Spec.lean). In particular, `DecodeCase input output capacity` asserts existence of a fresh instance with sufficient memory, and, for **every** host semantics and every fresh instance with sufficient memory, total correctness of this call:

```lean
CallReturns H
  ((s.withBytes 196608 (List.replicate capacity 165)).withBytes 131072 input)
  inst "LZ4_decompress_safe"
  [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
    .i32 (BitVec.ofNat 32 capacity)]
  (fun s' vs => vs = [.i32 (BitVec.ofNat 32 output.length)] ∧
    ∃ before after, s.mems[0]? = some before ∧ s'.mems[0]? = some after ∧
      (∀ k : Fin output.length, after.byte (196608 + k.val) = output[k.val]) ∧
      after.byte 196607 = before.byte 196607 ∧
      after.byte (196608 + capacity) = before.byte (196608 + capacity))
```

`CallReturns` means every execution terminates with the specified result and memory postcondition, and none traps. It is FVA's semantic proposition, not a test with a time limit. The source starts at 131072 and the destination at 196608. These fixed buffers are disjoint and in the caller's permitted region. The caller writes only the stated input and the destination fill; arbitrary other caller memory modifications are outside these claims. Equality of adjacent bytes is a final-state observation, not a proof that no access occurred there.

The checked `DecodeCase` arguments are below. Input bytes are hexadecimal; output uses ASCII notation where indicated. The Lean definitions contain the explicit byte lists.

| Claim | Input bytes | Expected output | Capacity |
| --- | --- | --- | ---: |
| `emptyBlock` | `00` | empty | 0 |
| `emptyBlockPositive` | `00` | empty | 1 |
| `literalBlock` | `50 41 42 43 44 45` | `ABCDE` | 5 |
| `overlappingMatch` | `13 41 01 00 50 42 43 44 45 46` | eight `A`s, then `BCDEF` | 13 |
| `extendedLiterals` | `f0 00 41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f` | `ABCDEFGHIJKLMNO` | 15 |
| `extendedMatch` | `1f 41 01 00 00 50 42 43 44 45 46` | twenty `A`s, then `BCDEF` | 25 |
| `zeroOffset` | `03 00 00 50 41 42 43 44 45` | seven zero bytes, then `ABCDE` | 12 |

The first six pairs illustrate R2. `zeroOffset` illustrates R3's offset-zero allowance; its input is invalid under the strict format. Interpreting these concrete pairs against `lz4_Block_format.md` is a human review step: there is no separately verified format parser here.

The two boundary propositions, exactly as defined in the spec, are:

```lean
def emptySource : Prop :=
  Returns Lifted.module "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 0, .i32 1] [.i32 4294967295]

def zeroCapacityByte : Prop := ∀ b : UInt8,
  ReturnsAfterWrite Lifted.module 131072 [b] "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 1, .i32 0]
    [.i32 (if b = 0 then 0 else 4294967295)]
```

The i32 bit pattern 4294967295 is signed -1. `zeroCapacityByte_holds` quantifies over all 256 bytes; it is not an extrapolation from a few examples.

2. Connection to the shipped artifact

All nine coverage claims mention `Proofs.Lifted.module`. [Proofs/Lifted.lean](Proofs/Lifted.lean) was generated with:

```sh
fva/.lake/build/bin/fva lift lz4-c.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

Its packed byte numeral contains exactly **8,469 bytes**, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

The exact bridge theorem is `Proofs.Lifted.decode_eq : FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len = Except.ok Proofs.Lifted.module`. The Lean kernel checks decoding, and `fva trust` checks that the generated source and byte numeral match the actual file. No source-language model, recompilation, or C-to-Wasm compiler-correctness assumption connects these results to the artifact. `src/lz4.c`, its helpers, and the `.wasm` were not changed.

[Proofs/Startup.lean](Proofs/Startup.lean) additionally proves the following exact statements inside namespace `Proofs`:

```lean
theorem initialized_instance (H : HostSem) :
  Instance Lifted.module H initialized.store allocated.2

theorem instance_unique {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Lifted.module H s inst) :
  s = initialized.store ∧ inst = allocated.2
```

These establish that the universal fresh-instance clauses are inhabited and identify every possible fresh instance. Initialization is checked against FVA semantics, including the global initializer and the 64-byte active data segment. `Proofs/Proof.lean` uses kernel-evaluated deterministic execution and FVA's soundness theorem to obtain total correctness; `Proofs/Boundary.lean` uses FVA symbolic execution. The fuel 5000 in the concrete proof implementation does not appear in any coverage claim: a successful deterministic run proves termination under the relational semantics.

3. Reproduction

From this directory, with the supplied offline Lean/Mathlib/FVA environment:

```sh
bash checks/verify.sh
lake env lean checks/Theorems.lean
```

The first command checks the byte length/hash, runs the Wasmtime examples, validates the Wasm file, builds all proofs, creates a separate temporary FVA package outside this project, relinks its checker executable, and runs its `trust` command. It copies the supplied unmodified FVA sources/build products/canaries and redirects only its dependency configuration to the already installed packages. It uses no network and removes its temporary checker afterward. `checks/fva-trust.txt` records the trust report. A clean proof rebuild can take several minutes.

Success requires exit status 0, the Wasmtime message `7 decode cases, 256 one-byte zero-capacity cases, and empty-source rejection passed`, a successful Lake build, and `fva trust: PASS`. The trust report must list all nine claims, the artifact link marked `matches`, and accepted replays by both `leanchecker` and `con-leche`, with their canaries checked. The second command must exit 0 and print the declared theorem types. A partial-coverage PASS does not close the unproved obligations in the first table.

The supplementary Wasmtime assertions can be repeated independently:

```sh
python3 checks/run_examples.py
```

They run the exact artifact bytes in WAST and check all seven outputs and adjacent bytes, all 256 one-byte zero-capacity results, and empty-source rejection (264 decoder calls). These are runtime checks, not universal proofs. Their guard bytes are filled with 0xA5 and cases share an instance, giving an additional state setup beyond the formal fresh-instance cases.

4. Review and trust

Observed result: **`fva trust: PASS`** for all nine restricted claims. `leanchecker` accepted the export in 480 seconds and the independent `con-leche` kernel accepted it in 326 seconds. The link `Proofs.Lifted (lz4-c.wasm) [lifted]: matches` passed. The report lists only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for each theorem.

FVA checked its 72 known-false canaries under its documented policy: `leanchecker` rejected 71 and accepted one; `con-leche` rejected 69, declined three, and accepted none. No canary crashed or timed out. The acceptance is covered by FVA's shipped `trust/canaries/known.tsv` policy and rejection by another kernel; this is not a claim that each kernel individually rejected every canary. No canary set, policy, or FVA source was changed for this verification.

The reported project review surface is **42 code lines**, all in `Proofs.Spec`. Including comments and blank lines, the proposition definitions occupy **Proofs/Spec.lean: 72 lines, 3,561 bytes**. Read its quantifiers, buffer setup, postconditions, and literal test vectors against README and the format document. FVA's reported review surface and replay outcome are recorded in `checks/fva-trust.txt`.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `README.md` | 18 | 2,872 | Intended requirements |
| `lz4_Block_format.md` | 244 | 10,683 | Format used to interpret the examples |
| `Proofs/Spec.lean` | 72 | 3,561 | Reviewed proposition definitions |
| `Proofs/Startup.lean` | 97 | 3,489 | Kernel-checked initialization proofs and witnesses |
| `Proofs/Proof.lean` | 150 | 6,718 | Kernel-checked seven decode proofs |
| `Proofs/Boundary.lean` | 97 | 4,717 | Kernel-checked boundary proofs |
| `Proofs/Lifted.lean` | 67 | 135,649 | Generated byte binding and decoded artifact |
| `Proofs.lean` | 2 | 43 | Imports all proofs |
| `checks/verify.sh` | 27 | 1,086 | Reproduction/checker orchestration |
| `checks/Theorems.lean` | 14 | 422 | Prints exact theorem types |
| `checks/run_examples.py` | 36 | 2,360 | Supplementary runtime-check generator |

The proof implementations and generated lifting are checked, rather than assumed correct. The scripts need inspection to interpret their runtime checks and reproduce the independent checker invocation; they are not axioms used by the Lean proofs. No `sorry`, `admit`, custom axiom, `native_decide`, or `bv_decide` is used in the project proofs.

The reviewed-once FVA specification base (`fva/FVA/Spec/**/*.lean`) contains 23 files, 3,606 lines, 161,903 bytes. The FVA trust glue in `fva/FVA/Trust/*.lean` contains 4 files, 887 lines, 40,918 bytes; `fva/FVA/Tool/Trust.lean` adds 309 lines, 16,031 bytes. The lifting/packing support (`fva/FVA/Lifted.lean`, `fva/FVA/Tool/Lift.lean`, `fva/FVA/Tool/Pack.lean`) totals 295 lines, 14,539 bytes. These are supplied FVA components, not new project specifications. The printer's output is additionally checked by the decoding theorem and byte-link checks.

Residual trust is the supplied FVA specification of Wasm and C-ABI claims, FVA's byte-link/fact-collection/export/process glue, the supplied Lean toolchain and pinned Mathlib, and the independently replaying kernels. The FVA implementation/proof closure is replayed; FVA's specs must still accurately express Wasm behavior. Wasmtime and wasm-tools are trusted only for the supplementary runtime and validation observations. These results say nothing universal about the compressor, which README excludes.
