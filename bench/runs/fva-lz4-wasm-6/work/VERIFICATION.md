All three README requirements fail on the shipped artifact. The counterexamples below are proved using FVA's WebAssembly semantics and independently reproduced with wasmtime. The artifact and its source have not been changed.

| Requirement | Result | Evidence |
|---|---|---|
| R1 | False | An encoder result violates both mandatory LZ4 end conditions. |
| R2 | False | A valid block for thirteen bytes returns one and writes only its first byte. |
| R3 | False | A valid one-byte empty block causes an out-of-block read, including an observable dependence on the following byte. |

The exact theorem declarations, all in `Proofs/Proof.lean`, are:

```lean
theorem preparation_holds : preparation
theorem r1_holds : r1
theorem r2_holds : r2
theorem r3_holds : r3
theorem r3_dependence_holds : r3_dependence
```

These names are in namespace `Proofs`. Their propositions and every project-specific definition they use are in `Proofs/Spec.lean`. `CallReturns` means every execution terminates with the specified results and memory observations, without trapping; `CallTraps` means every execution terminates in a trap. Each claim quantifies over every host semantics. `fresh` is the actual artifact's allocation in an empty store, and `preparation_holds` proves it is a fresh instance. Memory changes describe caller preparation, not changes to the Wasm code.

R1: initialize all 65,536 four-byte hash entries at address 0 to −65536, grow memory to five pages, and put ASCII `abcdeabcdWXYZ` (13 bytes) at 262144. Call `lz4BlockEncode(262144, 13, 262200)`. It returns 13 and writes:

```text
50 61 62 63 64 65 05 00 40 57 58 59 5a
```

The parse is unambiguous: token `50`, literals `abcde`, offset 5, match length 4, final token `40`, literals `WXYZ`. There are only four final literals, violating end condition 2 of `lz4_Block_format.md`. The last match starts at decoded position 5 in a 13-byte input, only eight bytes before the end, violating condition 3. This positive-length result refutes R1's validity conjunct; no assertion that every input fails to round-trip is needed.

The exact R1 proposition is:

```lean
def r1 : Prop :=
  (∀ H, CallReturns H encoderStore fresh.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 262200]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 262200 encoderOutput)) ∧
  ¬ endConditions 13 5 4
```

Here `encoderInput` and `encoderOutput` are the byte lists printed above, `encoderStore` contains the documented table and input, and `endConditions size start tail` is exactly `5 ≤ tail ∧ start + 12 ≤ size`. `preparation_holds` additionally checks every hash word, the input bytes, and the possibility of growing the fresh memory by four pages. The input, table, and output are disjoint and all buffers fit in memory.

R2: place this valid 13-byte compressed block at address 100 in a fresh one-page memory:

```text
10 41 01 00 80 42 43 44 45 46 47 48 49
```

Token `10` gives literal `A`, offset 1 and a four-byte overlapping match, producing five `A`s. Token `80` then gives eight literals `BCDEFGHI`. The decoded content is `AAAAABCDEFGHI`, length 13. The final eight bytes are literals and the match starts exactly twelve decoded bytes before the end. `shortValid` formalizes this two-sequence portion of the documented grammar, including the forward overlapping-copy rule and the end conditions; the theorem supplies and checks this validity certificate.

Call `lz4BlockDecode(100, 13, 0)`. It returns 1. Output memory at addresses 0 through 12 is `41` followed by twelve zeros, instead of the expected content. Input and output are disjoint and both have ample space. The exact R2 proposition is:

```lean
def r2 : Prop :=
  shortValid validBlock decodedContent ∧ decodedContent.length = 13 ∧
  ∀ H, CallReturns H (fresh.1.withBytes 100 validBlock) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 13, .i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 [65,0,0,0,0,0,0,0,0,0,0,0,0])
```

`validBlock` and `decodedContent` are the bytes described above. Inspection of the artifact identifies the address-dependent cause: it compares the match source in the output buffer against the end of the compressed input buffer and exits early. The counterexample requires no additional restriction on buffer order, since the README specifies none.

R3: the format document explicitly permits `[00]` as the valid encoding of empty content. Write it at address 65535 of a fresh one-page memory and call `lz4BlockDecode(65535, 1, 0)`. The entire supplied block is in bounds. The decoder nevertheless tries to read an offset at 65536 and traps; wasmtime reports a memory fault at `0x10000` in a memory of size `0x10000`. The exact trap theorem's proposition is:

```lean
def r3 : Prop :=
  ∀ H, CallTraps H (fresh.1.withBytes 65535 [0]) fresh.2 "lz4BlockDecode"
    [.i32 65535, .i32 1, .i32 0] (fun _ => True)
```

The theorem proves the trap outcome; identification of the particular faulting read is corroborated by the executable replay. A second theorem proves an observable out-of-block dependence even when all memory accesses fit in linear memory. Put `[00,00,00]` or `[00,01,00]` at address 100, but supply length **1** in both cases, so the supplied block is the same single byte `[00]`. Call `lz4BlockDecode(100, 1, 1000)`. Changing only address 101, outside the block `[100,101)`, changes the return value from 0 to 4:

```lean
def r3_dependence : Prop :=
  (∀ H, CallReturns H (fresh.1.withBytes 100 [0,0,0]) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 1, .i32 1000]
    (fun s vs => vs = [.i32 0] ∧ bytesAt s 1000 [0,0,0,0])) ∧
  (∀ H, CallReturns H (fresh.1.withBytes 100 [0,1,0]) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 1, .i32 1000]
    (fun s vs => vs = [.i32 4] ∧ bytesAt s 1000 [0,0,0,0]))
```

This dependence is a direct demonstration that decoding reads beyond its compressed input. It does not depend on an interpretation of legal match-copy reads from the output buffer. The empty-block examples also independently contradict R2.

The proofs concern exactly `lz4-block-codec.wasm`, 1,226 bytes, SHA-256:

```text
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

`Proofs/Lifted.lean` was generated by FVA from those bytes. It contains their packed numeral, the decoded module, and the kernel-checked `decode_eq` theorem. FVA checks that the numeral still matches the file and independently replays `decode_eq` along with the execution proofs. The proofs execute this decoded artifact using FVA's verified deterministic stepper and transfer the results to its relational `Must` semantics. There is no handwritten model of the codec and no assumption that the WAT source matches the binary. Kernel evaluation uses `decide +kernel`, without `sorry`, custom axioms, `native_decide`, or `bv_decide`.

Run every check from this directory, without network access:

```bash
bash verification/check.sh
```

The script runs `lake build`, executes `python3 verification/replay.py`, copies the supplied FVA package to a temporary directory, and rebuilds its verifier executable there using the installed dependencies. It then runs:

```text
<temporary external FVA> trust . --spec-module Proofs.Spec --root-module Proofs
```

This satisfies FVA's instruction to run a verifier built outside the project being judged. Only the external copy's package-location configuration and cached executable files are changed; FVA implementation sources remain unchanged. The temporary copy is removed on exit. To check just the kernel proofs or just the runtime demonstrations, run `lake build` or `python3 verification/replay.py`, respectively.

Success means the script exits 0, all five runtime cases print `counterexample confirmed`, and the final FVA verdict is `fva trust: PASS`. The complete trust report is saved to `verification/trust.txt`; PASS means the counterexample claims are proved, not that the codec satisfies the README. The build and runtime checks alone do not replace the independent kernel and artifact-link checks.

The project-specific review surface is `Proofs/Spec.lean`: 51 code lines by FVA’s count, 82 physical lines, 4,299 bytes. Review its constants, caller-prepared stores, memory observations, and the correspondence of `shortValid` and `endConditions` to `lz4_Block_format.md` (10,683 bytes). `shortValid` is a sufficient certificate for these small two-sequence blocks, not a claimed formalization or decision procedure for every LZ4 block. The R1 failure uses the mandatory end conditions directly. No universal encoder or decoder correctness theorem is asserted.

For the supplementary runtime evidence, read `verification/replay.py` (79 lines, 3,227 bytes), which checks the artifact hash, validates it, and generates wrappers that import the original module and memory. It checks return values and memory bytes, and checks the expected boundary trap. The orchestration script `verification/check.sh` is 31 lines, 1,168 bytes. Python, wasm-tools and wasmtime are trusted for this supplementary evidence; the Lean execution proofs do not rely on their results. `Proofs/Proof.lean` (135 lines, 4,960 bytes) and the generated lift (67 lines, 20,377 bytes) are checked by the kernels rather than trusted as handwritten assertions.

FVA's baseline trust remains its reviewed WebAssembly and claim specifications, verified decoder and execution machinery, trust collection/link/export orchestration, the Lean toolchain, installed Mathlib v4.35.0, and the independent kernels. FVA checks vendored base sources against its pinned hashes. Its report records the actual kernel replay outcomes, canary results, artifact link, permitted standard axioms, and code-line review count. The baseline specifications are under `fva/FVA/Spec/`; the other baseline layers are described in `fva/AGENT.md` and the report.

For scale, the supplied FVA baseline specification directory contains 23 Lean files, 3,606 physical lines and 161,903 bytes. Its trust-collection/replay directory contains 4 files, 887 lines and 40,918 bytes; the tool directory contains 13 files, 2,894 lines and 139,610 bytes (including tools unused by this verification). These baseline sizes are separate from FVA's project review-surface count. The installed executables used here report Lean 4.35.0, wasmtime 50.0.0 and wasm-tools 1.262.0.

The completed full check exited 0. `verification/trust.txt` records PASS for all five claims, acceptance by both `leanchecker` and `con-leche`, and a matching artifact link. The canary report includes one recorded known acceptance by `leanchecker`; con-leche accepted no known-false canary and declined three. These statuses are reported by FVA rather than described as universal rejection of every canary. The successful runtime outputs and complete command output are also retained in `verification/check.log`.
