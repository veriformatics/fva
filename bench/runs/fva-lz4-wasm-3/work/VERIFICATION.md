# Verification of the shipped LZ4 Wasm

**R1, R2, and R3 all fail.** The results below are machine-checked counterexample executions, not proofs that the requirements hold. The shipped software and requirements were not changed.

## Artifact and method

The subject is the original `lz4-block-codec.wasm`: **1,226 bytes**, SHA-256
`4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf`.

`Proofs/Lifted.lean` is the unedited output of FVA's lift command. It contains the exact packed bytes, their length and path, the decoded module, and the kernel-checked theorem

```lean
Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len =
    .ok Proofs.Lifted.module
```

FVA's artifact link check compares these bytes with the shipped file. All execution claims below refer to this decoded module through `fresh`; they are not proofs about the WAT source or a reimplementation of the codec.

`Proofs/Proof.lean` uses the verified FVA deterministic interpreter and `runDet_must` to prove the claims in `Proofs/Spec.lean`. The resulting statements quantify over every host semantics and assert termination with the specified result (or trap). The interpreter's finite fuel is used only to construct the proofs; none of the public claims has a fuel assumption. `r1_holds` also proves that `fresh` is an actual fresh instance under every host semantics. All other witnesses use that same instance.

There is no full formalization of the prose LZ4 format here. The kernel checks the artifact's execution facts. The explicit token parses below connect those facts to `lz4_Block_format.md`; that short interpretation of the supplied format remains a reviewer obligation. The Wasmtime reproduction also checks the witness format arithmetic with Python assertions.

The completed external FVA audit is saved in `verification/fva-trust.json`: **PASS**, no issues, all four claims attached to `Proofs.Lifted`, and **34 code lines** in the sole project review module, `Proofs.Spec`. Both `leanchecker` and the independent `con-leche` accepted the proof export, including `decode_eq`. The artifact's length, bytes, regeneration and decoding link checks all passed. The only proof axioms reported are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The documented `check_fva.sh` command was also run end to end and passed; its output is saved in `verification/fva-trust.txt` (Lean replay 134 seconds; independent replay 103 seconds).

The audit ran 72 known-false canaries per kernel: `leanchecker` rejected 71 and accepted the pinned known exception `prelude-15704/replaced-prelude`; `con-leche` rejected 69 and declined three unsupported cases. Neither crashed or timed out. FVA explicitly guards the known prelude exception with its prelude check and independent replay; this report does not claim that every canary was rejected by every kernel. The JSON records each outcome.

## R1 — invalid encoder output

Exact theorem in `Proofs/Proof.lean`:

```lean
theorem Proofs.r1_holds : Proofs.r1
```

The exact claim body in `Proofs/Spec.lean`, with its namespace open as in that file, is:

```lean
def r1 : Prop :=
  (∀ H, Instance Lifted.module H fresh.1 fresh.2) ∧
  (∀ H, CallReturns H encoderStore fresh.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 262200]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 262200 13 = some encoderOutput))
```

`fresh = allocModule {} Lifted.module [] [] []`. `encoderStore` grows its memory by four pages, initializes all 65,536 table words to −65536 (little-endian `00 00 ff ff`), and writes ASCII `abcdXabcd1234` at 262144, immediately after the table. The output starts at 262200, disjoint from the table and input, with ample capacity in the five-page memory. This meets the README's caller preparation rules.

The encoder returns **13**, with the exact bytes:

```text
50 61 62 63 64 58 05 00 40 31 32 33 34
```

These parse unambiguously as:

- Token `50`: five literal bytes `abcdX`, then offset `05 00` and match length 4. The match starts at decoded position 5.
- Token `40`: four final literals `1234`.

The decoded length under the sequence rules is 13. The final literal count is **4 < 5**, and the last match starts **13 − 5 = 8 < 12** bytes before the end. Both violate the mandatory “End of block conditions” in the supplied format. Thus R1's validity conjunct fails. No general round-trip claim is proved or needed to refute the conjunction.

## R2 — incorrect decoding of a valid block

Exact theorem in `Proofs/Proof.lean`:

```lean
theorem Proofs.r2_holds : Proofs.r2
```

Exact claim body in `Proofs/Spec.lean`:

```lean
def r2 : Prop :=
  ∀ H, CallReturns H (fresh.1.withBytes 100 validBlock) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 10, .i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 13 = some (65 :: List.replicate 12 0))
```

`validBlock` is:

```text
13 41 01 00 50 42 43 44 45 46
```

Token `13` supplies one literal `A`, offset 1, and match length **3 + 4 = 7**. Forward overlap copying therefore yields eight `A`s. Token `50` supplies the five final literals `BCDEF`. The required content is **`AAAAAAAABCDEF`**, length **13**. The block ends after its literals, has five final literals, and its last match starts at decoded position 1, exactly 12 bytes before the end. It is a valid independent block.

The artifact instead returns **1**. The theorem also checks all 13 output bytes: `41` followed by twelve zero bytes. Input `[100,110)` and the output buffer at 0 are disjoint and fit in the original one-page memory.

The decoded instructions explain the defect: the decoder compares the match source address to the *compressed input end*. Here the valid match source is 0, which is below 110, so it exits early. R2 does not restrict the relative ordering of the two buffers.

## R3 — reads beyond the declared block

Exact theorem in `Proofs/Proof.lean`:

```lean
theorem Proofs.r3_holds : Proofs.r3
```

Exact claim body in `Proofs/Spec.lean`:

```lean
def r3 : Prop :=
  (∀ H, CallReturns H (fresh.1.withBytes 0 [0, 0, 0]) fresh.2 "lz4BlockDecode"
    [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 0])) ∧
  (∀ H, CallReturns H (fresh.1.withBytes 0 [0, 1, 0]) fresh.2 "lz4BlockDecode"
    [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 4]))
```

Both calls declare the **same one-byte block `00`**, input 0, **n = 1**, output 1024. The format explicitly permits `00` as the empty block. The caller's larger write initializes surrounding memory; it does not enlarge the block passed to the decoder.

Only byte **1**, outside `[0,1)`, differs between the initial memories. The return changes from **0 to 4**. The decoder treats bytes 1 and 2 as an offset even though the final token had no literals and no offset. This is a successful out-of-block read affecting the result, not merely a potentially invalid address. Both calls finish without a Wasm memory trap. The second result also independently violates R2 for the empty block.

## Additional empty-block trap (R2 and R3)

Exact theorem in `Proofs/Proof.lean`:

```lean
theorem Proofs.emptyBlockTrap_holds : Proofs.emptyBlockTrap
```

Exact claim body in `Proofs/Spec.lean`:

```lean
def emptyBlockTrap : Prop :=
  ∀ H, CallTraps H (fresh.1.withBytes 65535 [0]) fresh.2 "lz4BlockDecode"
    [.i32 65535, .i32 1, .i32 0] (fun _ => True)
```

The valid block `00` occupies `[65535,65536)`, entirely inside the original one-page memory. No output capacity is needed for its empty decoded content. Instead of returning 0, the decoder traps while trying to load an offset byte at address **65536**. The theorem proves the trap outcome; the location and cause follow from the decoded load instructions and are also reproduced by Wasmtime. The preceding R3 witness already establishes a successful outside read without relying on how a trapping access is classified.

## Reproduce from this directory

No network or dependency downloads are needed in the supplied environment.

```sh
sha256sum lz4-block-codec.wasm
wasm-tools validate lz4-block-codec.wasm
lake build
bash verification/check_fva.sh
python3 verification/check_wasmtime.py
```

Success means:

1. SHA-256 equals the value above; `wasm-tools validate` exits 0.
2. `lake build` exits 0 and prints `Build completed successfully`.
3. The FVA script exits 0 and reports **`fva trust: PASS`**, with all four counterexample claims proved, an exact artifact link, and accepted independent kernel replays. This PASS certifies the counterexample proofs, **not** satisfaction of R1–R3.
4. The Wasmtime script exits 0 and prints `PASS: R1 invalid encoder output; R2 short decode; R3 outside-byte dependence; empty-block trap`.

`check_fva.sh` copies the supplied prebuilt FVA package to a temporary directory outside the judged project, checks the checker binary's SHA-256 (`5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407`), points its Lake configuration and manifest at the already installed packages, builds it there, and invokes `trust` with `--surface-budget 100`. The original FVA files remain unchanged. The temporary directory is removed on exit.

To regenerate the lift, if desired (this should reproduce the same file):

```sh
lake exe fva lift lz4-block-codec.wasm Proofs/Lifted.lean --ns Proofs.Lifted
lake build
```

The independent runtime script embeds the original binary verbatim in a temporary WAST script. A separate wrapper module imports its exports and memory, prepares the witnesses, and asserts return values and bytes. The final trap uses a separate fresh instance with one page. It never recompiles the WAT or modifies the shipped module.

## Review and trust

The project-specific reviewed definitions are **`Proofs/Spec.lean`: 71 lines, 3,657 bytes** (including documentation and blank lines). Read its preparation of memory, byte observations, concrete arguments and postconditions together with the token parses in this report. The supplied requirements are `README.md` (18 lines, 1,798 bytes); the supplied format is `lz4_Block_format.md` (244 lines, 10,683 bytes).

The proof file is **97 lines, 4,135 bytes**; its statements and proofs are kernel-checked, so its tactics and execution helpers need not be trusted as an alternate codec semantics. The generated lift is **67 lines, 20,377 bytes**; its byte binding and decoding theorem are checked rather than accepted as assumptions.

FVA's shared base remains a trust boundary: its Wasm and binary-format specifications, execution and numeric semantics, claim definitions and verdict rules (`fva/FVA/Spec/**/*.lean`, **3,606 lines, 161,903 bytes**); its checked implementation/proof library; and its collection/link/replay orchestration. For size context, `FVA/Trust/{Collect,Replay,Canary,Verdict}.lean` and `FVA/Tool/{Trust,BaseManifest,Lift}.lean` together have **1,676 lines, 81,814 bytes**. These files were not edited. FVA compares imported base sources against its pinned manifest. A reviewer must accept that FVA's formal semantics describe the relevant Wasm instructions, and that its trust orchestration correctly connects the files, declarations and replay processes.

Residual trust includes Lean 4.35.0's kernel and compiler, the independent replay kernel, pinned Mathlib v4.35.0 and dependencies, and the filesystem/hash/tool execution infrastructure. No `sorry`, custom axioms, `native_decide`, or `bv_decide` are used in the project proofs. Wasmtime 50.0.0 supplies independent operational corroboration, not the Lean proof semantics.

The reproduction scripts are `verification/check_fva.sh` (**28 lines, 1,234 bytes**) and `verification/check_wasmtime.py` (**84 lines, 3,793 bytes**). They must be read if relying on their orchestration or runtime demonstration. Their sizes exclude any generated temporary WAST; that WAST contains the unchanged binary twice and the wrapper/assertions generated by the Python script. The machine-checked Lean execution results do not depend on Python's codec arithmetic or on Wasmtime.
