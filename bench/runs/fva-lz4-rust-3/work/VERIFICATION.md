**Result: partial verification. R1, R2, and R3 remain unproved in their full stated scope. No counterexample to any of them was established.** The delivered Lean proofs establish 19 narrower claims about the shipped binary: existence of an initialized instance, behavior on zero-length input, and 17 specified calls. A passing audit of these claims must not be interpreted as a proof of all README requirements.

**Requirements and outstanding obligations**

| Requirement | Machine-checked result delivered | What remains unproved, and why |
| --- | --- | --- |
| R1 | Each of the 17 `Sample` theorems proves the read/write address restriction at **every reachable Wasm configuration** of that call. This includes bulk operations, wide loads/stores, and intermediate states, rather than merely comparing final memory. | Arbitrary compressed bytes, lengths, capacities, buffer addresses, and initial destination contents. The proofs execute specified inputs at fixed addresses after zeroing the destination. No invariant proving confinement through arbitrary iterations of the decoder and its copy loops was completed. |
| R2 | Exact total return values and output bytes for 10 specified valid independent blocks, including literal extensions, overlapping matches, match extensions, and fast/wide copies. | The universal connection between the LZ4 format and the artifact. There is no Lean formalization of the complete block grammar or an inductive refinement proof for arbitrary valid blocks. Validity of these particular encodings is a reading of the supplied format, not an additional Lean theorem. |
| R3 | Exact returns and content for the same 10 valid blocks and one block using the allowed end-condition relaxation; six specified malformed/undersized cases return `-1`. | An implication about **every** nonnegative return, including all sequence splits and offsets. Enumerating these executions does not prove that implication. There is no universal grammar/success equivalence theorem. |

These are limitations of this verification, not demonstrations of software defects. The Rust source being safe Rust, successful compilation, and passing tests were not treated as formal proofs of these requirements. The original software and requirements were not changed.

**Exact theorem statements and their meaning**

All 19 result theorems are in [Proofs/Proof.lean](Proofs/Proof.lean). Their exact Lean types are:

```lean
theorem Proofs.fresh_runtime_holds : Proofs.fresh_runtime
theorem Proofs.zero_input_holds : Proofs.zero_input
theorem Proofs.empty_block_holds : Proofs.empty_block
theorem Proofs.hello_block_holds : Proofs.hello_block
theorem Proofs.extended_literals_holds : Proofs.extended_literals
theorem Proofs.overlap_one_holds : Proofs.overlap_one
theorem Proofs.overlap_two_holds : Proofs.overlap_two
theorem Proofs.extended_match_holds : Proofs.extended_match
theorem Proofs.fast_overlap_holds : Proofs.fast_overlap
theorem Proofs.fast_wild_copy_holds : Proofs.fast_wild_copy
theorem Proofs.truncated_length_holds : Proofs.truncated_length
theorem Proofs.zero_offset_holds : Proofs.zero_offset
theorem Proofs.external_offset_holds : Proofs.external_offset
theorem Proofs.truncated_literals_holds : Proofs.truncated_literals
theorem Proofs.truncated_offset_holds : Proofs.truncated_offset
theorem Proofs.small_capacity_holds : Proofs.small_capacity
theorem Proofs.relaxed_end_holds : Proofs.relaxed_end
theorem Proofs.wide32_holds : Proofs.wide32
theorem Proofs.wide64_holds : Proofs.wide64
```

The propositions on the right are defined, with all exact input/output byte lists, in [Proofs/Spec.lean](Proofs/Spec.lean). These constants are their unreduced theorem types, not informal theorem descriptions. In that file, `fresh_runtime` is exactly:

```lean
∀ H, ∃ bytes, Instance Lifted.module H (runtime bytes) allocation.2
```

`allocation` allocates the **whole lifted module**, with the actual initial global `65536`. `runtime bytes` has that allocation's functions, exports and global, one fixed 32-page memory with byte function `bytes`, and a dropped data segment. The proof runs the real initializer and connects it to FVA's `Instance` relation. Thus the runtime class used in the other claims contains a genuine initialized instance; its hypotheses are not empty.

`zero_input` is exactly:

```lean
∀ (s : Store) (inst : ModuleInst) (src dst cap : BitVec 32) (H : HostSem),
  s.funcs[7]? = some (.wasm (Lifted.module.types[4]?.getD ⟨[], []⟩) inst Lifted.func7) →
  Must H (fun | .returned s' vs => s' = s ∧ vs = [.i32 4294967295]
              | .trapped _ => False)
    (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap])
```

This proves termination, no trap, the signed result `-1`, and equality of the entire final store to the initial store. It permits arbitrary pointers and capacity. It is a theorem about invoking the artifact's decoder code with the stated function-table premise. It does not separately assert a read-traffic property for that general class of stores.

The 17 remaining claims each specialize this exact common statement:

```lean
def Sample (input : List UInt8) (cap : Nat) (result : BitVec 32)
    (output : List UInt8) : Prop :=
  ∀ (bytes : Nat → UInt8) (H : HostSem),
    let s := ((runtime bytes).withBytes 262144 (List.replicate cap 0)).withBytes 131072 input
    CallReturns H s allocation.2 "lz4_decompress" (arguments input cap)
      (fun s' vs => vs = [.i32 result] ∧ outputBytes s' output.length = some output) ∧
    ∀ c, Steps H (invokeConfig s 7 (arguments input cap)) c →
      configSafe input.length cap c = true
```

`arguments input cap` is `[src=131072, dst=262144, n=input.length, cap]`, as four `i32` values. `outputBytes` reads the specified number of bytes at `dst` from memory 0. All listed inputs and capacities obey the README buffer bounds and nonoverlap conditions. All surrounding memory is universally quantified, including bytes immediately outside both buffers. **The destination buffer itself is explicitly initialized to zero.** These claims therefore include genuine fresh-instance calls after the stated caller writes; they do not quantify over arbitrary destination contents.

`configSafe` extracts the next memory instruction's operands through nested Wasm labels and frames. For each byte in a read/write range whose address lies in `[131072, 2097152)`, it requires membership in the destination buffer, or membership in the source buffer for reads only. The definition includes ordinary and packed loads/stores, `memory.copy`, `memory.fill`, and `memory.init`; data-segment reads are not linear-memory reads. The artifact has one memory, and its decoder uses memory 0. Reviewing these definitions against R1 is part of the stated review surface.

The proof of `certify_sound` transports the checked predicate through **all** semantic steps, using FVA's uniqueness and soundness results. Certificates also check the return and output. They do not assume that the reference interpreter is the semantics. The finite certificate fuel is a proof mechanism: acceptance proves total termination of the corresponding call, rather than merely asserting behavior if it terminates within that bound. No `sorry`, custom axioms, `native_decide`, or `bv_decide` occur in the submitted proofs.

| Claim | Capacity | Signed return | Exact observation / case |
| --- | ---: | ---: | --- |
| `empty_block` | 0 | 0 | Input `00`; empty content |
| `hello_block` | 5 | 5 | Input `50 68 65 6c 6c 6f`; output `hello` |
| `extended_literals` | 15 | 15 | Input `f0 00` followed by bytes 0 through 14; those 15 output bytes |
| `overlap_one` | 13 | 13 | Offset 1, match length 7; eight `A` bytes followed by `BCDEF` |
| `overlap_two` | 14 | 14 | Offset 2, match length 7; `ABABABABA` followed by `CDEFG` |
| `extended_match` | 25 | 25 | Match length 19 with zero extension; twenty `A` bytes followed by `BCDEF` |
| `fast_overlap` | 40 | 40 | 16-byte literal-copy fast path; five `A` bytes and 35 `B` bytes |
| `fast_wild_copy` | 64 | 43 | 18-byte match-copy fast path; `ABCDABCD` and 35 `E` bytes |
| `truncated_length` | 32 | -1 | Input `f0` |
| `zero_offset` | 32 | -1 | Input `10 41 00 00` |
| `external_offset` | 32 | -1 | Input `00 01 00`, referencing before the start of the output |
| `truncated_literals` | 32 | -1 | Input `20 41` |
| `truncated_offset` | 32 | -1 | Input `00 01` |
| `small_capacity` | 4 | -1 | Input `50 68 65 6c 6c 6f` |
| `relaxed_end` | 5 | 5 | Input `10 41 01 00 00`; five `A` bytes; final literal sequence empty |
| `wide32` | 71 | 71 | 32-byte physical match copy, four logical match bytes; exact output in Spec |
| `wide64` | 132 | 132 | 64-byte physical match copy, 33 logical match bytes; exact output in Spec |

All 17 rows prove the traffic property as well as the return/content observation. For error rows, `output=[]` means only an empty output observation: it does **not** assert rollback or an unchanged destination after failure. The six error rows are examples of rejection, not counterexamples to R1–R3. `relaxed_end` is likewise not a defect: R3 explicitly permits relaxing the end conditions.

**Connection to the shipped artifact**

The subject is the original `lz4-flex.wasm`, exactly 7,161 bytes, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

[Proofs/Lifted.lean](Proofs/Lifted.lean) was generated with:

```sh
lake exe fva lift lz4-flex.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It contains the exact bytes as a numeral, their length and source path, the decoded module, and the kernel-checked theorem:

```lean
Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len = .ok Proofs.Lifted.module
```

The proofs use function 7 and the actual artifact's allocation/export table, not a Rust model or a rewritten decoder. The module's `lz4_decompress` export is function 7. The lift was not edited. FVA's link check compares the numeral with the shipped file and verifies the generated source; its independent replay includes `decode_eq`.

**Reproduction, offline, from this directory**

Run the complete check with:

```sh
python3 verification/check.py
```

This checks the artifact hash and `wasm-tools validate`, runs `lake build`, copies the supplied unchanged FVA package outside the project into a temporary directory, points that copy at the already-installed packages, and relinks its executable there. It then runs that external executable as:

```sh
/path/to/external/fva/.lake/build/bin/fva trust . \
  --spec-module Proofs.Spec --root-module Proofs \
  --surface-budget 200 --kernel-limit 1200
```

The exact external pathname is printed by `check.py`. No network or package download is used. Independent kernel replay recomputes the proof obligations and can take several minutes even when the Lake build is cached. Retain an independently trusted copy of FVA if evaluating a subsequently modified/untrusted project: moving an altered verifier outside a project would not restore trust in it. The supplied FVA Lean sources were left unchanged in this work.

Success requires exit status 0, `lake build` reporting success, FVA reporting **PASS for all 19 listed claims**, accepted replays by `leanchecker` and `con-leche`, and canary coverage satisfying FVA’s documented verdict rules. The supplied canary table permits Lean’s known replaced-prelude acceptance when the independent checker rejects it; some canaries may be declined. The final script output is:

```text
PASS: 626 Wasmtime cases; exact artifact, return/output/source/guard checks
PASS: all delivered partial claims checked; universal R1–R3 remain UNPROVED
```

The FVA output is saved in [verification/TRUST.txt](verification/TRUST.txt); the complete one-command run is recorded in [verification/CHECK.txt](verification/CHECK.txt). Failure, rejection, timeout, or a missing checker is not success. The FVA PASS pertains only to the explicit `Proofs.Spec` claims, not the three universal requirements.

The additional runtime tests can be repeated independently:

```sh
python3 verification/runtime_checks.py
```

The script embeds the **unaltered binary bytes** in a WAST module, imports that module's actual memory/function into caller wrappers, initializes input/output buffers, and runs Wasmtime assertions. It checks return values, successful output bytes, unchanged source bytes, and 16 guard bytes on each side of the destination. It tests the 17 proof inputs plus generated literal/match blocks, insufficient capacities, and random byte strings using seed `0x4c5a34`. A separate Python sequence decoder supplies expectations for these supplementary tests, allowing a decoder to reject blocks that lack end conditions. Generated valid blocks must succeed when capacity suffices. Invalid sequence encodings and insufficient capacity must return `-1` in this test suite.

The 626 passing tests are empirical evidence only. They cannot establish read confinement, preservation of every byte outside the guards, exhaustive malformed-input behavior, or a universal format theorem. No observed runtime result was substituted for a Lean proof.

**Review and trust surface**

| Material | Size | Role |
| --- | --- | --- |
| `Proofs/Spec.lean` | 162 lines; 8,541 bytes | Project-specific propositions, runtime class, byte observations, and memory-traffic definitions. Review all of it for correspondence to the claimed partial results. |
| `Proofs/Proof.lean` | 177 lines; 6,517 bytes | Kernel-checked proofs and the proven certificate checker. Reading it is optional once independent replay succeeds; it contributes no assumed semantics. |
| `Proofs/Lifted.lean` | 82 lines; 97,882 bytes | Generated subject. Checked by byte linking and decoder proof, rather than trusting or manually reading its printer output. |
| `verification/check.py` | 51 lines; 2,321 bytes | Offline command orchestration. Review its verifier selection and exit handling if using the one-command reproduction. |
| `verification/runtime_checks.py` | 152 lines; 6,108 bytes | Only for the supplementary test claims: generator, independent Python decoder, caller wrappers, assertions. Not a trusted component of the Lean proofs. |
| `README.md`; `lz4_Block_format.md` | 18 lines / 2,402 bytes; 244 lines / 10,683 bytes | Human intent and format interpretation for the selected examples. No claim of a complete Lean transcription of this format. |
| FVA `FVA/Spec/**/*.lean` | 23 files; 3,606 lines; 161,903 bytes | Reviewed-once base: Wasm syntax, binary grammar, execution, numerics, instantiation, claims, and trust verdict specifications. |
| FVA `FVA/Trust/**/*.lean`; `FVA/Tool/**/*.lean` | 887 lines / 40,918 bytes; 2,894 lines / 139,610 bytes | Conservative size bounds for the supplied audit/glue directories, including collection, linking, export/replay, canaries, and orchestration. Not all files in these directories are on this audit's execution path. |

The residual trust is FVA's stated boundary: correctness of the reviewed specifications, Lean and the independent checker, the compiler/toolchain and pinned Mathlib, and the audit/export/canary glue. FVA's verified decoder/stepper and this project's certificate checker have checked proofs connecting them to their specifications. The correspondence between `configSafe` and the English memory-access requirement is still a human review obligation. Wasmtime, Python, and the supplementary Python parser are additional trust only for the test report, not for the formal claims.

The externally relinked FVA executable used for the recorded audit had SHA-256 `5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407`; this is provenance for this run, not a requirement that another toolchain reproduce identical executable bytes. The linked recorded audit supplies the actual replay/canary verdict and project review-surface count.

The completed one-command run exited **0**. FVA reported **PASS for 19 artifact-linked claims**, with **106 code lines** to review in `Proofs.Spec`. `leanchecker` accepted the proof export in 325 seconds and `con-leche` in 231 seconds. Of 72 pinned known-false canaries, Lean rejected 71 and accepted its one documented replaced-prelude case; `con-leche` rejected 69, declined 3, and accepted none. FVA checked the documented acceptance coverage and reported no canary, replay, axiom, layout, or link issue. The artifact link matched, and the subsequent 626 Wasmtime cases passed. This audit establishes the narrower claims listed above; it does not change the overall **unproved** status of R1–R3.
