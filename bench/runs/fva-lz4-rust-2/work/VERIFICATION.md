# Verification status: incomplete

**R1, R2 and R3 have not been proved in full, and no violation of them has been demonstrated.** The results below are partial machine-checked claims and finite execution checks. A PASS from FVA for these claims must not be read as a PASS for the README requirements.

The saved [`verification/FVA-trust.txt`](verification/FVA-trust.txt) records **FVA PASS for seven partial claims**: `leanchecker` accepted the proof export in 263 seconds, con-leche accepted it in 207 seconds, and the artifact link matched. FVA measured **38 code lines**, all in `Proofs.Spec`, as the project claim review surface. [`verification/regression.txt`](verification/regression.txt) records the 6,239 passing finite Wasmtime cases.

The canary results have exceptions: of 72 known-false exports, Lean rejected 71 and accepted the installed known exception `prelude-15704/replaced-prelude`. Con-leche rejected that exception; it rejected 69 canaries overall and declined `arena/bad/tutorial/047_inductBadNonSort2`, `arena/bad/tutorial/140_falseFromUnsafe`, and `arena/bad/tutorial/141_falseFromPartial`. Neither checker crashed or timed out on a canary. FVA's installed policy allows the known acceptance when another checker rejects that canary, and allows declines. Thus PASS does **not** mean that both checkers rejected every canary. The prelude check and independent replay are material parts of the trust boundary.

## Requirement coverage

| Requirement | Result and remaining obligation |
| --- | --- |
| R1: confinement of every read and write | Unproved. Some cases below preserve the final store or all memory outside the destination, but that does not establish confinement of intermediate accesses. The regression tests check adjacent write canaries, not reads. A complete proof needs access-sensitive invariants for every reachable load, store, memory copy and memory fill, including error paths. |
| R2: every valid independent block fitting in the destination decodes correctly | Unproved in general. The empty block and the family of one-byte literal blocks have explicit execution claims below. A general proof still needs a formal relation for the supplied LZ4 format, invariants connecting encoded sequences to decoder locals and output memory, termination arguments for the length/sequence/copy loops, and proofs for the optimized copy paths. |
| R3: every nonnegative result certifies a valid sequence decomposition and its output | Unproved in general. There are execution claims for a valid literal case and rejection of one zero-offset block. There is no proved converse for arbitrary inputs, no formal sequence-decomposition relation, and no proof covering all malformed inputs or all return paths. |

The source inspection and finite checks found no counterexample. Absence of a counterexample is not a universal correctness result. None of the three universal requirements has been replaced with a weaker claim and declared satisfied.

## Exact formal claims

All claim definitions are in [`Proofs/Spec.lean`](Proofs/Spec.lean). Their proofs are in [`Proofs/Proof.lean`](Proofs/Proof.lean), [`Proofs/Literal.lean`](Proofs/Literal.lean), and [`Proofs/Setup.lean`](Proofs/Setup.lean). The exact theorem statements are:

```lean
theorem Proofs.zero_input_holds : Proofs.zero_input
theorem Proofs.empty_block_holds : Proofs.empty_block
theorem Proofs.one_literal_holds : Proofs.one_literal
theorem Proofs.zero_offset_holds : Proofs.zero_offset
theorem Proofs.module_valid_holds : Proofs.module_valid
theorem Proofs.initializable_holds : Proofs.initializable
theorem Proofs.fresh_runtime_store_holds : Proofs.fresh_runtime_store
```

The first four use FVA's `CallReturns`: every execution under the quantified host semantics terminates, returns the stated result, and satisfies the postcondition; traps are excluded. Arguments below are in the exported order `(src, dst, n, cap)`. Byte strings are hexadecimal, and `-1` is the i32 bit pattern `4294967295`.

| Claim | Quantification, hypotheses and exact behavior |
| --- | --- |
| `zero_input` | Every host semantics, every `MemInst`, and every i32 `src`, `dst`, `cap`: calling with `n = 0` returns `-1` and the entire final store equals the starting store. No memory-size hypothesis. |
| `empty_block` | Every host semantics and every memory with 32 pages and `mem.byte 131072 = 0`: `(131072, 131104, 1, 0)` returns `0` and the entire store is unchanged. This input is the valid encoded empty block `00`, not a zero-byte compressed input. |
| `one_literal` | Every host semantics and every memory with 32 pages and `mem.byte 131072 = 16`: `(131072, 131104, 2, 1)` returns `1`; final memory 0 exists, its byte at 131104 equals the original byte at 131073, and its byte at every other natural-number address equals the original byte. Thus the payload byte is arbitrary, not just one chosen value. |
| `zero_offset` | Every host semantics and every memory with 32 pages and bytes 131072, 131073 and 131074 all zero: `(131072, 131104, 3, 4)` returns `-1` and the entire store is unchanged. The first sequence of `00 00 00` specifies offset zero, which the supplied format forbids. |
| `module_valid` | Exactly `FVA.Wasm.Valid.ModuleValid Proofs.Lifted.module`, using FVA's verified validator. This is Wasm typing, not LZ4 correctness or buffer confinement. |
| `fresh_runtime_store` | Exactly `∀ H, ∃ mem : MemInst, mem.pages = 32 ∧ Instance Lifted.module H (codeStore mem) allocation.2`. This connects the runtime-store family used by the case proofs to an actually successful fresh instantiation, under every host semantics. |
| `initializable` | Exactly `FVA.Wasm.Exec.Instantiable Proofs.Lifted.module`: for every host semantics there exists a successful fresh instance. It follows from `fresh_runtime_store`; that proof checks FVA's instantiator with fuel 2000 and applies its soundness theorem. Fuel is used to construct the proof, not as a bound in the claim. |

For the execution claims, the starting store and instance are **exactly** these definitions, not an assumed Rust implementation:

```lean
noncomputable def allocation : Store × ModuleInst :=
  allocModule {} Lifted.module [] [.i32 65536] []
noncomputable def codeStore (mem : MemInst) : Store :=
  { allocation.1 with mems := [mem], datas := [{ data := [] }] }
```

The starting store is `codeStore mem` and the instance is `allocation.2`. This supplies the functions, types, exports and initialized stack-pointer global from the decoded module, with its active data segment dropped and arbitrary memory. `fresh_runtime_store_holds` proves that this family includes a successfully initialized fresh instance for every host semantics. Replacing its memory with caller-written input leaves it within the same family. The four execution claims quantify over the entire family, including arbitrary bytes in the destination and elsewhere.

They do **not** quantify over `Instance` or prove uniqueness of all successful fresh instances. The existential instantiation bridge is stated explicitly above; it is not a proof of the universal README requirements or FVA's stronger `ReturnsAfterWrite` form.

## Connection to the shipped artifact

The subject is the unchanged `lz4-flex.wasm`, 7,161 bytes, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

[`Proofs/Lifted.lean`](Proofs/Lifted.lean) was generated with:

```sh
lake exe fva lift lz4-flex.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It contains the packed original bytes, byte length, source path, decoded functions and module, and the kernel-checked theorem:

```lean
theorem Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len =
    .ok Proofs.Lifted.module
```

FVA's link check compares the packed numeral against the actual file and checks the generated lift. The allocation exports `lz4_decompress` as function 7. The execution proofs use `Lifted.func7` from that module and FVA's proved reference-stepper semantics. No proof substitutes a decoder written in Lean for the compiled decoder. Neither the Rust build process nor equivalence of Rust source and Wasm is assumed for these results.

## Reproduction

Run from this directory, with the installed offline Lean 4.35/Mathlib environment:

```sh
sha256sum lz4-flex.wasm
lake build
python3 verification/check.py
python3 verification/regression.py
```

The hash must match above. `lake build` must exit zero and print `Build completed successfully`. The checking script verifies the artifact hash and pinned FVA source hashes, copies FVA to a fresh temporary directory outside this project, rebuilds its executable there using the installed packages and cached FVA library build artifacts, then checks `Proofs.Spec` under root module `Proofs`.

The script supplies the external executable path automatically. Success is exit zero, `fva trust: PASS`, acceptance by the default Lean and independent con-leche kernels, a matching artifact link and canary results accepted by FVA's policy described above, and the script's final message explicitly identifying these as partial claims. The FVA copy inside the submitted project is not used as the final verdict executable.

`python3 verification/regression.py` embeds the exact original binary in a temporary WAST script and executes it with Wasmtime. Success is exit zero and:

```text
PASS: 6239 finite Wasmtime cases; return values, successful output bytes, adjacent canaries.
No universal R1/R2/R3 proof; read confinement is not tested.
```

The deterministic cases include all 256 one-byte inputs; literal lengths around the nibble, copy-width and extension thresholds; offsets 1, 2, 3, 4, 8, 16, 32 and 64; overlapping matches; malformed and mutated blocks; several capacities including exact size and one byte too small; and alternating source/destination layouts at the memory boundary. A Python decoder supplies expected values and bytes. It deliberately permits end-condition violations, so it is not a recognizer for R2's valid-block domain. This test oracle is not a proved implementation of the format. Adjacent canaries do not rule out distant writes or any out-of-buffer reads.

## Review and trust

A reviewer must check that the claim definitions and their restricted scope mean what is reported. The proof files need not be accepted on inspection: the Lean kernel and FVA's independent replay check them. The formal trust boundary additionally includes FVA's reviewed Wasm specifications and claim forms, its verified decoder/stepper/validator/instantiator, FVA's source/link/axiom/closure collection and replay orchestration, the installed Lean compiler and kernels, and pinned Mathlib. This is FVA's documented base trust boundary, not a source-level Rust safety assumption.

For the finite execution evidence, additionally read and trust the entire Python oracle/generator and Wasmtime. For the one-command checking workflow, inspect `verification/check.py`, including its local-base-manifest comparison and external build. The manifest is not an independently authenticated download: its pin and the supplied FVA baseline are part of the tool installation trust.

Source sizes are recorded below; the measured FVA claim review surface is 38 code lines. Generated lift bytes are checked by the decoder/link mechanism rather than manually reviewed. The original `README.md`, `CHECK.md` and `lz4_Block_format.md` remain the English requirements against which this incomplete coverage is assessed.

| Review item | Size | Role |
| --- | ---: | --- |
| `Proofs/Spec.lean` | 77 lines; 3,810 bytes | All seven formal claim definitions and the runtime-store construction; read this to assess scope. |
| `verification/check.py` | 45 lines; 2,184 bytes | Hash checks, external FVA build and verdict orchestration. |
| `verification/regression.py` | 133 lines; 5,546 bytes | Entire unproved reference decoder and finite-test generator; needed only for the regression evidence. |
| `README.md` | 18 lines; 2,402 bytes | English requirements and artifact identity. |
| `lz4_Block_format.md` | 244 lines; 10,683 bytes | English format specification; no complete formalization is supplied here. |
| FVA `trust/canaries/set.tsv`, `trust/canaries/known.tsv` | 198 lines; 20,740 bytes total | Pinned canary cases and the known-acceptance policy, including the prelude exception above. |
| `CHECK.md` | 8 lines; 784 bytes | Delivery requirements. |
| FVA `FVA/Spec/**/*.lean` | 23 files; 3,606 lines; 161,903 bytes | Conservative count of the supplied reviewed specification base, including specifications unused by these integer-only calls. |
| FVA tool/support sources | 23 files; 4,131 lines; 196,491 bytes | Conservative count of all `FVA/Tool/**/*.lean`, `FVA/Trust/**/*.lean`, plus `Main.lean`, `FVA.lean`, `FVA/Cli.lean`, `FVA/Lifted.lean`, `FVA/Explain.lean`, `FVA/Version.lean`; not all are trusted or used in this run. |
| `Proofs/Proof.lean`, `Proofs/Literal.lean`, `Proofs/Setup.lean` | 133 lines; 5,132 bytes total | Machine-checked proofs, not additional assumptions to accept on inspection. |
| `Proofs/Lifted.lean` | 82 lines; 97,882 bytes | Generated subject and decoding proof; checked against the 7,161-byte artifact. |

The installed checker was Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with the supplied Mathlib v4.35.0 package. The finite regression used Wasmtime 50.0.0 (`ebe5e8df1`). Source sizes count physical newline-terminated lines and UTF-8 bytes, not FVA's separate code-line surface metric. The FVA report records that metric and the kernel/axiom/link results.
