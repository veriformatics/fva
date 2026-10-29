# Verification report

**Status: partial verification. Universal R1, R2, and R3 have neither been proved nor refuted.** No counterexample to a README requirement was established. The results below are an empty-input theorem and proofs for 15 concrete executions. Passing the check command does **not** establish the three universal requirements.

## Results and exact statements

The following statements are in [`Proofs/Claims.lean`](Proofs/Claims.lean), in namespace `Verification`:

```lean
theorem empty_input (src dst cap : Nat) (mem : Memory) :
    observe (run Artifact.code Artifact.ends 10 (initial src dst 0 cap mem)) =
      some (2^32-1, mem, [])

theorem corpus : cases.all checkCase = true
```

`Memory` is a byte-addressed finite association list with default zero. `observe` reports the returned i32 bit pattern, final memory, and the complete list of memory accesses by the decoder. Consequently, `empty_input` establishes a return of -1, unchanged memory, and no reads or writes, for every initial memory and every choice of parameters when `n = 0`. Physical Wasm arguments are the representable i32 instances of these natural-number parameters. This theorem takes ten interpreter steps; it is not a timeout observation.

`cases` and **all** the definitions giving `checkCase` its meaning are in `Claims.lean` and [`Proofs/Machine.lean`](Proofs/Machine.lean). `checkCase` requires admissible buffers, successful completion within 2,500 instructions, and permission for every byte of every recorded access. It then checks the expected return. For success it checks the capacity bound, every returned output byte, a complete independent LZ4 sequence parse, valid backward offsets, and the end conditions. For failure it checks that the independently parsed input is invalid or does not fit. The expected results are data checked by the proof, not assumptions supplied to the decoder semantics.

| Requirement | Established | Still open |
| --- | --- | --- |
| R1 | `empty_input` proves no accesses for all empty inputs. `corpus` checks the read/write restriction for each of the 15 concrete executions, including on error. | All other input bytes, lengths, capacities, buffer placements, and initial memories. No general memory-safety invariant was proved. |
| R2 | `corpus` proves the required return and contents for nine particular valid, fitting blocks. | Completeness and termination on every valid fitting block. No general refinement from the compiled control flow to the format specification was proved. |
| R3 | `corpus` proves the required parse, offsets, length bound, and contents for its nine successful executions. `empty_input` returns -1, so its R3 antecedent is false. | Soundness for every successful execution. No inductive correspondence between arbitrary decoder iterations and LZ4 sequences was proved. |

The finite corpus includes: an empty compressed stream; a zero token representing empty output; five literals; the literal-length extension at 15; insufficient capacity; zero and out-of-history offsets; truncated length and offset fields; an offset-one overlapping match; both overlapping and non-overlapping fast paths; a match-length extension; and input/output placements ending exactly at address 2,097,152. There are nine successes and six errors. The exact inputs, addresses, capacities, and expected bytes are the list `Verification.cases`; no random test seed or external corpus is needed. The memory initially contains the artifact's data segment, zeros elsewhere, the input bytes, and `0xcc` in the output buffer. The finite theorem does not quantify over other initial output contents.

## Connection to the shipped implementation

The artifact is the unchanged `lz4-flex.wasm`, exactly 7,161 bytes, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

[`verification/lift.py`](verification/lift.py) pins both length and digest, reads the binary sections, checks the absence of imports and a start function, checks the memory and export declarations, and extracts **function 7**, the exported `lz4_decompress`. Its body is 2,000 bytes, including five bytes declaring 17 i32 and seven i64 locals; the remaining bytes decode to 982 instructions. The script also extracts the module's actual active data segment.

The automatically generated [`Proofs/Artifact.lean`](Proofs/Artifact.lean) contains the instruction bytes, decoded instructions, branch targets, and initial data. It proves these statements in namespace `Artifact`:

```lean
theorem lift_exact : decode raw.length raw = some code.toList
theorem ends_exact : checkEnds code ends = true
```

Thus the decoded program and branch table are checked, not silently assumed correct output of a disassembler. The binary-to-raw-byte extraction and module metadata checks remain a small, explicitly trusted Python bridge. The one-command check regenerates the lift and requires byte-for-byte equality with the delivered file. It also runs `wasm-tools validate` on the binary.

`Machine.lean` interprets these actual instructions, including i32 wrapping arithmetic, little-endian scalar loads/stores, structured branches, overlap-safe `memory.copy`, and `memory.fill`. It records bulk accesses over their full ranges. Unsupported instructions, traps, and calls fail closed (`none`); no theorem here treats such a failure as a valid execution. The covered executions do not call helpers. The interpreter is a manually written WebAssembly semantics, **not a manually rewritten decoder**. Its agreement with WebAssembly semantics is part of the human review obligation; no adequacy theorem against an existing formal Wasm semantics is claimed. The Rust source and the shipped Wasm have not been rewritten or rebuilt.

Independently, [`verification/runtime.py`](verification/runtime.py) embeds the complete original binary in WAST tests and runs all 15 cases in Wasmtime, checking the actual return and every successful output byte. `Emit.lean` supplies this corpus directly from the proof definitions. This catches execution-model and harness mistakes on the corpus, but is not a proof of interpreter adequacy and does not independently observe every memory read.

## Reproduction and checker controls

From this directory, run:

```sh
python3 verification/check.py
```

No network is used. The command requires the provided Lean/Lake 4.35 installation and built dependencies, Python 3, `wasm-tools`, `wasmtime`, and the provided `/opt/lean/bin/leanexport`, `leanchecker-paranoid`, and `lean4lean` executables.

The command deletes only local proof build outputs, rebuilds the proofs, exports the complete dependency closure of the four named theorems, and replays that export through:

```sh
/opt/lean/bin/leanchecker-paranoid --from-export verification/generated/proofs.ndjson
/opt/lean/bin/lean4lean --import verification/generated/proofs.ndjson
```

The first uses Lean's default C++ kernel in its paranoid build. The second is the independent Lean4Lean kernel implementation. NDJSON transport avoids the installed Lean4Lean executable's incompatible `.olean` version; no version-header patching or skipped checks are used. Proofs use kernel reduction (`rfl` / `decide`, including `decide +kernel`), not `native_decide`. The dependency audit allows only the standard `propext` axiom and requires all four named theorem declarations to be present. It rejects `sorryAx` and unexpected axioms.

[`verification/FalseProofs.lean`](verification/FalseProofs.lean) deliberately constructs two invalid theorem declarations using disabled initial kernel checking: `False` from `True.intro`, and `0 = 1` from `Eq.refl 0`. This file is never imported by the real proofs. Each forged declaration is exported separately and submitted to **both** replay kernels. The command requires a nonzero exit **and an explicit declaration-type-mismatch diagnostic naming the false theorem**; arbitrary startup failures do not count as successful controls. Wasmtime also receives a deliberately wrong expected return and must reject it.

Success ends with exactly this message:

```text
CHECK PASSED: partial results only; universal R1, R2, R3 remain unproved.
```

Logs, the proof export, axiom/dependency counts, corpus WAST, and source sizes are saved under `verification/generated/`. A checker accepting a false proof, a missing theorem, a stale lift, an unexpected axiom, a wrong runtime result, or a failed positive replay makes the command fail.

## Human review and trust size

Counts below include comments and blank lines; bytes are UTF-8 file sizes. `verification/generated/sizes.json` reproduces the measurements.

| Material | Lines | Bytes |
| --- | ---: | ---: |
| `Proofs/Machine.lean`: instruction semantics, binary decoder, branch-table checker, memory/access definitions | 194 | 7,242 |
| `Proofs/Claims.lean`: format, admissibility, permission and output predicates, corpus, theorem statements and proofs | 133 | 5,324 |
| `verification/lift.py`: binary extraction and regeneration bridge | 78 | 3,466 |
| `Proofs/Artifact.lean`: generated instruction/data literals and two linking theorems | 995 | 26,841 |
| `Proofs.lean`: root import | 1 | 21 |
| `verification/check.py`: rebuild, export, audit, replay and controls | 92 | 5,063 |
| `verification/Emit.lean`: corpus transport | 10 | 358 |
| `verification/runtime.py`: independent binary-execution harness | 38 | 2,062 |
| `verification/FalseProofs.lean`: deliberate negative controls | 14 | 609 |

The handwritten formal files total **327 lines / 12,566 bytes**. Including the extraction bridge, that is **405 lines / 16,032 bytes**. All handwritten verification/support files including the root import and controls total **560 lines / 24,145 bytes**, plus the generated artifact file above. The generated literals should be checked by regeneration rather than reviewed as a second implementation.

These are not claims that the transitive definition closure is only 327 lines. The complete exported closure, including the relevant Lean `Init` definitions, has **493 definition records, 140 theorem records, 72 inductive groups, one opaque declaration, and one axiom (`propext`)**, serialized in **34,092 NDJSON lines / 1,855,688 bytes**. `verification/generated/closure.json` records these counts. The opaque declaration is `String.Internal.append`, from support for standard literal/representation definitions; it is not an assumed decoder-correctness theorem.

A reviewer must assess the README-to-predicate interpretation, the WebAssembly semantics and binary bridge, the corpus's limited quantification, the orchestration scripts, and the standard meanings of the library primitives used by those definitions. Foundational trust includes Lean's type theory and `propext`, the two kernels and their parsers/export transport, Python and OS/file integrity, and the compiler/runtime tools used for the independent execution checks. Kernel replay checks the proof and definition closure, but does not prove that these definitions express the English requirements. In particular, no finite corpus or successful checker-control test closes the universal gaps listed above.
