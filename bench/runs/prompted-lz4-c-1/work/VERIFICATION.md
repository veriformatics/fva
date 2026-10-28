# Verification result: incomplete

**R1, R2, and R3 remain unproved in their universal form. No counterexample to any of them was found.** This directory contains machine-checked partial results and a reproducible checking setup, not a complete verification of the README requirements. Passing the check command does not certify universal R1–R3.

## Results for each requirement

| Requirement | Machine-checked result | Remaining obligation |
| --- | --- | --- |
| R1 | For each of the 16 explicit cases in `Verification.cases`, the execution terminates and every byte of every recorded user-region load/store satisfies R1. Two additional theorems cover arbitrary initial memory at fixed boundary-case arguments, below. | Arbitrary arguments, source bytes, and caller memory. There is no inductive invariant proving the bounds of all parsing and copying loops. |
| R2 | For those cases where the executable format specification says the block is conforming and the capacity condition holds (11 cases), the returned length and every decoded byte agree with the specification. The zero-capacity theorem also describes the empty-block boundary case for arbitrary memory. | All valid blocks and all permitted placements/capacities. The necessary relation between an arbitrary parsed prefix, the output prefix, and the optimized copying loops has not been proved. |
| R3 | For all 13 nonnegative returns in the case list, relaxed format parsing succeeds, the length is within capacity, and every output byte agrees with the parsed content. This includes two zero-offset examples. | Every possible successful execution. No global parsing/output invariant connects every success exit to the format specification. |

The finite checks use a deliberately nonzero initial caller memory, byte `165` (`0xa5`), except for the supplied source bytes. They are not quantified over all caller memory. The two boundary theorems below **are** quantified over memory, but keep the addresses, sizes and capacities shown in their statements fixed.

The exact aggregate theorem, in [`Proofs/Certificates.lean`](Proofs/Certificates.lean), is:

```lean
Certificates.checked_cases :
  Verification.cases.all Verification.checks = true
```

Its complete specification dependency is in [`Proofs/Cases.lean`](Proofs/Cases.lean), [`Proofs/Spec.lean`](Proofs/Spec.lean), [`Proofs/Wasm.lean`](Proofs/Wasm.lean), and the artifact constants described below. In particular, `checks` requires:

1. The README buffer-placement and non-overlap preconditions.
2. A terminating execution with the explicitly expected return value.
3. R1 for every byte covered by each load/store event.
4. R2 whenever `LZ4.decode` marks the input conforming and the capacity antecedents hold.
5. R3 whenever the return is nonnegative; `LZ4.decode` permits zero offsets and departures from the end conditions, implementing zero-offset matches as zero bytes.

`LZ4.decode` is an independent format specification, not a transcription of the C decoder. It parses literal/match length extensions, little-endian offsets, overlapping matches, the final literal sequence, and the end conditions. Its correspondence to the prose format document is a **human review obligation**, not a separately proved theorem.

The other two public behavioral theorems are in `Proofs/Cases.lean`. Their exact source statements, inside `namespace Verification` with `open Wasm`, are:

```lean
theorem no_input (mem : Mem) :
    observation (run Artifact.functions 32
      (start Artifact.functions mem 131072 1048576 0 32)) =
      some (4294967295, [])

theorem zero_capacity (mem : Mem) :
    observation (run Artifact.functions 32
      (start Artifact.functions mem 131072 1048576 1 0)) =
      some ((if load mem 131072 1 == 0 then 0 else 4294967295),
        [⟨false, 131072, 1⟩])
```

Here `4294967295` is the i32 representation of `-1`. `Mem` is a byte-addressed function; loads reduce values modulo 256. `observation` retains the return and complete memory-access trace. Thus empty compressed input performs no memory access; a one-byte input at zero capacity reads precisely its one source byte and performs no writes. The latter succeeds exactly when that byte is zero.

These are partial theorems, not restatements of universal R1–R3. In particular, no finite test bound is substituted for the quantifiers in README.md.

## Connection to the shipped implementation

The artifact is the original **8,469-byte** `lz4-c.wasm`, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

No C source or shipped Wasm bytes were changed, and the artifact was not rebuilt.

[`Proofs/Artifact.lean`](Proofs/Artifact.lean) quotes every binary byte as `Artifact.bytes`. The check command compares this literal byte-for-byte with the file, independently of the generator, and checks the size/hash and `wasm-tools validate`.

The exact linking theorem is:

```lean
Artifact.code_link :
  Wasm.program Artifact.bytes = some Artifact.functions
```

`Wasm.program` reads the binary sections and function bodies and decodes the instructions of actual functions 2, 3, and 4: the exported decompressor and its `memcpy`/`memmove` callees. Instruction tables are generated data; this theorem checks them against the binary reader inside the proof kernel. They are not a handwritten replacement implementation.

`Artifact.metadata_link` (exact statement at the end of `Proofs/Artifact.lean`) also checks all non-code section payloads. They fix the signatures and function indices, exported decoder at function 2, fixed 32-page memory, mutable global, absence of imports/start/table, and the active 64-byte data segment at address 65536. Its data payload is expressed using `Artifact.dataBytes`, the same constant used by the execution's initial memory.

`Proofs/Wasm.lean` supplies the reviewed operational semantics: i32 wraparound/comparisons/shifts, structured branches and loops, calls/returns, little-endian loads/stores, and memory bounds/access recording. Unsupported instructions/calls, traps and exhausted fuel produce `none`, which cannot satisfy `checks`. This is a manually defined restricted **Wasm semantics**, not a manually defined LZ4 implementation. Its agreement with WebAssembly semantics remains a review/trust boundary. Wasmtime executions provide an additional independent cross-check, not a universal refinement proof.

Concrete executions use fuel 1000; the longest selected execution takes 880 instructions including its terminating instruction. Each certificate proves an actual successful execution, so fuel exhaustion is not silently accepted. The arbitrary-memory boundary theorems use fuel 32 and likewise prove termination.

## One command to check everything

From this directory, run:

```sh
./check.sh
```

No network or source rebuild is used. The command requires the installed Lean 4.35.0 toolchain, Python 3, `wasm-tools`, `wasmtime`, and the installed `leanexport`, `nanoda_bin`, and `con-ron` binaries in Lean's binary directory. It does not require Mathlib imports or downloads.

It performs the following checks:

- Validates and identifies the artifact and checks every quoted byte.
- Compiles every project proof module afresh into a temporary import directory. Existing project `.olean` files are not used.
- Prints theorem axioms and exports the five public results, including the two linking theorems, with their complete proof dependency closure.
- Audits the export for missing results and unapproved axioms. The actual closure uses only the standard axiom `propext`. The explicit allowlist also permits `Classical.choice` and `Quot.sound`; neither occurs. `sorryAx`, compiler-trust axioms and arbitrary new axioms are not permitted.
- Replays that same export through **Nanoda** and **Con-ron in `--verified` mode**, separate Rust proof kernels, in addition to Lean's own checking.
- Checks positive controls and then feeds both independent kernels valid-format exports whose original reflexivity proof has been forged to claim `False` and `0 = 1`. Both must reject with type-checking failures. Nanoda's installed build reports these as a `tc.rs` definitional-equality assertion failure (exit 101); the script requires that diagnostic, not just any crash. Con-ron must report a type mismatch (exit 1). Lean must also reject a false source proof.
- Uses Wasmtime to execute the **unaltered binary**, embedded directly in a WAST harness, for all 16 cases. It checks returns, decoded bytes, source preservation and adjacent canaries. A deliberately incorrect expected return must make this harness fail.

Success is exit status zero with this final line:

```text
PASS: all stated partial results checked; universal R1, R2, R3 remain UNPROVED
```

The command was run successfully. Nanoda checked 2,740 environment declarations with no type-checker errors; Con-ron accepted 2,589 declaration records. These counts use different units. Nanoda also prints one pretty-printer diagnostic, `Unable to print axioms`; it is not a type-checking failure. All negative controls were rejected and all 16 Wasmtime executions passed.

The export, axiom listing and runtime harness are retained under `.lake/verification/` as `proofs.ndjson`, `axioms.txt`, `cases.json`, and `runtime.wast`. The export was 3,382,071 bytes. Proof generation is not needed to check the committed results. Optional generators are `verification/generate.py` and `verification/certify.lean`; their outputs remain subject to all kernel checks.

## Review and trust surface, with sizes

The primary custom semantic/specification files total **364 lines, 13,650 UTF-8 bytes**, counting comments and blank lines:

| File | Lines | Bytes | What needs semantic review |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 236 | 8,388 | Binary reader and restricted Wasm semantics. |
| `Proofs/Spec.lean` | 44 | 1,745 | Meaning of conforming and relaxed independent blocks. |
| `Proofs/Cases.lean` | 84 | 3,517 | Preconditions, initial memory, observations, property predicates, explicit case list and boundary statements. |

Also review the linking statements/metadata in `Proofs/Artifact.lean`, the public aggregate statement in `Proofs/Certificates.lean`, and the bridge from disk bytes to the quotation in `verification/check.py`.

For a conservative count that includes **all** numeric artifact tables, the linking metadata, composition lemma, aggregate module and library root, these project proof/specification files total **821 lines, 53,962 bytes**. `Proofs/Artifact.lean` accounts for 406 lines/38,193 bytes, mostly mechanically checked data. Generated intermediate execution certificates in `Proofs/Certificates/C*.lean` add **3,394 lines, 447,844 bytes**. Their states and step equations occur in the proofs, not in the public property definitions: kernels check them, so they need not be trusted as an oracle or manually matched to the implementation.

The checking/evidence scripts also matter for the claimed end-to-end result:

| Files | Lines | Bytes |
| --- | ---: | ---: |
| `verification/check.py` | 125 | 6,743 |
| `check.sh` | 4 | 100 |
| `verification/negative.py` | 51 | 2,193 |
| `verification/runtime.py` | 40 | 2,183 |
| `verification/export_cases.lean` | 11 | 487 |
| `verification/axioms.lean` | 6 | 202 |

The generators are untrusted certificate/data producers: `generate.py` is 88 lines/3,804 bytes; `certify.lean` is 91 lines/5,863 bytes. Kernels check binary decoding, execution step equations, their composition and final predicates. Native evaluation used to produce certificates or the runtime test inputs does not discharge proof obligations.

The remaining foundational trust includes the meanings of Lean's standard logic/arithmetic/list definitions, `propext`, the installed checker binaries and their supported primitive rules, the toolchain exporter, Python/file I/O and process execution, the host system, and Wasmtime/wasm-tools for the runtime evidence. The exported closure includes the relevant standard-library definitions and proofs and is independently replayed. No claim is made that this work verifies those tools themselves, proves the custom semantics equivalent to an official Wasm semantics, or supplies the missing universal LZ4 invariants.
