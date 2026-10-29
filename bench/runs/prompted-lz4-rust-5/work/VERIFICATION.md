# Verification status: partial, not a proof of R1–R3

The universal requirements R1, R2 and R3 are **unresolved**. No counterexample to them was found. The results below prove a universal zero-input subcase and 28 specific executions of the shipped artifact. Passing the check command must not be interpreted as establishing the universal requirements.

## Results and exact statements

The four exported root theorems are:

```lean
-- Proofs/Claims.lean, namespace Verification
 theorem zero_input (src dst cap : Nat) (m : Wasm.Memory) :
    let s := Wasm.run Artifact.code 5
      (Wasm.initial Artifact.localCount src dst 0 cap m)
    s.status = .returned 4294967295 ∧ s.mem = m ∧ s.events = []

 theorem buffers_admissible : Samples.all.all admissible = true
 theorem samples_format : Samples.all.all formatAgrees = true

-- Proofs/Cases.lean, namespace Verification
 theorem samples_artifact : Samples.all.all agrees = true
```

Here `4294967295` is the i32 bit pattern for signed `-1`. All other sample returns are small nonnegative i32 values. The exact sample inputs, capacities, expected returns and expected output bytes are the 28 named definitions in [Proofs/Samples.lean](Proofs/Samples.lean), also recorded as readable data in [verification/cases.json](verification/cases.json).

`Verification.agrees c` requires all of the following: the execution returns `c.result` within its stated fuel; the first `c.output.length` destination bytes equal `c.output`; and **every logged memory access**, including accesses beyond the returned output length, satisfies `Wasm.eventSafe`. It cannot succeed on fuel exhaustion, a trap, an unsupported instruction or a call to an unmodeled helper. Addresses are `src = 131072`, `dst = 262144`; initial memory contains the actual module data segments and sample input, with other bytes zero.

`admissible` checks byte values, disjoint buffers, their address bounds, and that expected content fits the capacity. `formatAgrees` checks the independent format specification for every successful case: `result = output.length`, `LZ4.relaxedDecode input output`, and `LZ4.validIndependent input output` except for the explicitly named `relaxed_end` case. Error cases make no format assertion. Definitions are in [Proofs/Claims.lean](Proofs/Claims.lean), [Proofs/Wasm.lean](Proofs/Wasm.lean) and [Proofs/Format.lean](Proofs/Format.lean).

There is also one theorem for each sample, in [Proofs/Traces.lean](Proofs/Traces.lean), with the exact statement schema

```lean
 theorem Verification.run_NAME :
   Verification.agrees Samples.NAME = true
```

`NAME` ranges over exactly the names in `Samples.all`. These theorems imply `samples_artifact`; they use kernel-checked short execution equalities and the proved `Wasm.run_join` composition lemma. No `sorry`, extra assumed correctness axiom, `native_decide`, or trusted compiled evaluation supplies these proofs.

| Requirement | Established result | Remaining gap |
| --- | --- | --- |
| R1 | `zero_input` proves that every zero-length input returns `-1` after five instructions, without any reads or writes, for arbitrary memory and arguments. `samples_artifact` proves the access restriction for all 28 concrete executions, with `buffers_admissible` establishing their preconditions. | No invariant covering all inputs, buffer placements, initial destination contents, length-extension loops and fast/slow paths was proved. |
| R2 | Twenty concrete valid independent blocks decode to their specified content and length, with sufficient capacity. This follows jointly from the three sample root theorems. Cases include literals, length extensions, overlapping matches, the fast loop, and wider copies. | No universal simulation/induction theorem from arbitrary valid sequences to artifact executions was proved. Finite executions do not establish it. |
| R3 | All 21 successful sample executions have the declared length and decoded sequence content, with offsets checked by the independent format specification. This includes one permitted relaxed-end block. Seven malformed/insufficient-capacity cases return `-1`. | No converse theorem for every possible successful artifact execution was proved. Rejection examples do not establish that all other malformed blocks are rejected. |

The independent format definition checks byte-valued inputs, nibble lengths, mandatory terminating extension bytes, little-endian offsets, positive offsets bounded by bytes already decoded, overlapping match expansion, and a final literal sequence. Strict validity additionally checks at least five final literals and the last match starting at least twelve decoded bytes before the end, with the all-literal exception. Its agreement with the English format document is a human review obligation.

## Connection to the actual artifact

The target is the original **7,161 bytes** of `lz4-flex.wasm`, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

[verification/extract.py](verification/extract.py) reads those binary bytes directly, verifies the hash and module structure, finds the exported `lz4_decompress`, verifies its signature and fixed 32-page memory, and decodes its body into **982 instructions and 24 locals**. It also extracts the active data segments. There is no import or start function. The instruction table in [Proofs/Artifact.lean](Proofs/Artifact.lean) is regenerated and compared exactly on every check. Branch targets are calculated from the binary's structured nesting; block signatures must be empty. Unsupported encodings fail extraction.

This is a Wasm operational model of the extracted instructions, **not** a hand-written model of the Rust algorithm. Its interpretation of the Wasm instructions and the binary extractor must be reviewed; there is no formal proof of the extractor or of equivalence to the complete official Wasm semantics. Calls are deliberately unsupported, and a checked returning trace therefore cannot assume a helper correct. The original Wasm and Rust source are not rebuilt or modified.

As a separate execution cross-check, a harness imports the original module and its memory into Wasmtime. It verifies all 28 return values, expected content, source preservation, and 16 guard bytes on each side of the destination capacity. These runtime checks alone neither observe reads nor prove R1. The harness also deliberately expects a wrong result and must trap.

## One check command

From this directory, offline:

```sh
./check.sh
```

The command validates and re-extracts the artifact, checks generated sample/certificate consistency, recompiles every local proof module from source, exports all root proofs and their transitive dependencies, audits axioms and root presence, and replays the proof objects through:

1. Lean 4.35's kernel during fresh compilation;
2. `/opt/lean/bin/con-ron --verified --jobs=2`;
3. `/opt/lean/bin/nanoda_bin`, with an explicit axiom allowlist and hard rejection of other axioms.

The independent kernels must first accept a positive control and must then reject **well-formed but ill-typed proof objects** claiming `0 = 1` and `False` using a proof of `0 = 0`. The objects have valid expression references; the check requires a type-error diagnostic, not merely a parse failure. Lean's own kernel is separately given both false declarations directly through `addDecl` and must reject both. Empty exports and missing roots are rejected by the export audit. The permissive `leanchecker --from-export` invocation that accepted an empty/irrelevant export during setup is not used; `lean4lean` could not read this installation's olean header and is not counted as a replay.

Success is exit code zero followed by:

```text
PASS: artifact-bound partial proofs, independent replay, false-proof rejection, runtime checks
UNRESOLVED: R1, R2, R3 for arbitrary inputs; this is not a full verification.
```

The completed run on 2026-10-29 exited **0**. Con-ron accepted **16,953** declaration records in verified mode; Nanoda checked **17,134** declarations with zero typechecking errors (it additionally generates datatype declarations). The 11,482,608-byte export contains 8,790 definitions, 8,089 theorems, 72 inductive blocks, one opaque declaration and the single standard axiom `propext`. Both independent kernels rejected both forged proofs, Lean rejected both direct false declarations, and the 28-case Wasmtime harness passed and rejected its wrong-expectation control.

Any failed assertion, build, kernel replay, negative control or runtime check gives a nonzero exit status. Logs, the exported proof stream, kernel binary hashes, axiom inventory and exact source-size inventory are written under `verification/out/`; the machine-readable index is `verification/out/summary.json`. Nanoda may report a cosmetic inability to pretty-print axioms; its typechecking must report zero errors.

## Review surface and trust

The semantic review surface consists of `Proofs/Wasm.lean`, `Proofs/Format.lean`, `Proofs/Claims.lean`, and `Proofs/Cases.lean`, plus the 28 one-line execution statements in `Proofs/Traces.lean`. Read the definitions behind the four root statements; a kernel cannot establish that these definitions express the English requirements.

Measured project review sizes (physical lines, including comments, blank lines and proof bodies) are:

| Part | Lines | Bytes |
| --- | ---: | ---: |
| Four semantic/claim files just named | 349 | 14,071 |
| Extraction, export, orchestration, negative controls and runtime-check files | 415 | 18,411 |
| Combined project review files | 764 | 32,482 |
| Generated artifact statement data (`Artifact.lean`) | 1,970 | 70,158 |
| Generated sample statement data (`Samples.lean`) | 42 | 5,486 |
| Generated proof certificates (`Traces.lean`, including 28 execution declaration lines) | 31,790 | 5,572,965 |
| Untrusted certificate search (`traces.py`) | 165 | 7,665 |

The 764-line total is an upper bound for handwritten project code review, not the size of the complete trusted toolchain. It excludes the generated statement data, which are counted separately rather than hidden, and the 28 generated execution statement lines. Standard-library dependency declarations are separately included in the exported closure and replayed; the check records the closure's declaration and axiom inventory. The readable JSON sample duplicate is 1,115 lines / 12,067 bytes.

The binary-to-statement connection additionally depends on `verification/extract.py`. The orchestration, export audit, negative controls and runtime checks are in `check.sh`, `verification/check.py`, `verification/checkers.py`, `verification/export.lean`, `verification/samples.py`, `verification/runtime.py`, `verification/Negative.lean`, and `verification/KernelNegative.lean`. Their exact sizes and hashes are measured by the check command. The README and the 244-line format document remain the normative English requirements.

`Proofs/Artifact.lean` and `Proofs/Samples.lean` are generated statement data; their contents are checked against the pinned artifact and explicit samples. `Proofs/Traces.lean` contains generated proof-only intermediate states and proofs. Those intermediate definitions do not occur in the exported claims' statements. The 165-line `verification/traces.py` is untrusted proof search: all transitions it proposes are checked by the kernels, and it may be replaced without changing the claims. It does not provide an assumed theorem.

The remaining infrastructure assumptions are the installed Lean elaborator/exporter and standard datatype semantics, the independent checker implementations and their permitted standard logical axioms, Python and SHA-256/file handling for the artifact binding, `wasm-tools` for independent binary validation, Wasmtime for the runtime cross-check, and the operating system/hardware. Independent replay and negative controls reduce dependence on one checker; they do not formally verify these tools.
