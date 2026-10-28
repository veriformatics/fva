# Verification report

**Incomplete: R1, R2, and R3 are not proved in general. No counterexample to them was established.** The results below are machine-checked, explicitly scoped facts about the shipped WebAssembly. They do not establish the README's universal requirements. In particular, successful tests and bounded executions are not being presented as universal proofs.

## Check command

From this directory, with the supplied offline toolchain:

```sh
python3 verification/check.py
```

The command deletes and rebuilds only the local `.lake/build` products. It needs no network and leaves the C sources and `lz4-c.wasm` unchanged. It regenerates checking outputs under `verification/`. Expect several minutes of checking and substantial memory use; the proof-producing evaluator generates a large proof term.

Success requires exit status 0 and these final lines:

```text
CHECK PASSED: scoped theorems replayed; false proofs rejected; Wasmtime cases passed.
R1, R2, R3 remain UNPROVED in general. See VERIFICATION.md.
```

The complete command passed in this workspace in 460.8 seconds, including a clean local rebuild. Its output is retained in `verification/check-final.log`.

An earlier success message from any one subprocess is insufficient. Any missing kernel, rejected positive proof, unapproved axiom, absent exported theorem, incorrect negative-control outcome, binary identity mismatch, or failing runtime assertion aborts the check.

## Results by requirement

### R1: partial only

`Proofs/Results.lean` proves the following two statements. `m : Wasm.Memory` is arbitrary; it is not restricted to zero-filled memory. Addresses are the fixed, valid, nonoverlapping caller addresses 131072 and 262144. Return values here are unsigned i32 bit patterns: 4294967295 denotes -1.

```lean
theorem zero_source_zero_capacity (m : Memory) :
    outcome (execute 40 131072 262144 0 0 m) = some 4294967295 ∧
    accesses (execute 40 131072 262144 0 0 m) = [] ∧
    unchanged m (execute 40 131072 262144 0 0 m)

theorem empty_block_zero_capacity (m : Memory) :
    outcome (execute 40 131072 262144 1 0 m) =
      some (if m 131072 % 256 = 0 then 0 else 4294967295) ∧
    accesses (execute 40 131072 262144 1 0 m) = [⟨false,131072,1⟩] ∧
    unchanged m (execute 40 131072 262144 1 0 m)
```

`accesses` records every load/store executed by the interpreter, in execution order. Each record gives write/read, start address, and byte width. `unchanged` means equality of the entire memory function. `execute` runs at most the specified number of Wasm instructions; `outcome = some ...` requires an actual return, not exhaustion of that bound or a trap.

The additional theorem, in the same file, is:

```lean
theorem concrete_cases : cases.all checkCase = true
```

`cases` and `checkCase` are definitions in that file, not opaque test oracles. For each listed initial memory, this proves termination within its instruction bound, the exact return bit pattern, every listed output byte, and that **every byte of every recorded access** satisfies the R1 address restriction. Reads from destination memory are included. It does not assert that these initial memories cover all inputs.

General R1 remains unproved: there is no inductive invariant covering every decoder/copy loop, arbitrary source contents, capacities, and buffer placements. A finite instruction bound used for these cases cannot substitute for such an invariant.

### R2: partial only

`empty_block_zero_capacity` proves the decoder's empty-block behavior at the stated placement, for arbitrary initial memory, including the README's special zero-capacity convention. When the input byte is zero, it returns zero without changing memory.

`concrete_cases` proves the exact positive executions listed below. Their interpretation as particular LZ4 sequences can be checked against the format document. **There is no general formal LZ4 validity/decoding relation in this development.** In particular, these execution facts are not a theorem quantifying over all valid independent blocks.

| Case | Source bytes (hex) | Capacity | Signed return | Checked content |
|---|---|---:|---:|---|
| No source | empty | 1 | -1 | none |
| Empty, no capacity | `00` | 0 | 0 | empty |
| Empty, with capacity | `00` | 1 | 0 | empty |
| One literal | `10 41` | 1 | 1 | `A` |
| Five literals | `50 41 42 43 44 45` | 5 | 5 | `ABCDE` |
| Extended literal length | `f0 00`, then 15 copies of `41` | 15 | 15 | 15 copies of `A` |
| Overlapping match | `13 41 01 00 50 42 43 44 45 46` | 13 | 13 | 8 copies of `A`, then `BCDEF` |
| Offset zero, extended match | `0f 00 00 01 50 42 43 44 45 46` | 25 | 25 | 20 zero bytes, then `BCDEF` |
| Offset before output | `13 41 02 00 50 42 43 44 45 46` | 13 | -5 | none asserted |

All cases use source 131072, destination 262144, and initially fill the destination capacity with byte 165. The offset-zero case therefore tests clearing, rather than relying on initially zero output. It concerns the R3 exception, not a valid-block instance of R2. The exact instruction bounds and byte lists are in `cases`.

General R2 remains unproved: no proof connects the decoder's optimized copy loops to a formal LZ4 decoding relation for arbitrary valid blocks.

### R3: partial only

The two symbolic-memory theorems and `concrete_cases` above establish those particular return/output facts, including an accepted offset-zero match and rejection of one offset that exceeds the decoded prefix. They do not establish that all successful executions parse into the required sequences, or that arbitrary offset-zero matches decode as zeroes.

General R3 remains unproved: a soundness proof needs a format relation, complete parsing/length invariants, and a correspondence between the bytes copied by every successful machine path and that relation. This development has none of those general theorems. No input demonstrating a failure of R3 was found.

## Connection to the shipped artifact

The checked binary is exactly 8,469 bytes, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`verification/embed.py` embeds those exact bytes in `Proofs/Bytes.lean`, divided into 256-byte chunks. The check both verifies the digest and compares the generated text with the checked-in embedding. It also tests that a changed byte fails the identity predicate.

`Proofs/Binary.lean` parses sections, LEB immediates, function locals, and instruction bytes from that embedding. There is no transcription of the C decoder into Lean. `verification/decode.py` generates instruction caches in `Proofs/Code.lean`; the following theorems in that generated file verify those caches against the Lean binary parser:

```lean
theorem linked2 : parseFunction 2 = some cached2
theorem linked3 : parseFunction 3 = some cached3
theorem linked4 : parseFunction 4 = some cached4
```

Function 2 is the decoder; 3 and 4 are its reachable copy helpers. `Proofs/Wasm.lean` interprets these cached instructions using i32 arithmetic, operand stacks, function calls, empty-type blocks/loops, branches, bounded memory loads/stores, and access recording. Unsupported instructions/calls produce a trap, which cannot satisfy the positive execution checks. The interpreter is handwritten **Wasm semantics**, not a handwritten LZ4 algorithm. Its correspondence to the WebAssembly standard is a review assumption, not a theorem proved here.

The following additional exact statements, in `Proofs/Results.lean`, check relevant module metadata and initialized data:

```lean
theorem module_memory : getSection 5 = some [1,1,32,32]
theorem module_functions : getSection 3 = some [6,0,1,1,2,2,2]
theorem module_types : getSection 1 = some
  [3,96,6,127,127,127,127,127,127,1,127,96,4,127,127,127,127,1,127,96,3,127,127,127,1,127]
theorem module_exports : getSection 7 = some
  [3,6,109,101,109,111,114,121,2,0,20,76,90,52,95,99,111,109,112,114,101,115,115,95,100,101,102,97,117,108,116,0,1,
   19,76,90,52,95,100,101,99,111,109,112,114,101,115,115,95,115,97,102,101,0,2]
theorem module_data : dataSegment = some (65536, expectedData)
```

`expectedData` is the explicit 64-byte list in that file. These facts identify fixed 32-page memory, function types/indices, exported names, and the tables used by the interpreter's concrete initial memories. The supplied `wasm-tools` validates the unchanged binary. Separately, `verification/runtime.py` embeds that same unmodified binary in WAST test modules and checks all nine exact return/output results in Wasmtime. No C compiler, build equivalence assertion, or source model is trusted for these results.

## Independent replay and negative controls

The check first rebuilds with Lean 4.35 and replays the resulting declarations with `leanchecker-paranoid`. It then exports the dependency closure of every theorem listed in `verification/roots.txt`, confirms all those theorem records are present, checks the axiom list, and replays the same export in:

- Nanoda, an independent Rust kernel;
- Con-Ron, its default `--verified` mode, with two workers.

Both accepted the positive proofs in the initial replay: Con-Ron counted 989 declaration records; Nanoda checked 1,156 declarations/constants. These counters use different units. Nanoda also prints `Unable to print axioms` as a pretty-printer diagnostic; it reports no typechecker errors and exits zero. The single check command repeats both replays and requires both to accept. No `native_decide` or compiler-trust axiom is used. The reported theorem dependencies use `propext` and, for the empty-block/concrete execution proofs, `Quot.sound`. The export checker permits only the standard `propext`, `Quot.sound`, and `Classical.choice`; it rejects `sorryAx`, `Lean.trustCompiler`, and custom axioms.

`verification/ProbeGen.lean` intentionally bypasses the frontend's kernel check **only in a separate negative-control module**. It writes a theorem whose type is `0 = 1` and whose proof is `Eq.refl 0`. The ordinary frontend rejects the same false claim without that bypass. Each replay kernel must reject the forged declaration specifically for a type mismatch. Nanoda reports this mismatch through an assertion panic (exit 101); the script checks that diagnostic, rather than accepting arbitrary command failures. Con-Ron and the paranoid checker name the bad theorem. The bad module is never imported by `Proofs`.

The Wasmtime harness also has a negative control: a deliberately wrong expected assertion must fail. Lean4Lean was tried but could not read this installation's `.olean` header; it is not counted as a successful replay or required by the check.

## Review surface and trust

Read the exact theorem statements **and all their local semantic definitions** in these files:

| Files | Physical lines | UTF-8 bytes |
|---|---:|---:|
| `Proofs/Binary.lean`, `Proofs/Wasm.lean`, `Proofs/Results.lean` | 361 | 14,588 |
| Generated byte/instruction constants: `Proofs/Bytes.lean`, `Proofs/Code.lean` | 1,366 | 50,335 |

Also read the three linkage theorem statements and `function` routing (5 lines, 323 bytes) in `Proofs/Code.lean`, and `Artifact.byteAt` (3 lines) in `Proofs/Bytes.lean`. Including these generated but semantic lines, the local formal review surface is **369 lines, 14,994 bytes**; the size script reports it separately. The chunk/instruction literal payloads remain machine-compared data.

The first row deliberately counts proof bodies, comments, and blank lines as well; it is a conservative size for the local statements/semantics review. Apart from the eight semantic lines just identified, the second row is generated data. The byte embedding is compared to the pinned artifact, and the instruction caches have the checked linkage theorems above. A reviewer can rely on those checks instead of manually comparing 8,469 bytes or auditing a C-to-Lean translation.

Also review the check driver, generators, runtime harness, exporter wrapper, negative-control generator, cases, theorem-root list, and size script. Together these checking-support files occupy **268 lines, 14,268 bytes**. Their exact per-file sizes and total are produced by `python3 verification/size.py` in `verification/sizes.json`. They are separate from the 369-line formal review surface; the whole local checking pipeline is not claimed to be only 369 lines. `verification/census.json`, produced on a successful complete run, records the exported declaration census, axioms, roots, and elapsed time.

The larger external trust assumptions are ordinary Lean/Nat/List/Option/Bool/Int meanings, the permitted foundational axioms, installed kernel implementations and runtimes, OS/filesystem/process behavior, and SHA-256 identity checking. The kernels recheck exported library dependencies, but their intended mathematical meaning is still part of interpreting the statements. Tool binaries and foundational library sources are not included in the local line counts. Independent replay reduces reliance on a single kernel; it does not remove these assumptions or prove the custom Wasm interpreter faithful.

The intended requirements also require reading the original `README.md` (18 lines, 2,872 bytes) and `lz4_Block_format.md` (244 lines, 10,683 bytes). These normative documents are separate from the Lean review-size totals; the general format semantics have not been formalized.

The source, binary, README, and format document were not rewritten. The remaining universal verification work is explicitly outstanding.
