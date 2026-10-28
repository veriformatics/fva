# Verification report

**Partial verification. R1, R2, and R3 remain unproved in their full generality.
No counterexample to any of them was established.** The results below establish
specific executions and two restricted results quantified over initial memory;
they must not be interpreted as proofs of the three universal requirements.

## Artifact and connection to the proofs

The artifact is the unchanged `lz4-c.wasm`: 8,469 bytes, SHA-256
`8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`.
`wasm-tools validate` accepts it.

`verification/extract.py` checks this size and digest and decodes its binary
sections directly. It checks the fixed 32-page memory, global initializer,
function signatures, exports, and active data segment; there are no imports or
start function. Starting at exported function 2 (`LZ4_decompress_safe`), its
direct-call closure is exactly functions 2, 3, and 4. The generated
`Proofs/Artifact.lean` contains those instructions and the initial data. Other
function slots are empty placeholders and are never reached by these results.
The extractor rejects unsupported instructions and block types. `--check`
regenerates the entire Lean file in memory and compares it with the saved file.

`Proofs/Wasm.lean` supplies an executable semantics for that reachable subset:
unsigned i32 values with arithmetic modulo 2^32, signed comparison, operand and
call stacks, block/loop labels and branch stack restoration, and little-endian
loads/stores. Effective load/store addresses do not wrap, and accesses beyond
2 MiB fail. Every load and store records its address, width, and direction.
Memory is a finite map over zero-filled memory; stored values are interpreted
as bytes. Calls are executed instruction by instruction, including the actual
compiled copy helpers. There are no summaries assuming `memcpy` is safe.

The extractor and this Wasm semantics are **reviewed assumptions**, not formally
verified translations of the WebAssembly specification. These are proofs about
the extracted model, connected to the artifact by the checked extraction.
Neither the C source nor the compiler nor `build.sh` is used to justify them.

As a separate execution check, `verification/check_runtime.py` embeds the exact
binary in WAST tests and calls its export in Wasmtime. For every listed case it
compares the return value and **every byte of all 2 MiB of final memory** with
the model. This comparison does not observe reads, and does not replace a
general simulation proof between the model and WebAssembly.

## Exact statements of the finite-case theorems

All these declarations are in `Proofs/Cases.lean`, in namespace
`Verification.Cases`. Their exact statements, with names relative to that
namespace, are:

```lean
theorem empty_zero_capacity : check cases[0]! = true
theorem empty_positive_capacity : check cases[1]! = true
theorem no_input : check cases[2]! = true
theorem literal_one : check cases[3]! = true
theorem literal_one_no_capacity : check cases[4]! = true
theorem overlap_offset_one : check cases[5]! = true
theorem offset_zero : check cases[6]! = true
theorem literal_extension : check cases[7]! = true
theorem shortcut : check cases[8]! = true
theorem truncated_extension : check cases[9]! = true
theorem offset_before_output : check cases[10]! = true
theorem literal_at_memory_end : check cases[11]! = true
```

Each is proved by `decide`, with reduction checked by Lean's kernel. No
`sorry`, custom axiom, `native_decide`, or external solver certificate is
used. The axiom audit reports exactly `[propext]` (Lean's standard
propositional extensionality axiom) for each of the fourteen theorems.
`verification/Audit.lean` prints these dependencies.

The definition `check c` asserts all of the following:

1. The source and destination buffers satisfy the address and non-overlap
   preconditions. Sizes are natural numbers within the fixed memory.
2. Executing function 2 finishes within 12,000 instruction steps, rather than
   trapping or exhausting the fuel, and returns `c.expectedReturn`.
3. Every recorded memory access satisfies `r1`: for each byte in the user
   address range, writes are in the destination buffer and reads are in the
   source or destination buffer. This includes accesses before a negative
   return, and all speculative/wild-copy bytes.
4. For cases flagged `valid`, `r2` checks that the input is a valid independent
   block under `Proofs/Format.lean`, including end conditions, that the expected
   output fits the capacity and the special zero-capacity rule, and that the
   actual length and bytes equal that output.
5. `r3` checks that whenever the returned i32 is nonnegative, its value is at
   most the capacity and a format parse consumes the entire input and produces
   exactly the returned output. That parse enforces offsets within already
   decoded output, allows offset zero with zero-filled match content, and
   omits the end-of-block restrictions, as R3 permits.

`Proofs/Format.lean` is a separate executable specification. It parses tokens,
literal and match length extensions, literals, little-endian offsets, and
overlapping matches. It checks the entire input consists of bytes. Its validity
predicate requires a final literal-only sequence and the end conditions. The
12-byte condition is measured in decoded output positions. Agreement between
these definitions and the English format document requires review; it is not
itself a theorem about the document.

The exact fixtures, addresses, expected bytes, and initial memory are defined
in `cases` and `initialMemory` in `Proofs/Cases.lean`. Except for the last case,
source is 131072 and destination is 262144. The destination initially contains
0xA5, source contains the given input, and other user memory is zero. The last
case has source 2097150 and destination 131072. Here are the inputs in hex:

| Index | Case | Input | Capacity | Signed return |
|---:|---|---|---:|---:|
| 0 | Empty, zero capacity | `00` | 0 | 0 |
| 1 | Empty, positive capacity | `00` | 1 | 0 |
| 2 | No input | empty byte string | 1 | -1 |
| 3 | One literal | `10 41` | 1 | 1 |
| 4 | No capacity for literal | `10 41` | 0 | -1 |
| 5 | Overlapping match, offset 1 | `13 41 01 00 50 42 43 44 45 46` | 13 | 13 |
| 6 | Offset zero | `03 00 00 50 41 42 43 44 45` | 12 | 12 |
| 7 | Extended literal length | `f0 00 41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f` | 15 | 15 |
| 8 | Copy shortcut | `84 41 42 43 44 45 46 47 48 08 00 80 49 4a 4b 4c 4d 4e 4f 50` | 64 | 24 |
| 9 | Truncated extension | `f0` | 64 | -2 |
| 10 | Offset before output start | `00 01 00 50 41 42 43 44 45` | 64 | -4 |
| 11 | Literal at memory end | `10 5a` | 1 | 1 |

Returns are stored as unsigned i32s in Lean; for example -1 is 4294967295.

## Exact statements quantified over initial memory

`Proofs/Boundary.lean` contains these theorems in namespace
`Verification.Boundary`, with `Wasm` opened:

```lean
theorem no_input_any_memory (m : Memory) :
    invoke Artifact.program 50 2 [131072, 262144, 0, 1] m =
      some ⟨4294967295, m, []⟩

theorem zero_capacity_single_byte (m : Memory) :
    invoke Artifact.program 50 2 [131072, 262144, 1, 0] m =
      some ⟨(if byte m 131072 = 0 then 0 else 4294967295), m,
        [⟨false, 131072, 1⟩]⟩
```

Both proofs are `rfl`, checked by the kernel. The first establishes that this
zero-input call returns -1, makes no memory accesses, and changes no memory,
for every initial memory. The second establishes that this zero-capacity,
one-byte-input call reads exactly the source byte, makes no writes, and accepts
exactly byte zero, for every initial memory. The 50-step fuel suffices for both.
They do not quantify over other addresses or sizes.

## Status of each README requirement

| Requirement | Established result | Remaining gap |
|---|---|---|
| R1 | All twelve finite-case theorems establish the full access predicate for their executions. Both boundary theorems establish the stated access traces for arbitrary initial memory. | No bounds invariant was proved across arbitrary literal/match extension loops, optimized copies, and helper calls for all legal buffers and input bytes. R1 as a whole is unproved. |
| R2 | Cases 0, 1, 3, 5, 7, 8, and 11 establish correct length/content for valid independent blocks. The second boundary theorem also covers empty input byte zero with capacity zero at the specified addresses for arbitrary initial memory. | No inductive refinement proof relates all valid format sequences to all successful decoder paths. General lengths, offsets, capacities, addresses, and initial memories are not covered. R2 as a whole is unproved. |
| R3 | The eight nonnegative-return cases (0, 1, 3, 5, 6, 7, 8, 11) establish a complete parse with the permitted relaxations and correct output. Negative-return cases satisfy the implication vacuously. The second boundary theorem characterizes success for its one-byte, zero-capacity calls. | No invariant establishes that every possible successful path has such a parse and output. R3 as a whole is unproved. |

In particular, the rejected malformed inputs in the table are **not** evidence
that a requirement fails, and passing examples are **not** exhaustive verification.

## Reproduction, without network access

Run from this directory, using the installed tools and already-built Mathlib:

```sh
python3 verification/extract.py --check
wasm-tools validate lz4-c.wasm
lake build
lake env lean Proofs/Cases.lean
lake env lean Proofs/Boundary.lean
lake env lean verification/Audit.lean
python3 verification/check_runtime.py
```

Every command must exit zero. Extraction prints `PASS: exact artifact digest,
interface, reachable code and data`. Validation and the direct Lean proof
checks normally print nothing. `lake build` reports success. Direct Lean checks
force proof rechecking even if Lake's local build cache is populated; allow a
few minutes for the finite-case reduction proofs. The audit must print
`depends on axioms: [propext]` for all fourteen declarations. Runtime checking
prints twelve individual `PASS` lines and ends with
`PASS: 12 exact-artifact Wasmtime checks`. Wasmtime's compilation cache is
disabled; the harness uses a temporary directory and does not modify the
artifact. No source rebuild, download, or network access is required.

## Review and trust inventory

Sizes below are lines and bytes, as reported by `wc -l -c`. Generated code is
listed too: it may be reviewed directly or checked via the extractor.

| File | Lines | Bytes | Why it matters |
|---|---:|---:|---|
| `Proofs/Wasm.lean` | 201 | 7008 | Meaning of Wasm execution and recorded accesses; primary semantic trust boundary |
| `verification/extract.py` | 194 | 6848 | Binary decoding, reachable-code extraction, digest/interface/data checks |
| `Proofs/Artifact.lean` | 898 | 12927 | Generated exact reachable instruction model and initial data |
| `Proofs/Format.lean` | 63 | 2343 | Meaning of format validity, relaxed parsing, and decoded content |
| `Proofs/Cases.lean` | 105 | 4449 | Fixtures, initial states, requirement predicates, and twelve proofs |
| `Proofs/Boundary.lean` | 19 | 602 | Exact scope and statements of the two quantified results |
| `Proofs.lean` | 2 | 43 | Library root importing all proofs |
| `verification/Export.lean` | 20 | 761 | Exports computed model states for the independent runtime checks |
| `verification/check_runtime.py` | 89 | 3013 | WAST harness generation and complete final-memory comparison |
| `verification/Audit.lean` | 16 | 739 | Axiom dependency audit |
| `README.md` | 18 | 2872 | Requirements and artifact identity |
| `lz4_Block_format.md` | 244 | 10683 | English specification used to review the format model |
| `lakefile.toml` | 12 | 264 | Build configuration |
| `lean-toolchain` | 1 | 25 | Lean 4.35.0 selection |
| `lake-manifest.json` | 117 | 3536 | Dependency versions and locations |

The executable proof checker is Lean 4.35.0's kernel and its imported libraries
(Mathlib v4.35.0 and Lean's standard library), with standard propositional
extensionality (`propext`) as reported by the audit. The installed toolchain and
prebuilt library files are trusted infrastructure, not newly verified here.
Python 3 and its SHA-256 implementation are trusted for extraction and harness
generation; Wasmtime 50.0.0 and wasm-tools 1.262.0 are trusted for the independent
runtime/validation results. The native Lean compiler is used by the JSON
exporter, but not to justify any of the fourteen theorems. The runtime harness
and exporter are not dependencies of those proofs. The format document and
the Wasm/format model correspondence must be read critically; no claim of a
fully verified WebAssembly interpreter or end-to-end universal verification is
made.
