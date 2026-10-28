# Verification of `lz4-c.wasm`

## Outcome

**Partial verification. None of R1, R2, or R3 is proved in its full generality,
and no counterexample to any of them was found.** This report does not certify
the artifact as meeting all requirements.

There are 20 kernel-checked Lean theorems: six about early exits and zero output
capacity, nine about concrete executions of extracted WebAssembly, and five
about the format and expected content of example blocks. Additional runtime
checks pass on the unmodified artifact and on a copy instrumented to check
every memory load and store. Tests are evidence about the listed cases, not
universal proofs.

| Requirement | Proved portion | Remaining gap |
| --- | --- | --- |
| R1 | `zeroCapacity_other` proves no memory access at all for zero capacity and input size other than one, for arbitrary memory, source address other than zero, and destination address. `zeroCapacity_safety` covers **every** zero-capacity call with source address 131072, arbitrary memory, input size, and destination address. All nine execution examples also check the entire access trace. | No invariant proves the memory bounds through every iteration of the decoder and copy loops for arbitrary inputs with positive capacity. No general termination proof is provided. |
| R2 | `zeroCapacity_empty` proves decoding of the specified empty block for arbitrary memory with byte zero at source address 131072 and arbitrary destination address. The empty, literal, overlapping-match, and literal-extension examples have checked format membership, expected content, and successful execution. | No refinement proof relates **all** valid independent blocks to executions of the extracted decoder, for arbitrary buffer locations, capacities, and initial memories. The format model is constructive and does not cover every possible final-token low nibble. |
| R3 | `zeroCapacity_sound` proves that a nonnegative return with zero capacity and source address 131072 implies input size one, source byte zero, return zero, unchanged memory, and exactly one source-byte read. The successful execution examples have checked return lengths, content, and traces, including the permitted zero-offset case. | No theorem extracts a format derivation from **every** successful execution with positive capacity. The general offset/history and output-content invariants are unproved. |

For application to the README, arguments must satisfy its caller-buffer and
`i32` preconditions. In particular the fixed source address 131072 is an allowed
address, but the quantified results with that address do not claim coverage of
other source addresses. `emptySource` is specifically about source address
131072 and capacity **13**, not every capacity.

## Connection to the shipped bytes

The checked artifact is exactly 8,469 bytes with SHA-256

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`verification/extract.py --check` checks this size and digest, parses the binary
sections directly, checks the exports and fixed 32-page memory, and compares
its deterministic Lean output byte for byte with `Proofs/Artifact.lean`.
The extracted function numbers are 2 (`LZ4_decompress_safe`), 3 (`memcpy`), and
4 (`memmove`). Their function types, local counts, instructions, immediates,
structured blocks, loops, and initial data bytes come from the binary. The
decoder's suffix is named `decoderRest` only to keep its generated expression
manageable. The compressor is omitted from the model.

`Proofs/Wasm.lean` defines an executable semantics for the instruction subset
used by those functions: modulo-2^32 integer arithmetic, signed and unsigned
comparisons, little-endian memory, locals, operand stacks, calls, returns,
branches, and void blocks/loops. Loads and stores check the 2 MiB memory bound
and record address, width, and read/write direction. Unknown instructions,
unsupported constructs, traps, or exhausted fuel produce `none`, never a
successful result. Alignment hints do not restrict Wasm memory accesses.

`Memory` is a finite association list with newest binding first, zero for an
absent address, and bytes reduced modulo 256. An arbitrary finite 2 MiB byte
memory can be represented this way. The early-exit theorems quantify over
arbitrary such lists. Concrete examples start with zero memory, the artifact's
data segment at 65536, and their source bytes at 131072. Their destination is
262144. Results use unsigned `i32` representations: 4294967295 is return -1,
and values below 2147483648 are nonnegative returns.

**The kernel checks the theorems about this model, not an end-to-end theorem
about raw WebAssembly bytes.** Interpreting the theorems as artifact results
requires trusting the extractor and reviewing the Wasm semantics for adequacy.
No formal binary-parser correctness or official-Wasm-semantics adequacy theorem
is supplied. The C source, compiler, and `build.sh` are not used as a proof of
correspondence. The shipped artifact was not rebuilt or changed.

## Meaning of the execution predicates

All theorem names below are in namespace `Verification`. Their exact statements
are reproduced later in this report.

`invoke decoderModule fuel src dst size capacity m` executes function 2 and
returns an optional `Result` containing `value`, `memory`, and a reverse-order
access `trace`. The bounds used in `safeTrace` are half-open byte intervals.
It checks every byte of every access: below 131072 is unrestricted by R1;
otherwise writes must be in the destination, and reads must be in the source
or destination. A trapping or out-of-fuel run cannot satisfy these predicates.

The concrete predicates in `Proofs/Examples.lean` are exactly:

```lean
def outputBytes (m : Memory) (dst n : Nat) : List Nat :=
  (List.range n).map (fun i => readByte m (dst + i))

def exampleMemory (input : List Nat) : Memory :=
  putBytes (putBytes [] 65536 initialData) 131072 input

def decodes (input expected : List Nat) (capacity : Nat) : Bool :=
  match invoke decoderModule 2000 131072 262144 input.length capacity
      (exampleMemory input) with
  | none => false
  | some r =>
    r.value == expected.length &&
    outputBytes r.memory 262144 r.value == expected &&
    safeTrace 131072 262144 input.length capacity r.trace

def rejectsSafely (input : List Nat) (capacity : Nat) : Bool :=
  match invoke decoderModule 2000 131072 262144 input.length capacity
      (exampleMemory input) with
  | none => false
  | some r => 2147483648 ≤ r.value &&
    safeTrace 131072 262144 input.length capacity r.trace
```

The format definitions in `Proofs/Format.lean` construct literal/match sequences,
encode token nibbles, extension bytes, and little-endian offsets, and decode
matches one byte at a time from the growing output. `decodedBlock false`
requires positive offsets into the already decoded prefix; `decodedBlock true`
also permits zero offsets and emits zero bytes for them. `validIndependentBlock`
adds the five-final-literals and twelve-bytes-from-last-match conditions when
matches exist. It always constructs a final literal-only sequence and uses zero
for its unused token nibble. This is a reviewed model of the supplied format,
not a proven equivalence with its English text.

`overlapSequences = [⟨[65], 1, 7⟩]`,
`zeroSequences = [⟨[65], 0, 7⟩]`, and
`exampleTail = [66, 67, 68, 69, 70]`.
Thus the valid overlap example decodes to eight `A` bytes followed by `BCDEF`.
The zero-offset example decodes to `A`, seven zero bytes, and `BCDEF`;
`zeroOffsetFormat` also proves that it is invalid under strict independent-block
validity, as required by the distinction between R2 and R3.

## Reproduction

Run from this directory, without network access:

```sh
bash verification/check.sh
```

The script runs these checks in order (the temporary path is created with
`mktemp -d` and removed on exit):

```sh
python3 verification/extract.py --check
wasm-tools validate lz4-c.wasm
lake build
lake env lean Proofs/Results.lean
lake env lean Proofs/Examples.lean
lake env lean Proofs/Format.lean
lake env lean Proofs/Audit.lean
test "$(wasmtime -C cache=n --preload artifact=lz4-c.wasm --invoke check verification/smoke.wat)" = 1
python3 verification/instrument.py "$verification_tmp/instrumented.wasm"
wasm-tools validate "$verification_tmp/instrumented.wasm"
node verification/test.mjs "$verification_tmp/instrumented.wasm"
```

The three direct `lean` invocations re-elaborate every theorem file even if
Lake's build outputs are cached. Proofs use kernel reduction, `decide`, and
ordinary proof tactics. There is no `sorry`, added axiom, `native_decide`,
external decision oracle, or asserted successful execution used as a premise.
The audit prints `[propext]` for each of the 20 theorems; no other axiom appears.

Success means every command exits zero, the extractor prints its `PASS`, Lean
reports no error, every axiom line contains only `[propext]`, the Wasmtime smoke
test prints its `PASS`, and the final lines are:

```text
PASS: 83417 cases; 8833 nonnegative returns checked against grammar; 2416 valid-input expectations; 18831405 instrumented accesses
PASS: all partial-verification checks (full R1–R3 remain unproved)
```

The whole script was run successfully in this environment. The Wasmtime
experimental-`--invoke` warning is expected. Versions used: Lean 4.35.0,
Mathlib v4.35.0 as configured by this project, Python 3, Node v26.12.1,
Wasmtime 50.0.0, and wasm-tools 1.262.0. The existing Lake configuration uses
the already installed dependencies; no dependency download is needed.

## Runtime evidence and its limits

`verification/smoke.wat` imports the original module's memory and decoder using
Wasmtime's preload facility. It checks five actual calls: the overlap and
zero-offset examples, an invalid offset, insufficient capacity, and the empty
block. It checks successful return values and all successful output bytes.

`verification/instrument.py` disassembles the hash-pinned original, shifts
function indices for two check imports, and inserts a guard immediately before
each load/store. The guards preserve the instruction's operands. The original
artifact is also executed separately by Node's WebAssembly engine, and each
case compares both return values and the complete destination-capacity region
against the instrumented run. The access guards check R1 even on negative
returns. A separate JavaScript byte-at-a-time decoder checks the R3 implication
on every nonnegative return, allowing zero offsets and omitting end conditions.
For generated valid blocks, expected output is independently constructed and
compared, checking the R2 conclusion on those cases.

The deterministic suite includes:

- All 256 one-byte inputs at nine capacities, and empty input at nine capacities.
- All 65,536 two-byte inputs, each at **one** selected capacity/layout, not all
  capacity combinations.
- Literal lengths 0, 1, 4, 5, 12, 14, 15, 16, 269, 270, 271, 524, 525, 4096,
  final low nibbles 0–15, and exact/extra output capacity.
- Offsets 0–9, 15, 16, 31, 255, 256, 65535; match lengths 4, 7, 8, 11, 12, 15,
  16, 18, 19, 20, 273, 274, 275, 530; exact, extra, and insufficient capacities.
- 1,000 valid generated multi-sequence blocks, three mutations of each, and
  10,000 random byte strings, with fixed RNG seed `0x7834ab21`.
- Adjacent buffers in either order, buffers against the upper memory boundary,
  and separated, unaligned buffers.

These tests do not exhaust the input, capacity, address, or initial-memory
domains. Runtime destinations are initialized to `0xa5`; the formal concrete
examples instead use zero-backed memory. Only the quantified early-exit
theorems cover arbitrary initial memory. Runtime checks and validation do not
close the universal proof gaps in the outcome table.

## Review and trust inventory

Sizes below are `wc -l -c` counts (lines, bytes). All executable definitions and
scripts used by the results are listed; there is no hidden generated certificate.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 197 | 6731 | Wasm semantics, memory, invocation, R1 trace predicate; adequacy must be reviewed |
| `Proofs/Artifact.lean` | 895 | 19904 | Generated extracted functions and data; checked against binary by extractor |
| `Proofs/Format.lean` | 90 | 3751 | Constructive format model and five format theorems |
| `Proofs/Examples.lean` | 60 | 2315 | Execution predicates and nine concrete theorems |
| `Proofs/Results.lean` | 61 | 2339 | Six quantified/early-exit theorems |
| `Proofs/Audit.lean` | 22 | 870 | Axiom audit for all 20 theorems |
| `Proofs.lean` | 3 | 66 | Root imports |
| `verification/extract.py` | 171 | 5899 | Trusted byte-to-model bridge and hash/metadata checks |
| `verification/instrument.py` | 41 | 1896 | Instrumented-test construction; trusted only for runtime access evidence |
| `verification/test.mjs` | 177 | 7630 | Test generation, reference decoding, guards, assertions |
| `verification/smoke.wat` | 33 | 1654 | Wasmtime harness for the unchanged artifact |
| `verification/check.sh` | 19 | 853 | Reproduction driver |

The artifact is 8,469 bytes. The governing English requirements and format are
`README.md` (2,872 bytes) and `lz4_Block_format.md` (10,683 bytes). The source
files and build script are useful context but are not trusted correspondence
steps for these results.

For the mathematical proofs, trust Lean's kernel, its standard `propext` axiom,
and the meanings of the reviewed definitions. Tactic and compiler output used
to construct proofs is subsequently kernel checked; it is not accepted as an
execution oracle. For the connection to actual Wasm additionally trust Python's
binary reading/SHA-256 and the extractor's parsing. For runtime evidence also
trust wasm-tools, Wasmtime, Node's WebAssembly engine, and the listed harnesses.
No proof of those tools is provided. Standard tools and the installed Mathlib
distribution are external dependencies, not local proof files.

## Exact theorem statements

The declarations below omit only their proof terms. All names are fully
qualified by the `Verification` namespace. Definitions and fixed addresses
have the meanings stated above and in the cited files.

From `Proofs/Results.lean`:

```lean
theorem zeroCapacity_other (src dst size : Nat) (m : Memory)
    (hs : src ≠ 0) (hn : size ≠ 1) :
    invoke decoderModule 100 src dst size 0 m =
      some ⟨4294967295, m, []⟩

theorem zeroCapacity_unit (dst : Nat) (m : Memory) :
    invoke decoderModule 100 131072 dst 1 0 m =
      some ⟨(if readByte m 131072 = 0 then 0 else 4294967295), m,
        [⟨false, 131072, 1⟩]⟩

theorem zeroCapacity_empty (dst : Nat) (m : Memory) (h : readByte m 131072 = 0) :
    invoke decoderModule 100 131072 dst 1 0 m =
      some ⟨0, m, [⟨false, 131072, 1⟩]⟩

theorem emptySource (dst : Nat) (m : Memory) :
    invoke decoderModule 100 131072 dst 0 13 m =
      some ⟨4294967295, m, []⟩

theorem zeroCapacity_safety (dst size : Nat) (m : Memory) :
    ∃ r, invoke decoderModule 100 131072 dst size 0 m = some r ∧
      r.memory = m ∧ safeTrace 131072 dst size 0 r.trace = true

theorem zeroCapacity_sound (dst size : Nat) (m : Memory) (r : Result)
    (hr : invoke decoderModule 100 131072 dst size 0 m = some r)
    (hn : r.value < 2147483648) :
    size = 1 ∧ readByte m 131072 = 0 ∧ r.value = 0 ∧ r.memory = m ∧
      r.trace = [⟨false, 131072, 1⟩]
```

From `Proofs/Examples.lean`:

```lean
theorem emptyBlock : decodes [0] [] 0 = true

theorem literalBlock : decodes [48, 65, 66, 67] [65, 66, 67] 3 = true

theorem overlapBlock :
    decodes [19, 65, 1, 0, 80, 66, 67, 68, 69, 70]
      [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70] 13 = true

theorem zeroOffsetBlock :
    decodes [19, 65, 0, 0, 80, 66, 67, 68, 69, 70]
      [65, 0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70] 13 = true

theorem invalidOffset :
    rejectsSafely [19, 65, 2, 0, 80, 66, 67, 68, 69, 70] 13 = true

theorem undersizedOutput :
    rejectsSafely [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 12 = true

theorem truncatedLength : rejectsSafely [240] 100 = true

theorem literalExtension :
    decodes ([240, 0] ++ List.replicate 15 42) (List.replicate 15 42) 15 = true

theorem unusedFinalNibble : decodes [15] [] 1 = true
```

From `Proofs/Format.lean`:

```lean
theorem overlapFormat :
    validIndependentBlock overlapSequences exampleTail = true ∧
    encodeBlock overlapSequences exampleTail = [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] ∧
    decodedBlock false overlapSequences exampleTail =
      some [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]

theorem zeroOffsetFormat :
    encodeBlock zeroSequences exampleTail = [19, 65, 0, 0, 80, 66, 67, 68, 69, 70] ∧
    decodedBlock true zeroSequences exampleTail =
      some [65, 0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70] ∧
    validIndependentBlock zeroSequences exampleTail = false

theorem emptyFormat :
    validIndependentBlock [] [] = true ∧ encodeBlock [] [] = [0] ∧
    decodedBlock false [] [] = some []

theorem literalFormat :
    validIndependentBlock [] [65, 66, 67] = true ∧
    encodeBlock [] [65, 66, 67] = [48, 65, 66, 67] ∧
    decodedBlock false [] [65, 66, 67] = some [65, 66, 67]

theorem extensionFormat :
    validIndependentBlock [] (List.replicate 15 42) = true ∧
    encodeBlock [] (List.replicate 15 42) = [240, 0] ++ List.replicate 15 42 ∧
    decodedBlock false [] (List.replicate 15 42) = some (List.replicate 15 42)
```
