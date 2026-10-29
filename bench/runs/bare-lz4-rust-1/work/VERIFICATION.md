# Verification report

The universal requirements **R1, R2, and R3 remain unproved**. No counterexample
was found. This delivery contains bounded machine-checked results about a model
extracted from the shipped Wasm, an independent constructive LZ4 specification,
and matching executions of the original binary in Wasmtime. These results do
not certify the three requirements for all inputs.

## Requirement coverage

| Requirement | Established result | Remaining gap |
| --- | --- | --- |
| R1 | `bounded_artifact_checks` checks every modeled load/store range, including bulk operations, for every delivered case. Reads in the caller band are confined to the two buffers; writes there are confined to the destination. | No invariant establishing confinement for every possible execution, arbitrary initial memory, all capacities, and all legal buffer placements. Wasmtime replay does not trace reads. |
| R2 | All 27 strict block fixtures satisfy `LZ4.Block.valid`, fit their capacities, and produce the specified length and content, at four placements each. All 16 one-byte encodings of empty content also succeed at both tested capacities and four placements. | No proof covering all valid blocks, all contents, all initial memories, and all legal capacities/placements. The constructive format specification has not been formally related to the English document by a completeness theorem. |
| R3 | Every successful delivered execution has an independent sequence witness: its encoding equals the input, its offsets are positive and refer to already decoded bytes, its content equals the output, and its length is at most capacity. Two fixtures deliberately violate only end conditions and are accepted. | No theorem producing such a witness from an arbitrary successful execution of the artifact. |

The finite set is `Verification.cases` in `Proofs/Cases.lean`: 2,220 cases,
including duplicates. Before expanding placements there are 27 valid block
fixtures, two relaxed end-condition fixtures, 14 malformed/undersized-output
fixtures, and all 256 one-byte inputs at capacities 0 and 35. Each has four
placements: separated buffers, source ending at the top of memory, source
immediately after destination, and destination immediately after source.

The fixtures cover literal lengths 0, 1, 2, 3, 4, 5, 7, 8, 14, 15, 16, 17,
31, 32, 33, 269, 270, and 525; overlapping matches; offsets 1 and 2; both hot
match-copy paths; 32/64-byte wild copies; bulk copies; extended match lengths;
multiple sequences; truncated fields; invalid offsets; and insufficient
capacity. This is not a claim of exhaustive instruction-path coverage.

## Exact machine-checked statements

Namespaces and defining files matter: the statements below use the definitions
in the delivered Lean sources, not an implicit implementation of Wasm or LZ4.

`Proofs/Artifact.lean`, namespace `Artifact`:

```lean
theorem instruction_decode :
  Wasm.decodeBody body = some (localCount, code)
```

`Proofs/Results.lean`, namespace `Verification`:

```lean
theorem strict_inputs_valid :
  strictBlocks.all (fun (_, b, cap) => b.valid && b.decode.length ≤ cap) = true

theorem bounded_artifact_checks : cases.all Case.certify = true

theorem each_case_certified (c : Case) (h : c ∈ cases) : c.certify = true

theorem extension_accumulator_fits (n acc : Nat) (hn : n ≤ 1966080)
    (ha : acc ≤ 255*n+19) : acc < 4294967296
```

`Case.certify` checks the buffer preconditions, byte-valued input, normal
termination within 100,000 interpreter steps, exact return value, the complete
access trace, and unchanged source bytes. For an expected success it additionally
checks `b.relaxed`, `b.encode == input`, `b.decode.length ≤ cap`, and equality of
the returned content with `b.decode`. Expected errors must return the i32 word
4294967295, interpreted by the interface as -1. A trap, unsupported instruction,
or exhausted fuel fails certification; it is never treated as an error return.

The arithmetic theorem is a general bound, since the caller band has 1,966,080
bytes. It does **not** prove that a program accumulator satisfies its hypothesis,
nor that aggregate output-position arithmetic is correct.

`Proofs/Format.lean`, namespace `LZ4`:

```lean
theorem copyMatch_length (off n : Nat) (out : List Nat) :
  (copyMatch off n out).length = out.length+n

theorem Sequence.decode_length (s : Sequence) (out : List Nat) :
  (s.decode out).length = out.length+s.literals.length+s.matchLength

theorem valid_implies_relaxed (b : Block) (h : b.valid = true) :
  b.relaxed = true

theorem sequencesOK_head (s : Sequence) (ss : List Sequence) (pos : Nat)
    (h : sequencesOK (s::ss) pos = true) :
  1 ≤ s.offset ∧ s.offset ≤ 65535 ∧ s.offset ≤ pos+s.literals.length ∧
  4 ≤ s.matchLength
```

These general lemmas concern the independent format model, not the decoder's
machine code. `Block` supplies sequence boundaries as a witness. Its encoder
implements token nibbles, mandatory zero extension terminators, little-endian
offsets, and the final literal-only sequence. Its decoder copies matches
sequentially, allowing overlap. `relaxed` validates bytes, offsets, and minimum
match lengths. `valid` adds the final-literal and match-distance conditions.
Review these definitions against `lz4_Block_format.md`; the prose specification
has not itself been machine-checked.

## Connection to the exact artifact

The artifact was not rebuilt or changed. All checks require these exact bytes:

```text
lz4-flex.wasm
7161 bytes
SHA-256 1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

`verification/generate.py --check` hashes the binary, checks its module
structure (including no imports or start function, the decoder signature,
exports, fixed memory, and initial data), extracts function index 7, and
requires exact equality with the generated Lean source. The extracted body is
2,000 bytes, with 24 locals and 982 instructions. `instruction_decode` separately
checks the instruction decoding from those body bytes in Lean, including
structured-control targets. Python's extraction of sections and selection of
the function body remain trusted glue; the hash/extraction are not Lean proofs.

`Proofs/Wasm.lean` is a hand-written execution model for the instructions used
by this decoder. It models wrapping i32 arithmetic, unsigned comparisons and
shifts, operand/label stacks, locals, little-endian memory operations, bounds
traps, snapshot semantics for `memory.copy`, and `memory.fill`. It records
entire memory-access ranges. The model is not a verified implementation of an
official Wasm semantics. Wasm validation supplies typing; the interpreter does
not prove typing itself.

Every modeled case starts with zero memory below address 131072, overlaid with
the artifact's initial data, and byte 165 throughout the caller band, overlaid
with the case input. Thus the tests do not quantify over arbitrary initial
destination or surrounding memory. The model has a sparse map representation
of this memory. Calls are explicitly unsupported, so no successful certificate
can depend on the behavior of omitted callees or global state. The tested
executions return without calling them. Untested executions may call them.

`verification/replay.py` embeds the original binary bytes in a WAST script and
invokes its exported function with exactly the same 2,220 inputs, arguments, and
initial caller memory. Wasmtime checks return values, output bytes, unchanged
source bytes, and selected canaries outside the buffers. All passed. This is
an independent execution cross-check, not a refinement proof between the Lean
interpreter and Wasmtime and not an exhaustive check of external writes.

No assertion about the Rust compiler, build reproducibility, or correctness of
the vendored Rust source is used to connect these checks to the binary.

## Reproduction

From this directory, with the installed offline dependencies:

```sh
bash verification/check.sh
```

The script runs these exact commands in order:

```sh
python3 verification/generate.py --check
wasm-tools validate lz4-flex.wasm
lake build
lake env lean Proofs/Results.lean
python3 verification/replay.py
```

Success means exit status zero for every command, no Lean errors or missing
proof warnings, and these messages (along with build and axiom information):

```text
PASS: artifact SHA-256, module structure, and generated decoder model
PASS: 2220 original-artifact Wasmtime replays (returns, output, source, canaries)
PASS: all delivered checks; universal R1/R2/R3 remain unproved (see VERIFICATION.md)
```

The Wasm validator is silent on success. For a shorter diagnostic of the Lean
execution cases after building, run:

```sh
lake env lean --run verification/Export.lean --diagnose
```

Its success output is `PASS: 2220 execution certificates`. Replay creates its
WAST file in a temporary writable directory, disables Wasmtime's disk cache,
and needs no Python Wasmtime package. No command needs network access.

Checked with Lean/Mathlib v4.35.0, Wasmtime 50.0.0, wasm-tools 1.262.0, and
Python 3.14. A normal `lake build` may reuse compiled results; the explicit
`lake env lean Proofs/Results.lean` re-elaborates the main result proofs.

## What must be trusted and reviewed

The Lean interpreter and LZ4 definitions require review for the interpretation
of the results. Their correspondence to the published execution/format
semantics is a trust assumption, not a theorem supplied here. The generator,
replay harness, and case selection also require review. Sizes below include
comments and blank lines; generated data is listed separately.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 173 | 6763 | Execution semantics and access confinement predicate |
| `Proofs/DecodeWasm.lean` | 117 | 3472 | Binary instruction decoding and control-target construction |
| `Proofs/Format.lean` | 98 | 3772 | Independent format definitions and general lemmas |
| `Proofs/Cases.lean` | 117 | 4987 | Initial state, case set, certificate predicate |
| `Proofs/Results.lean` | 37 | 1539 | Main proofs and axiom audit commands |
| `Proofs/Artifact.lean` | 996 | 22162 | Generated body bytes, initial data, instructions, decoding check |
| `verification/generate.py` | 200 | 6349 | Artifact binding and generation |
| `verification/Export.lean` | 28 | 1158 | Native diagnostic and replay-case export |
| `verification/replay.py` | 72 | 3070 | WAST harness and Wasmtime invocation |
| `verification/check.sh` | 9 | 305 | Reproduction entry point |
| `Proofs.lean` | 1 | 22 | Library import |
| `README.md` | 18 | 2402 | Requirements |
| `lz4_Block_format.md` | 244 | 10683 | Prose format specification |
| `lakefile.toml` | 12 | 264 | Build configuration |
| `lake-manifest.json` | 117 | 3536 | Dependency versions |
| `lean-toolchain` | 1 | 25 | Lean version |

`instruction_decode` and `bounded_artifact_checks` use `native_decide`.
Consequently they depend on Lean's native evaluator/compiler/runtime, in
addition to its proof kernel and ordinary logical axioms. In this Lean version,
`#print axioms` displays generated `...native_decide.ax_1_1` axioms for those
computations; `each_case_certified` inherits the bounded check's dependency.
These are **not kernel-only computational proofs**. `strict_inputs_valid`
uses `decide`, which is checked by kernel reduction. The arithmetic and general
format lemmas use ordinary proof terms. The audit commands print each theorem's
actual dependencies. There are no `sorry` proofs or user-written axioms.

The surrounding toolchain remains trusted: installed Lean and Mathlib, their
compiled dependencies, Python and SHA-256 implementation, wasm-tools for Wasm
validation, Wasmtime for direct replay, and the operating system/hardware.
Their implementations have not been verified or included in the source-size
table. In particular, passing the reproduction script establishes only the
bounded and model-level statements recorded above.
