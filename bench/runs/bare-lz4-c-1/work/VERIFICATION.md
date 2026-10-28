# Verification results

**Partial verification. R1, R2, and R3 remain unproved in their full quantified form. No violation was demonstrated.** The results below are kernel-checked finite executions of an instruction model extracted from the shipped binary, plus independent executions of the unchanged binary. Passing these checks does not establish universal correctness.

## Artifact and connection to the proofs

The subject is `lz4-c.wasm`, exactly 8,469 bytes, SHA-256:

```
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`verification/extract.py --check` checks this size and digest, decodes the binary sections and instructions, and compares its generated Lean text with `Proofs/Artifact.lean`. It checks the exports, absence of imports and a start function, fixed 32-page memory, and the initialized 64-byte table at address 65536. It extracts functions 2 (`LZ4_decompress_safe`), 3 (`memcpy`), and 4 (`memmove`); all calls in those functions must target 3 or 4. The compressor is outside the requirements and is not modeled.

The extractor resolves block/loop labels to instruction addresses. It accepts only void blocks/loops and checks that branch operand stacks have the required empty height. `Proofs/Wasm.lean` supplies the executable instruction semantics, including 32-bit arithmetic, signed comparison, little-endian loads/stores, calls, returns, memory bounds, and an access trace. The instruction table is split into chunks to make reduction practical; this does not change instruction addresses.

**The binary-to-model correspondence is not itself proved in Lean.** Interpreting the model theorems as facts about Wasm requires trusting the extractor and checking the semantics against WebAssembly. No correctness of the C compiler, the C sources, or a rebuilt binary is assumed. `verification/runtime.py` additionally embeds the exact binary bytes in a Wast script and invokes the original export with Wasmtime; it does not replace or instrument the decoder.

## Exact checked statements and requirement coverage

All finite proof statements are in `Proofs/Cases.lean`, in namespace `Verification`. The aggregate theorem is exactly:

```lean
theorem all_cases_checked : ∀ c ∈ cases, check c = true
```

There is also one theorem for each row below, with the exact statement
`theorem NAME_checked : check NAME = true` (substitute the row's `NAME`). All are proved with `decide +kernel`, not `native_decide`. The inputs, capacities, and expected outputs are explicit definitions in the same file and are reproduced from `verification/cases.py` by its `--check` command.

| NAME | Input/behavior covered | Expected result |
| --- | --- | --- |
| `empty_zero` | `00`, capacity 0 | Empty output, return 0 |
| `empty_one` | `00`, capacity 1 | Empty output, return 0 |
| `one_literal` | `10 41`, capacity 1 | `41`, return 1 |
| `one_literal_spare` | `10 41`, capacity 64 | `41`, return 1 |
| `fourteen_literals` | `e0` followed by bytes 0 through 13, capacity 14 | Those 14 bytes |
| `fifteen_literals` | `f0 00` followed by bytes 0 through 14, capacity 15 | Those 15 bytes |
| `overlap_one` | `14 41 01 00 50 42 43 44 45 46`, capacity 14 | Nine `41` bytes, then `42` through `46` |
| `shortcut_eight` | `80`, bytes 0 through 7, `08 00 80`, bytes 20 through 27; capacity 64 | Bytes 0 through 7, bytes 0 through 3, bytes 20 through 27 |
| `zero_offset` | `04 00 00 50 01 02 03 04 05`, capacity 32 | Eight zero bytes, then bytes 1 through 5 |
| `empty_source` | No source bytes, capacity 1 | Negative return |
| `truncated_literal` | `10`, capacity 16 | Negative return |
| `missing_extension` | `f0`, capacity 32 | Negative return |
| `too_small` | `20 41 42`, capacity 1 | Negative return |
| `offset_before_start` | `00 01 00 50 01 02 03 04 05`, capacity 32 | Negative return |
| `zero_cap_nonzero` | `01`, capacity 0 | Negative return |
| `zero_cap_two_bytes` | `00 00`, capacity 0 | Negative return |

For every row, `src = 131072` and `dst = 196608`. Initially, all public memory bytes outside the source equal 165. Below 131072 memory is zero except for the actual initialized table. These are specific memory states and buffer placements, not universally quantified ones.

`Proofs/Checks.lean` defines `check`. A successful check establishes all of the following in the model: the README's buffer preconditions; termination with a return within 2,000 modeled instruction steps (not a fuel exhaustion or trap); and that every traced load/store satisfies `Wasm.accessOK`. For successful decodes it also checks the returned length against the capacity, every returned output byte, and the independent format parser. For rejection cases it checks that the returned i32 has its sign bit set.

`Proofs/Format.lean` is an independent specification based on the supplied `lz4_Block_format.md`. It parses tokens, terminating length extensions, literals, little-endian offsets, and overlapping matches. Positive offsets must refer to bytes already decoded. Its strict mode disallows offset zero and checks the final-literal and last-match end conditions. Its relaxed mode permits offset zero with zero-filled matches and omits the end conditions. Equivalence of this specification to the English format document is a review obligation, not a proved theorem.

**R1:** For all 16 rows, the entire modeled access trace passes the requirement's address restrictions, including executions returning errors. Accesses below 131072 are outside R1's stated address scope; among public addresses, reads must lie in either supplied buffer and writes in the destination buffer. The checker checks access widths, not just starting addresses. **Unproved in general:** no invariant covering all decoder loops, variable lengths, hostile inputs, initial memory states, and admissible placements has been established.

**R2:** The first eight rows have strict-format parsing and valid end conditions, fit their capacities, and return exactly the specified content and length. The zero-capacity row is exactly the allowed one-byte empty block. **Unproved in general:** there is no completeness proof connecting every valid independent format block to an accepting execution, including arbitrary length extensions, matches, and boundary placements.

**R3:** For the nine successful rows, the parser checks the specified decoded content, length, and offsets; `zero_offset` uses the relaxed interpretation and checks that its match yields zero bytes. The seven remaining rows are checked to return negative values. **Unproved in general:** there is no soundness invariant showing that every nonnegative return on every possible input corresponds to a complete permitted sequence decomposition and the correct content.

The Wasmtime checks exercise the same 16 inputs, capacities, and expected success/rejection behavior on the unchanged artifact. They compare all expected output bytes, check source preservation, and check the destination's immediately adjacent guard bytes. Those guard checks are not a proof of R1 and do not observe reads; the model's finite trace checks serve that purpose for the listed model executions.

## Reproduction

From this directory, with the supplied installed toolchain/packages and no network:

```sh
wasm-tools validate lz4-c.wasm
python3 verification/extract.py --check
python3 verification/cases.py --check
lake build
lake env lean verification/Audit.lean
python3 verification/runtime.py
```

Every command must exit zero. `wasm-tools validate` is silent on success. The Python consistency checks print `PASS`. Lake reports `Build completed successfully` (and may replay the 16 `PASS Lean` messages). The audit prints the exact aggregate theorem type and reports `depends on axioms: [propext]`; there is no `sorryAx` or native-evaluation axiom. The runtime script prints `PASS: 16 unchanged-artifact Wasmtime executions`; every Wast assertion must pass. It puts the Wasmtime cache in a temporary writable directory and removes temporary files afterwards.

The checked versions used here are Lean 4.35.0 with the project's Mathlib v4.35.0 dependency, wasm-tools 1.262.0, and Wasmtime 50.0.0. No rebuild of `lz4-c.wasm` is needed or performed.

## Review and trust

The kernel checks the finite proof terms by reduction. The `#eval` lines in the generated cases only print progress messages; they do not supply evidence to a theorem. The audit exposes theorem axioms. To interpret these results as the stated software behavior, review the definitions and bridge code listed below. Standard dependencies are Lean's kernel and the logical foundations of the imported Lean/Mathlib libraries; Python and its standard library are trusted for extraction, digest checking, and harness construction; Wasmtime is trusted for the independent runtime assertions.

The following sizes are source lines and bytes (`wc -lc`), not the size of compiled proof objects. The definitions and scripts are the reviewable trust boundary for the artifact and format correspondence. The case data and proof statements define the finite scope.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 154 | 5,587 | Instruction semantics, memory and access predicate |
| `Proofs/Format.lean` | 67 | 2,467 | Format specification |
| `Proofs/Checks.lean` | 46 | 1,570 | What each finite certificate checks |
| `verification/extract.py` | 208 | 7,468 | Binary identity and extraction bridge |
| `Proofs/Artifact.lean` | 124 | 11,845 | Generated instruction and static-memory data |
| `verification/cases.py` | 59 | 2,784 | Explicit finite corpus and declaration generator |
| `Proofs/Cases.lean` | 76 | 5,135 | Generated cases and kernel-checked theorems |
| `verification/runtime.py` | 53 | 2,518 | Independent Wasmtime assertion harness |
| `verification/Audit.lean` | 5 | 176 | Theorem type and axiom inspection |
| `Proofs.lean` | 1 | 20 | Library root importing all delivered proofs |
| `lakefile.toml` | 12 | 264 | Build and dependency configuration |
| `lean-toolchain` | 1 | 25 | Lean version pin |
| `lake-manifest.json` | 117 | 3,536 | Installed dependency revisions |
| `README.md` | 18 | 2,872 | Requirements |
| `lz4_Block_format.md` | 244 | 10,683 | Format document |

The generator consistency checks make manual transcription unnecessary, but do not replace reviewing the generators. The C source is not a premise of the model proofs. The external Lean/Mathlib installation, Python, wasm-tools, and Wasmtime are not vendored or included in these source-size counts; their trusted roles and versions are described above. Wasm validation is a tool result, not a Lean proof.

These results provide partial evidence. They neither prove all three requirements nor demonstrate that any of them is false.
