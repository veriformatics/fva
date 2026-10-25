**R1, R2, and R3 all fail for the shipped artifact.** The evidence consists of concrete executions of the original binary in two independent WebAssembly engines, together with kernel-checked proofs of the format facts needed by those counterexamples. These are refutations by witnesses, not universal correctness proofs.

From this directory, run:

```sh
python3 verification/check.py
```

Success means exit status 0 and the final line:

```text
PASS: R1, R2, R3 REFUTED on the pinned shipped artifact; three proof kernels and two runtime engines checked, including negative controls.
```

The command requires the installed Lean 4.35 toolchain (including `leanexport`, `nanoda_bin`, and `con-ron` alongside `lean`), Lake, Python 3, Node, `wasm-tools`, and Wasmtime. It uses the existing local Lake dependencies, needs no network, and rebuilds the project proofs from source on every run. Generated proof streams, disassembly, and the trap transcript go in `.lake/verification/`.

**R1: invalid encoder output.** In a fresh instance, grow memory from one to eight pages. Initialize all 65,536 little-endian words at addresses 0–262143 to −65536, as required by the README. Put the thirteen input bytes `abcdefabcdxyz` at address 262144. Call:

```text
lz4BlockEncode(262144, 13, 300000)
```

It returns 13 and writes exactly:

```text
60 61 62 63 64 65 66 06 00 30 78 79 7a
```

This has six initial literals (`abcdef`), offset 6, a four-byte match, then a final sequence with only three literals (`xyz`). It violates end-of-block condition 2: with a match present, the last sequence must contain at least five literals. It also violates condition 3: its match starts at decoded position 6, only seven bytes before the end. The buffers and hash table are disjoint, and all accesses have allocated memory. Failure of the validity conjunct alone refutes R1; no claim about every encoder input is needed.

Both runtime harnesses assert the return value and every output byte. In [Proofs/Format.lean](Proofs/Format.lean), the exact formal statement is:

```lean
LZ4.r1_invalid : ¬ LZ4.valid LZ4.encoderBlock
```

`encoderBlock` is the thirteen bytes above. The human-readable format interpretation is [lz4_Block_format.md](lz4_Block_format.md), especially “End of block conditions.”

**R2: a valid block decoded incorrectly.** In a fresh one-page instance, place this ten-byte block at address 1024:

```text
13 61 01 00 50 61 61 61 61 61
```

Its first sequence has one literal `a`, offset 1, and a seven-byte overlapping match. Its last sequence has five literal `a` bytes. The decoded content is thirteen `a` bytes, and the match starts exactly twelve bytes before the end, so all end conditions hold. Fill output addresses 0–12 with `cc`, then call:

```text
lz4BlockDecode(1024, 10, 0)
```

It returns **1**, writes `61` at address 0, and leaves addresses 1–12 unchanged. The block and output buffers are disjoint and fully allocated. The interface permits this placement. In the binary, the decoder compares the match source address with the compressed input's end address; the legitimate match source 0 is less than 1034, so decoding stops early.

Both harnesses assert the return value, first output byte, and twelve untouched bytes. The exact formal statements in [Proofs/Format.lean](Proofs/Format.lean) are:

```lean
LZ4.r2_content :
  LZ4.decode LZ4.goodBlock = some (List.replicate 13 97)
LZ4.r2_valid : LZ4.valid LZ4.goodBlock
LZ4.r2_wrong_length : (1 : Nat) ≠ (List.replicate 13 97).length
```

`goodBlock` is the ten-byte block above. Thus this refutation concerns a valid, small block, with sufficient output capacity.

**R3: reading past a valid empty block.** In a fresh one-page instance (65,536 bytes), put byte `00` at address 65535 and call:

```text
lz4BlockDecode(65535, 1, 0)
```

The format explicitly permits `00` as the encoding of empty content. The entire input block lies inside memory. Both engines trap on an out-of-bounds access. Wasmtime identifies the offending instruction at binary file offset `0x32c` and the attempted address as `0x10000` in memory of size `0x10000`. `wasm-tools dump` identifies that exact instruction as `i32.load8_u`, with bytes `2d 00 00`. After consuming the zero token, the decoder tries to load a match offset at address 65536. This is a read outside the supplied interval [65535, 65536), rather than an unallocated input byte or output overflow.

The command checks both the trap location/address and the disassembly. It saves the transcript in `.lake/verification/r3-trap.txt`. The exact formal statements in [Proofs/Format.lean](Proofs/Format.lean) are:

```lean
LZ4.r3_empty_valid : LZ4.decode [0] = some [] ∧ LZ4.valid [0]
LZ4.r3_outside :
  ¬ (65535 ≤ (65536 : Nat) ∧ 65536 < 65535 + 1)
```

**Connection to the artifact and scope of the proofs.** The check command first verifies that `lz4-block-codec.wasm` is exactly 1,226 bytes with SHA-256:

```text
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

It also pins the original README and format document by size and hash. Node instantiates these binary bytes directly. Wasmtime preloads the same file as module `codec`; the WAT harness imports its exported functions and its actual memory. The harness does not contain a replacement codec. The shipped `.wasm` and `.wat` are unchanged; the source is neither recompiled nor used as a substitute for the binary.

`LZ4.decode` is a format specification, not a model of the implementation. It reads token nibbles, mandatory length extensions, literals and little-endian offsets; copies matches byte by byte to allow overlap; and checks the final-literal and last-match restrictions. `LZ4.valid bs` means this specification returns content. Its sequence fuel is the compressed byte count, enough for the number of tokens. The specification uses unbounded natural numbers and rejects values outside the byte range.

The Lean theorems establish the displayed specification facts. Actual binary behavior is established by the two runtime demonstrations. There is no claim here that a WebAssembly execution trace has been derived inside Lean, or that the specification has itself been proved equivalent to the English document. Those interpretation and execution links are explicit review/trust boundaries. Since every universal requirement has a counterexample, neither a general implementation model nor a full correctness proof is necessary to settle these requirements.

**Independent replay and rejection controls.** The command compiles the proofs with Lean's kernel, then exports the seven theorem roots below, with their complete transitive dependencies. Nanoda (a separate Rust Lean type checker) and con-ron (a separate Rust kernel, run in its `--verified` mode) independently check the exported declarations. The only axiom in the exported closure is `propext`, which is explicitly allowlisted; `sorryAx`, `Lean.trustCompiler`, and arbitrary added axioms are not permitted. Proofs use `decide` with kernel reduction, not `native_decide` or an oracle.

The seventh root is the control theorem in [Proofs/Format.lean](Proofs/Format.lean):

```lean
LZ4.kernelCanary : (0 : Nat) = 0
```

The checker demonstrably rejects false proofs in all three kernels:

- [verification/KernelNegative.lean](verification/KernelNegative.lean) submits `Eq.refl 0` as a proof of `0 = 1` directly through `Lean.addDecl`, bypassing tactic/elaborator proof checking. Success of the overall command requires Lean's specific **kernel declaration type mismatch** diagnostic.
- For the two external kernels, the script changes only the exported canary's conclusion from `0 = 0` to `0 = 1`, preserving its proof body and the rest of the stream. Nanoda must fail its type-equality check; con-ron must report a theorem type mismatch at `LZ4.kernelCanary`. A missing executable or a parsing failure does not pass these controls.
- Each runtime harness also contains a deliberately false assertion. The command requires both engines to reject theirs, in addition to reproducing all three witnesses. Failure expectations are checked against specific diagnostics, not just arbitrary nonzero exits.

**Review surface and trust.** Read the formal definitions and theorem statements in [Proofs/Format.lean](Proofs/Format.lean) against the original format text, then check that the runtime harnesses set up the described buffers and compare the same byte vectors. The complete custom verification code, including proof bodies, comments, and blank lines, is:

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs/Format.lean` | 73 | 2,796 | Format definitions, witness constants, six result theorems and canary |
| `Proofs.lean` | 1 | 21 | Library import |
| `verification/check.py` | 146 | 7,147 | Artifact pins, execution, rebuilding, export/replay, rejection controls |
| `verification/runtime.mjs` | 41 | 1,776 | Node witness executions and byte assertions |
| `verification/harness.wat` | 52 | 2,182 | Wasmtime witness executions and byte assertions |
| `verification/KernelNegative.lean` | 15 | 493 | Direct kernel false-proof control |
| **Total** | **328** | **14,415** | Entire maintained verification code |

The entire domain-specific formal file is **73 lines / 2,796 bytes**; no additional project-specific definitions are hidden in an implementation model. Definitions also depend on the standard Lean `Init` semantics for naturals, booleans, lists, options, indexing, decidability, and their instances. Mathlib is available in the project but is not imported by these proofs. To avoid treating standard-library dependencies as invisible, the complete exported closure is also measured: **585 declaration records, 24,014 JSON lines, 1,320,045 bytes** (364 definitions, 157 theorems, 62 inductive records, one opaque declaration, and one axiom). Nanoda reports 715 declarations because its count includes the constants introduced by inductive records. All of this closure is replayed, not assumed as user axioms.

Beyond these files and the original requirements/format documents, trust remains in the installed checker/runtime binaries, their parsers and build toolchains, Lean's exporter, standard-library definitions, Python's process/file/hash operations, the operating system, and WebAssembly semantics. The independent kernels and runtime engines reduce reliance on any single implementation; the negative controls exercise the actual paths used for this verification. The command prints current code sizes and export census so the recorded measurements are reviewable. This report and `.gitignore` are excluded from the code-size total.
