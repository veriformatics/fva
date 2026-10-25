All three requirements fail on the shipped artifact. The evidence combines
kernel-checked Lean judgments about concrete LZ4 blocks with asserted executions
of the actual WebAssembly binary. No network access is needed.

**R1 fails: the encoder returns an invalid block.**

Initialize memory to eight pages. Fill all 65,536 hash words starting at address
0 with signed i32 value -65536, as required by the README. Put these 13 input
bytes at address 262144:

```text
41 42 43 44 45 46 47 48 41 42 43 44 45
```

`lz4BlockEncode(262144, 13, 327680)` returns 13 and writes exactly:

```text
80 41 42 43 44 45 46 47 48 08 00 10 45
```

The first token describes eight literals and a four-byte match at offset 8.
The final token describes just one literal. The decoded length would be 13,
and the last match starts at decoded position 8. This violates both end rule 2
(at least five final literals) and end rule 3 (last match starts at least twelve
bytes before the decoded end). The input, table, and output are disjoint, all
addresses are in allocated memory, and output has room for the encode bound.

The exact supporting theorem statements in
[Proofs/Counterexamples.lean](Proofs/Counterexamples.lean), inside namespace `LZ4`,
are:

```lean
theorem encoder_block_rejected : decodeSpec encoderBlock = none
theorem encoder_block_invalid : ¬ ValidBlock encoderBlock
theorem encoder_end_rules_fail : ¬ (5 ≤ (1 : Nat)) ∧ ¬ (8 + 12 ≤ (13 : Nat))
```

`encoderInput` and `encoderBlock` in that file are exactly the two byte lists
above, expressed in decimal. Invalidity of a returned block suffices to falsify
R1's conjunction.

**R2 fails: a valid block decodes incorrectly with output before input.**

In a fresh one-page memory, put this ten-byte block at address 1024:

```text
13 41 01 00 50 42 43 44 45 46
```

The first sequence is one literal `41`, followed by a seven-byte match at offset
1. The last sequence has five literals. Its correct decoded content is:

```text
41 41 41 41 41 41 41 41 42 43 44 45 46
```

The last match starts at decoded position 1, exactly twelve bytes before the
end. The block satisfies all end conditions and its offset references existing
output, including the permitted overlapping match.

Fill output addresses 0 through 12 with `cc`, then call
`lz4BlockDecode(1024, 10, 0)`. It returns **1**, writes only the first `41`, and
leaves the next twelve bytes `cc`. These buffers are disjoint and entirely
allocated. The interface imposes no requirement that decoder output follow
input. As a control, the same block at 1024 decoded to 2048 returns the expected
13 bytes in a fresh instance.

In the binary disassembly, function 3 computes the match pointer and exits when
it is less than the **compressed input end**. Here the match pointer is 0 and
the input end is 1034. This check incorrectly rejects a valid reference into
the output buffer.

The exact supporting statements in `Proofs/Counterexamples.lean`, namespace
`LZ4`, are:

```lean
theorem decoder_block_content : decodeSpec decoderBlock = some decoderContent
theorem decoder_block_valid : ValidBlock decoderBlock
theorem decoder_content_length : decoderContent.length = 13
```

`decoderBlock` and `decoderContent` are exactly the lists above.

**R3 fails: decoding the valid empty block reads beyond its input.**

In a fresh instance, memory has exactly 65,536 bytes. Set byte 65535 to `00` and
call `lz4BlockDecode(65535, 1, 0)`. The one-byte block is entirely in memory;
its decoded content is empty, so output requires no writes. Execution traps
with `WebAssembly.RuntimeError: memory access out of bounds`.

The format explicitly permits `00` as the encoding of empty content. The exact
supporting statements in `Proofs/Counterexamples.lean`, namespace `LZ4`, are:

```lean
theorem empty_block_content : decodeSpec emptyBlock = some []
theorem empty_block_valid : ValidBlock emptyBlock
```

`emptyBlock = [0]`. In the binary's function 3, the token read advances the input
pointer to 65536. A zero literal length skips the final-sequence termination
check, which is inside the nonzero-literal branch. The next instruction that
accesses memory is `i32.load8_u` at that pointer while reading a supposed match
offset. Address 65536 is outside both the supplied block and memory. No store
occurs on this execution path before the trapping load. This also independently
falsifies R2 for a valid block.

**Connection to the artifact.**

[verify.mjs](verify.mjs) reads `lz4-block-codec.wasm` directly, asserts its length
is 1,226 bytes, and asserts its SHA-256 is:

```text
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

It instantiates those exact bytes using Node's WebAssembly engine. Each test
uses a fresh instance. It checks the returned values, output bytes, unchanged
output sentinel bytes for R2, and the memory access trap for R3. The script
obtains its byte lists from [ExportWitnesses.lean](ExportWitnesses.lean), which
imports the proved definitions and exports them as JSON. The checked witnesses
and execution inputs therefore share their definitions. The `.wat` source is
not used as an execution substitute; no source/binary equivalence is assumed.

Lean's `decodeSpec` models the format using natural-number lengths, extension
bytes, literal and offset bounds, sequential overlapping copies, and all three
end conditions. `ValidBlock bytes` means
`∃ content, decodeSpec bytes = some content`. Its recursion fuel bounds sequence
count by input length; it does not limit match lengths. These are specification
definitions, not a model of this decoder's implementation.

The Lean theorems establish the listed judgments about this specification.
Execution assertions establish the reported behavior of the pinned binary.
There is no kernel-checked WebAssembly operational semantics or proof relating
V8 execution to such a semantics. The specification's correspondence to the
English format document requires review; the concrete sequence interpretations
above also permit checking each format judgment directly. No universal
correctness claim is made for either the binary or the specification parser.

**Reproduction commands, from this directory.**

```sh
wasm-tools validate lz4-block-codec.wasm
lake build
lake env lean Proofs/Counterexamples.lean
node verify.mjs
```

All four commands must exit with status 0. `wasm-tools validate` is silent on
success. `lake build` reports a successful build. Direct Lean checking prints
axiom reports for `encoder_block_invalid`, `decoder_block_content`, and
`empty_block_content`, each depending only on the standard axiom `propext`.
Proofs use `decide` and ordinary proof terms, with no `sorry`, added axioms, or
`native_decide`.

The Node command prints the artifact hash, three `FAIL confirmed` messages
(meaning the corresponding requirement has been falsified), the successful R2
control, and finally:

```text
PASS: all three counterexamples reproduced against the pinned shipped artifact.
```

To inspect the actual binary instructions cited above, optionally run:

```sh
wasm-tools print lz4-block-codec.wasm
```

These commands were run successfully with Lean 4.35.0, the installed Mathlib
v4.35.0, Node v26.11.1 (V8 14.6.202.34-node.37), and wasm-tools 1.262.0.

**Review and trust surface.**

Sizes are lines / bytes for the delivered files:

| File | Size | What to review |
| --- | ---: | --- |
| `Proofs/Counterexamples.lean` | 100 / 4,161 | Format definitions (lines 1–72), witness definitions, and eight proofs. |
| `ExportWitnesses.lean` | 12 / 525 | Exports exactly the theorem witness definitions as JSON. |
| `verify.mjs` | 73 / 3,467 | Binary hash pin, memory initialization, calls, assertions, and trap classification. |
| `Proofs.lean` | 2 / 79 | Imports the proof module into the Lake build target. |
| `lz4_Block_format.md` | 244 / 10,683 | Authoritative format interpretation, especially end conditions and overlapping matches. |
| `README.md` | 18 / 1,798 | Interface assumptions and requirements being falsified. |
| `lakefile.toml` | 12 / 264 | Build configuration and Mathlib dependency. |
| `lean-toolchain` | 1 / 25 | Lean version pin. |
| `lz4-block-codec.wasm` | 1,226 bytes | Exact tested artifact; inspect its decoder disassembly for the read-trap explanation. |

Additionally trust Lean's kernel and standard logical foundations, the local
Lean/Lake/compiler and imported library infrastructure, Node/V8's WebAssembly
execution and JavaScript assertions, JSON export/runtime plumbing, SHA-256
implementation, wasm-tools validation/disassembly, and the operating environment.
The binary was not modified. Successful reproduction demonstrates failures of
R1, R2, and R3; it does not certify behavior on other inputs.
