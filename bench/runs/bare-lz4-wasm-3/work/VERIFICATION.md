# Verification results

**R1, R2, and R3 are false for the shipped artifact.** The results below are
concrete counterexamples, combining Lean-checked format facts with Wasmtime
assertions about execution of the original binary. They are not a universal
correctness proof or a Lean formalization of WebAssembly execution.

## Artifact and specification

The artifact tested is `lz4-block-codec.wasm`, exactly 1,226 bytes, SHA-256:

```
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

The specification is the supplied `lz4_Block_format.md`, SHA-256:

```
dce3c34a8738c44ed1dffb48c73e30297fca98ba7881408dc228865912c9a42e
```

`verification/check.py` checks both hashes and the artifact length, validates
the binary with `wasm-tools`, embeds its exact bytes in WAST `module binary`
directives, and runs four independent cases with `wasmtime wast`. Each case
instantiates the original module and a small test module importing its memory
and functions. The test modules initialize memory, invoke the exports, and
assert returns, memory contents, or traps. The shipped `.wat` is not compiled,
modified, or substituted for the binary. The original software is unchanged.

## R1: encoder produces a valid block and preserves the input — fails

Initialize memory and call as follows (all addresses and lengths are decimal):

- Grow memory from one to five pages (327,680 bytes).
- Initialize all 65,536 little-endian 32-bit table entries at address 0 to
  −65536, as the README requires. `getLinearMemoryOffset()` returns 0.
- Put the 13-byte input `abbbbbbbbbbbb` at address 262144. This is one `a`
  followed by twelve `b` bytes.
- Call `lz4BlockEncode(262144, 13, 262160)`.

The artifact returns **11**, and the exact eleven output bytes are:

```
22 61 62 01 00 50 62 62 62 62 62
```

The replay asserts every output byte and checks that the input is unchanged.
The table, input, and output are disjoint and have sufficient memory.

This block contains literals `ab`, an offset-1 match of length 6, then five
literal `b` bytes. Its decoded length is 13 and its last match starts at decoded
position 2 (zero-based). Therefore only **11** decoded bytes remain from the
match start to the end. End-of-block condition 3 in the supplied specification
requires at least **12**. The block does expand to the input, but violates the
required format restriction, refuting R1's validity conjunct.

The exact Lean statements, in namespace `LZ4` in
`Proofs/Counterexamples.lean`, are:

```lean
theorem encoder_block_expands :
    expand encoderBlock = some ⟨encoderInput, some 2, 5⟩
theorem encoder_block_violates_end_condition :
    ¬ (2 + 12 ≤ encoderInput.length)
theorem encoder_block_invalid : validDecode encoderBlock = none
```

Here `encoderInput` is the decimal byte list for the input above, and
`encoderBlock` is the decimal byte list for the eleven observed output bytes.
The three fields of `Expanded` are content, last-match start, and final literal
count. `validDecode` rejects a block whose end conditions fail. The artifact
execution result is the WAST assertion group named
`r1-invalid-encoded-block` in `verification/check.py`.

## R2: every valid block decodes to its exact content and length — fails

The supplied specification explicitly permits the one-byte block `00` for
empty content. Lean checks its meaning with:

```lean
theorem empty_block_valid : validDecode [0] = some []
```

Put `00` at address 1024, set the next two bytes at 1025 and 1026 to `01 00`,
and set byte 2047 to `aa`. Initialize output bytes 2048–2051 to `cc`.
Call `lz4BlockDecode(1024, 1, 2048)` with one page of memory.

The artifact returns **4** and writes `aa aa aa aa` to output. A correct
decoder must return **0** and write no bytes for this valid block. This is
asserted in `r2-r3-empty-block-suffix-dependence`. Both the block and output
are within memory and disjoint; the incorrect behavior is not caused by
insufficient output capacity.

There is also a nonempty counterexample, avoiding any reliance on the special
empty case. Put these ten bytes at address 1024:

```
13 61 01 00 50 62 63 64 65 66
```

Call `lz4BlockDecode(1024, 10, 0)` in fresh one-page memory. The block contains
one literal `a`, an offset-1 match of length 7, then literals `bcdef`. The
correct content is `aaaaaaaabcdef` (eight `a` bytes followed by `bcdef`),
length **13**. The last match starts at position 1, exactly 12 bytes before
the end, and the final five bytes are literals, so all end restrictions hold.

The artifact instead returns **1**, writes only the first `a`, and leaves
output bytes 1–12 zero. This is asserted by
`r2-nonempty-block-output-before-input`. The input and output are disjoint and
fully allocated. The README imposes no ordering restriction on decoder input
and output addresses. The binary compares its match pointer against the
compressed input's end address, causing premature exit for this layout.

The additional exact Lean statements are:

```lean
theorem nonempty_block_valid :
    validDecode nonemptyBlock = some nonemptyContent
theorem nonempty_decoded_length : nonemptyContent.length = 13
```

`nonemptyBlock` and `nonemptyContent` are the explicit decimal byte lists in
`Proofs/Counterexamples.lean`. These statements and `empty_block_valid` are in
that file under namespace `LZ4`.

## R3: decoder reads no byte outside the supplied block — fails

The same valid one-byte `00` block demonstrates actual dependence on memory
outside the block. In `r2-r3-empty-block-suffix-dependence`:

1. Put `00 00 00` at addresses 1024–1026, byte `aa` at 2047, and four `cc`
   bytes at output 2048. `lz4BlockDecode(1024, 1, 2048)` returns **0** and
   leaves those output bytes unchanged.
2. Change **only byte 1025**, from `00` to `01`. Repeat the identical call.
   It returns **4** and writes four `aa` bytes. The block byte at 1024 remains
   `00`, which the replay also asserts.

The compressed input interval in both calls is exactly `[1024,1025)`.
The changed byte is outside it. The decoder consumes bytes 1025 and 1026 as
a nonexistent offset after reading the final token. This is an out-of-block
compressed-input read, independently of the ordinary output-history reads
needed for legitimate LZ4 matches.

An additional boundary witness, `r2-r3-empty-block-boundary-trap`, puts `00`
at address **65535** in fresh one-page memory and calls
`lz4BlockDecode(65535, 1, 2048)`. The valid input is entirely allocated;
empty output needs no space. Wasmtime asserts an **out-of-bounds memory
access trap**, caused by the offset load at address 65536 after the token.
This also independently refutes R2's promise to return the decoded length.
The binary's end-of-input exit after literals is skipped when the token's
literal length is zero.

## Reproduction

From this directory, with the installed offline Lean/Mathlib and tools:

```sh
lake build
lake env lean verification/Audit.lean
python3 verification/check.py
```

Run all three commands and require exit status 0 for each. `lake build` must
report `Build completed successfully`. The audit must print:

```
'LZ4.encoder_block_expands' depends on axioms: [propext]
'LZ4.encoder_block_violates_end_condition' does not depend on any axioms
'LZ4.encoder_block_invalid' depends on axioms: [propext]
'LZ4.empty_block_valid' depends on axioms: [propext]
'LZ4.nonempty_block_valid' depends on axioms: [propext]
'LZ4.nonempty_decoded_length' does not depend on any axioms
```

The replay must print:

```
PASS r1-invalid-encoded-block
PASS r2-r3-empty-block-suffix-dependence
PASS r2-nonempty-block-output-before-input
PASS r2-r3-empty-block-boundary-trap
PASS exact artifact: 4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

Here PASS means the asserted **failure behavior** was reproduced. An expected
trap is a passing assertion; an unexpected trap or return value fails the
script. The script disables Wasmtime's compilation cache so the commands also
work with the sandbox's read-only home directory. It needs no network and
uses Python's standard library only. Checked with Lean 4.35.0, Mathlib
v4.35.0, Wasmtime 50.0.0, wasm-tools 1.262.0, and Python 3.14.8.

## Review and trust boundary

The custom files relevant to the checks are:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Counterexamples.lean` | 98 | 3896 | Format definitions, concrete byte lists, and six proofs |
| `Proofs.lean` | 2 | 79 | Imports the proof file into the default Lake target |
| `verification/Audit.lean` | 8 | 283 | Prints the six proofs' axiom dependencies |
| `verification/check.py` | 125 | 5174 | Hash checks, exact binary embedding, initial states, runtime assertions |
| `lz4_Block_format.md` | 244 | 10683 | Prose specification the format model interprets |
| `README.md` | 18 | 1798 | Requirements and caller conventions |
| `lz4-block-codec.wasm` | — | 1226 | Original tested software |

The build configuration is `lakefile.toml` (12 lines, 264 bytes),
`lean-toolchain` (1 line, 25 bytes), and `lake-manifest.json` (117 lines,
3536 bytes). All file sizes are source byte counts, excluding generated
Lake build output and temporary WAST scripts. The latter are constructed
transparently by the 125-line replay script and deleted after execution.

Review the format model against the supplied document: token nibbles,
extension lengths, little-endian nonzero offsets into existing output,
forward overlapping match copies, literal-only final sequences, and the
five-literal/twelve-byte end restrictions. Lengths use mathematical naturals.
The parser bounds sequence count by compressed length; every sequence consumes
a token. These definitions are a human interpretation of the prose, not a
machine-checked equivalence to the prose. The concrete witnesses can also be
checked directly using the explanations above. In particular, no extension
length fields occur in these witnesses.

The proofs use kernel-checked `by rfl` and `by decide`; there are no `sorry`,
project-defined axioms, or `native_decide` proofs. Four theorems depend on
Lean's standard propositional extensionality axiom `propext`; the other two
have no axiom dependencies, as shown above. Trust that standard axiom, Lean's
kernel, and the normal offline Lean/Lake/Mathlib installation. The axiom audit
is included to expose that boundary.

For runtime results, trust Python and its standard library, the SHA-256
identity check, wasm-tools validation, and Wasmtime's binary parser, execution
engine, and WAST assertion implementation, together with the host system.
These installed tools are not reverified or vendored here. Review the script's
constants against the Lean byte lists and the report's memory states. There is
no Lean theorem connecting Wasmtime execution to a formal Wasm semantics;
the artifact connection is direct execution of the exact binary. No universal
encoder/decoder correctness or safety theorem is claimed. Each universal
requirement is refuted by an explicit finite, machine-checked demonstration.
