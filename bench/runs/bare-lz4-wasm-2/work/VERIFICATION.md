# Verification results

**R1, R2, and R3 all fail.** Each has a reproducible counterexample executed
against the shipped binary. Lean checks the format interpretation and arithmetic
of the witnesses. These are demonstrations of failure, not universal correctness
proofs or a formalization of WebAssembly semantics.

## Artifact and connection

The tested artifact is `lz4-block-codec.wasm`, exactly **1,226 bytes**, SHA-256:

```
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

`verification/check.py` rejects a different size or hash and validates the binary
with `wasm-tools`. For each test it embeds those exact bytes in a WAST
`(module $codec binary "...")` directive. The harness imports the module's actual
memory and functions. Wasmtime executes the original instructions; no translated
codec, recompilation of the supplied WAT, or instrumented replacement is used.
Each test starts with a separate instance. Temporary WAST files and the runtime
cache are placed in a temporary directory, then removed.

`Proofs/Counterexamples.lean` instead defines a specification interpreter:
`parseBlock` reads literal lengths, literal bytes, little-endian offsets, match
lengths, and overlapping match copies for independent blocks. It records decoded
match positions. `endConditions` checks the final literals restriction (including
the short/empty exception) and the distance of matches from the decoded end.
`ValidBlock bs` means `checkBlock bs = true`. Its correspondence to the prose
specification is a review obligation, not a proved equivalence with another
formal LZ4 standard. All witnesses are small independent blocks. No general
correctness/completeness theorem about this interpreter is claimed or needed for
these directly inspectable witnesses.

The Lean lists below are decimal byte values; the runtime harnesses assert the
same bytes. Wasmtime assertions supply the artifact behavior, while Lean
supplies the separate specification facts. There is no Lean theorem claiming to
execute or verify the Wasm binary.

## R1 — invalid encoder output

File: `verification/r1.wast`.

The harness grows memory from one page to five, initializes all 65,536 hash words
at addresses 0–262143 to **−65536**, and places this 13-byte input immediately
after the table, at address **262144**:

```
ASCII: ababababababc
hex:   61 62 61 62 61 62 61 62 61 62 61 62 63
```

It calls `lz4BlockEncode(262144, 13, 262208)`. The input, hash table, and output
buffers are disjoint and in bounds. The call returns **11**, and assertions check
every returned byte:

```
22 61 62 02 00 50 61 62 61 62 63
```

The first token has two literals (`ab`) and a six-byte match at offset two.
The last sequence contains five literals (`ababc`). Thus the decoded input has
13 bytes and its sole/last match starts at decoded position 2. Only **11** bytes
remain from that position to the end, violating the mandatory **12**-byte rule
in “End of block conditions”, item 3 of `lz4_Block_format.md`.

This disproves the validity conjunct of R1. Its round-trip conjunct need not
also fail: the specification interpreter reconstructs the original input.

Exact Lean theorem statements, in namespace `LZ4`, in
`Proofs/Counterexamples.lean`:

```lean
theorem r1_parse : parseBlock r1Block = some ⟨r1Input, [2], 5⟩
theorem r1_last_match_too_late : ¬ (2 + 12 ≤ r1Input.length)
theorem r1_not_valid : ¬ ValidBlock r1Block
```

Here the exact definitions are:

```lean
def r1Input : List Nat := [97, 98, 97, 98, 97, 98, 97, 98, 97, 98, 97, 98, 99]
def r1Block : List Nat := [34, 97, 98, 2, 0, 80, 97, 98, 97, 98, 99]
```

## R2 — valid block decoded incorrectly

File: `verification/r2.wast`.

At address **1024** the harness places this valid ten-byte block:

```
13 61 01 00 50 61 61 61 61 61
```

Its content is **13 copies of byte 97** (`aaaaaaaaaaaaa`): one literal `a`,
a seven-byte overlapping match at offset one, and five final literal `a` bytes.
The match starts at decoded position 1, exactly 12 bytes before the end.
All three end restrictions hold, and no dictionary is needed.

The harness initializes the 13-byte destination at address **0** to `cc` and
calls `lz4BlockDecode(1024, 10, 0)`. Both buffers are disjoint and fully in bounds;
the interface imposes no ordering restriction on their addresses. The function
returns **1**, writes byte 97 at address 0, and leaves byte 1 equal to **204**
(`cc`). The required return is 13 and the required second byte is 97.

The decoder compares its match source address against the **compressed input
end address**, rather than the output start. Here that comparison is
`0 < 1034`, causing it to stop after the first literal. This explanation is
visible in the shipped binary's decoder (`wasm-tools print`), and the observed
return and bytes are checked by runtime assertions.

Exact Lean theorem statements, in namespace `LZ4`, in
`Proofs/Counterexamples.lean`:

```lean
theorem r2_parse :
    parseBlock r2Block = some ⟨List.replicate 13 97, [1], 5⟩
theorem r2_valid : ValidBlock r2Block
theorem r2_wrong_length : (1 : Nat) ≠ (List.replicate 13 97).length
theorem r2_wrong_second_byte : (204 : Nat) ≠ (List.replicate 13 97)[1]!
```

The exact witness definition is:

```lean
def r2Block : List Nat := [19, 97, 1, 0, 80, 97, 97, 97, 97, 97]
```

## R3 — reads outside even a valid block

File: `verification/r3.wast`.

The supplied specification explicitly permits the one-byte block **`00`** for
empty decoded content. In a fresh one-page memory the harness uses that block
at **1024**, sets memory[4095] to **42**, and calls
`lz4BlockDecode(1024, 1, 4096)` twice:

1. With zero bytes after the block, the function returns **0**.
2. After changing only memory[1025] (immediately outside the block) to **1**,
   the function returns **4** and writes four copies of **42** at 4096–4099.

The first call writes no output. Thus the only memory change between calls is
the store at 1025. The changed behavior demonstrates an actual successful read
outside the specified block, not merely a possible out-of-bounds address in a
model. The decoder incorrectly treats the two bytes at 1025–1026 as an offset.
These addresses are mapped but outside the one supplied byte at 1024.

The same script also calls **`lz4BlockDecode(65535, 1, 1024)`**. The final byte of
the one-page memory is zero and constitutes the whole valid block. Wasmtime
checks that the call **traps with “out of bounds memory access”**. After reading
the token, its literal count is zero, so the decoder skips the branch containing
the end-of-block check and attempts to load an offset byte at **65536**. That
address is outside both the block and the 65,536-byte memory. No literal/match
copy or output store precedes this access on this path. This gives a second
boundary demonstration, independent of output-buffer capacity or malformed
input. It also supplies another failure of R2.

Exact Lean theorem statements, in namespace `LZ4`, in
`Proofs/Counterexamples.lean`:

```lean
theorem empty_parse : parseBlock emptyBlock = some ⟨[], [], 0⟩
theorem empty_valid : ValidBlock emptyBlock
theorem r3_boundary :
    65535 < 65536 ∧ 65535 + emptyBlock.length = 65536 ∧
    ¬ (65536 < 65535 + emptyBlock.length) ∧ ¬ (65536 < 65536)
```

The exact witness definition is `def emptyBlock : List Nat := [0]`.

## Reproduce every result

From this directory, with the already installed offline dependencies:

```sh
lake build
lake env lean verification/Audit.lean
python3 verification/check.py
```

All commands must exit with status **0**. `lake build` ends with
`Build completed successfully` (job counts/caching output may differ).
The audit prints the dependencies of all ten theorem proofs: either
`does not depend on any axioms` or `depends on axioms: [propext]`.
There are no `sorry` proofs, custom axioms, `native_decide`, or unproved
WebAssembly-correctness assumptions in these statements. `propext` is Lean's
standard propositional extensionality axiom.

The Python runner prints exactly these success lines (Wasmtime may also print
its own diagnostics):

```
PASS R1: all counterexample assertions checked
PASS R2: all counterexample assertions checked
PASS R3: all counterexample assertions checked
PASS artifact: 1226 bytes, sha256 4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

“PASS” means that the **failure evidence** was reproduced, not that the
requirements hold. Hash mismatch, validation error, wrong return/byte, missing
expected trap, or failed Lean proof makes the relevant command fail.

For optional inspection of the original instructions (not required to execute
the checks):

```sh
wasm-tools print lz4-block-codec.wasm
```

## Review and trust boundary

Local files relevant to interpreting/reproducing the claims:

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `lz4_Block_format.md` | 244 | 10,683 | Authoritative prose format and end restrictions |
| `README.md` | 18 | 1,798 | Requirements, interface preconditions, artifact identity |
| `Proofs/Counterexamples.lean` | 117 | 4,892 | Specification definitions, witnesses, all ten theorem proofs |
| `Proofs.lean` | 1 | 30 | Imports proofs into the default build |
| `verification/Audit.lean` | 12 | 347 | Reports theorem axiom dependencies |
| `verification/check.py` | 25 | 1,329 | Hash binding, exact-byte embedding, execution and failure propagation |
| `verification/r1.wast` | 30 | 1,745 | Encoder setup and all returned-byte assertions |
| `verification/r2.wast` | 13 | 691 | Valid-block input, incorrect return/output assertions |
| `verification/r3.wast` | 23 | 1,254 | Successful overread and boundary-trap assertions |
| `lakefile.toml` | 12 | 264 | Build/dependency configuration |
| `lake-manifest.json` | 117 | 3,536 | Existing pinned dependency manifest |
| `lean-toolchain` | 1 | 25 | Pins Lean 4.35.0 |
| `lz4-block-codec.wasm` | binary | 1,226 | Subject of the runtime demonstrations |

The supplied `lz4-block-codec.wat` is not used as a substitute for the artifact.
No source-to-binary equivalence assumption is needed.

A reviewer must trust the interpretation of the prose embodied in the small
specification interpreter, the harness setup/assertions, and the runner's link
to the hash-pinned artifact. Lean 4.35.0's kernel and standard `propext` check
the proofs; the installed Mathlib v4.35.0/List dependencies and Lake provide the
build environment. Runtime evidence additionally trusts Python 3 (including
hashlib and subprocess), Wasmtime **50.0.0** (build `ebe5e8df1`), wasm-tools
**1.262.0** (build `e22db44da`), and the host system. These external toolchains
are not themselves verified here; the sizes above describe the complete local
proof/model/harness review surface, not the external tools' source trees.

There is no universal safety or correctness result for other inputs. Since each
universal README requirement already has a concrete violating input, no such
proof could establish these requirements for this unchanged artifact.
