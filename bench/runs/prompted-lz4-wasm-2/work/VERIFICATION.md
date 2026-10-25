# Verification result

**R1, R2, and R3 all fail.** The counterexamples below execute the unchanged
shipped module in both Node/V8 and Wasmtime. Lean proofs establish the relevant
LZ4 format facts; those proofs also pass the independent Rust kernel Nanoda.
These are counterexample demonstrations, not universal correctness proofs.

Run, from this directory, with no network:

```sh
./check.sh
```

Success is exit status 0 and the final line:

```text
ALL CHECKS PASSED: R1, R2, R3 are refuted on the shipped artifact.
```

The command forcibly recompiles the project proofs, exports their dependency
closure, checks it through two kernels, checks rejection controls, and runs both
WebAssembly engines. It requires the installed Lean 4.35.0 Lake environment,
Python 3, Node, wasm-tools, and Wasmtime. It finds `leanexport`, `leanchecker`,
and `nanoda_bin` beside the resolved `lean` executable. Generated inputs,
exports, disassembly, individual checker logs, and sizes are in `.verification/`.
Any missing checker or failed assertion makes the command fail.

## R1: encoder emits an invalid block

Initialize all 65,536 hash words at address 0 to signed i32 value -65536.
Grow memory from one to six pages. Store these 13 input bytes at 262144:

```text
ASCII: abcdabcdEFGHI
hex:   61 62 63 64 61 62 63 64 45 46 47 48 49
```

Call `lz4BlockEncode(262144, 13, 327680)`. Both engines observe return value
13 and these bytes at 327680:

```text
40 61 62 63 64 04 00 50 45 46 47 48 49
```

Token `40` specifies four literals, `abcd`, and a four-byte match. Offset
`04 00` copies `abcd` again. Token `50` introduces the five final literals
`EFGHI`. Thus the match starts at decoded position 4 of a 13-byte input:
only 9 bytes remain. The format's third end condition requires at least 12.
The output is invalid even though ignoring that restriction would recover
the input. This disproves R1's validity conjunct.

`Verification.encoder_block_invalid` checks that the specification rejects
these exact output bytes; `Verification.late_match` checks the violated
inequality. Runtime assertions check the returned size and every emitted byte,
and confirm the original input remains unchanged.

## R2: a valid block returns the wrong content and length

In a fresh one-page instance, put this 10-byte block at address 4096:

```text
13 61 01 00 50 62 63 64 65 66
```

It means one literal `a`, a seven-byte overlapping match at offset 1, then
five final literals `bcdef`. Its decoded content is `aaaaaaaabcdef`
(eight `a` bytes followed by `bcdef`), length 13. The last match starts at
position 1, exactly 12 bytes before the end, and all end conditions hold.
`Verification.valid_block_content` proves this interpretation.

Call `lz4BlockDecode(4096, 10, 0)`. Both engines observe return value **1**,
with output bytes `61` followed by twelve untouched zero bytes. Input and
output buffers are disjoint and fully allocated; the README places no ordering
constraint on their addresses. As a positive control, the same block decoded
to address 8192 returns 13 and writes all the expected bytes in both engines.

The artifact disassembly shows why: its match-address check compares the match
address against the end of the compressed input, rather than the beginning of
the output. In this example the match address is 0 and the input end is 4106,
so it exits after copying the first literal.

R2 also fails on the valid empty block in the next counterexample.

## R3: the decoder reads outside a valid supplied block

The format explicitly represents empty content by a single `00` byte.
`Verification.empty_block_content` proves that interpretation.

In a fresh one-page instance, place that byte at address 65535 and call
`lz4BlockDecode(65535, 1, 0)`. Both engines trap with an out-of-bounds memory
access instead of returning 0. The entire supplied block is accessible and
the output has ample memory. Binary disassembly shows that, after reading
the zero token and advancing the cursor, the decoder skips its literal branch
and attempts `i32.load8_u` at **65536**, outside `[65535,65536)`. No output
write precedes that load. This refutes R3 even if R3 is restricted to valid
blocks, and also refutes R2's claim for the valid empty block.

An additional witness demonstrates completed reads outside the block without
a trap: put `00` at 4096, set byte 4098 to zero, and decode with
`lz4BlockDecode(4096, 1, 8192)`. With byte 4097 zero, the return is 0; with
byte 4097 one, the return is 4. Both engines reproduce this difference in
otherwise identical fresh memories. The supplied block `[4096,4097)` is
unchanged. Thus a byte outside it affects execution even without reaching
the memory boundary. This witness concerns compressed-input overreads, not
the ordinary output-history reads needed for matches.

## Exact formal statements and artifact connection

All the following declarations are in `Proofs/Format.lean`, within namespace
`Verification`; `Proofs.lean` imports that file:

```lean
theorem encoder_block_invalid : specDecode encoderBlock = none
theorem late_match : ¬ (4 + 12 ≤ encoderInput.length)
theorem valid_block_content : specDecode validBlock = some validContent
theorem valid_content_length : validContent.length = 13
theorem empty_block_content : specDecode emptyBlock = some []
theorem wrong_return : (1 : Nat) ≠ validContent.length
theorem outside_block : ¬ (65535 ≤ (65536 : Nat) ∧ 65536 < 65535 + 1)
```

The five concrete lists and every project-specific definition these statements
depend on are in that same file. `specDecode` is a specification of independent
LZ4 blocks: byte range checks, both length-extension fields, little-endian
nonzero offsets into already decoded content, forward overlapping match copies,
literal-only termination, and both final-match restrictions. Naturals avoid
machine-word length overflow. Sequence and extension fuel exceed the available
number of tokens/extension bytes. No whole-format equivalence theorem with
the English document is claimed: reviewing this small specification against
`lz4_Block_format.md` remains necessary. The concrete token interpretations
above can also be checked directly against that document.

`EmitCases.lean` emits the very lists used in these proofs as JSON. The runtime
harness reads those lists and checks actual execution, rather than implementing
a replacement encoder or decoder. The Wasmtime WAST suite embeds all 1,226
original binary bytes verbatim; its auxiliary modules only initialize memory
and read back bytes through the original exported memory. V8 instantiates the
original binary directly. Neither path executes a reconstruction of the WAT.

The check pins these SHA-256 hashes before proceeding:

| File | SHA-256 |
| --- | --- |
| `lz4-block-codec.wasm` | `4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf` |
| `lz4-block-codec.wat` | `737b63992149810690086420d4802d86db058359c998768a9737962c974250e3` |
| `lz4_Block_format.md` | `dce3c34a8738c44ed1dffb48c73e30297fca98ba7881408dc228865912c9a42e` |

The source and artifact were not modified. There is **no Lean theorem of
WebAssembly execution semantics** here: the connection between the format
proofs and the module is a reproducible execution demonstration, cross-checked
by two independent runtime implementations. Consequently, runtime correctness
and the small harness are part of the evidence's trust boundary. This is the
demonstration alternative requested for failing requirements.

## Independent checking and rejection controls

`leanexport` exports only the seven named theorems and their transitive
dependencies. `leanchecker --from-export` replays the declarations through
Lean's C++ kernel from an empty environment. `nanoda_bin` checks the same
export with its independently implemented Rust kernel. Replaying with
`leanchecker` alone would not be an independent kernel; Nanoda supplies that
independence. Neither checker is replaced by a second elaboration run.

The export audit and Nanoda configuration permit only `propext` as an axiom.
They exclude `sorryAx`, compiler-trust axioms, and arbitrary verification
assumptions. The proofs use kernel reduction/`decide`, not `native_decide`.
The complete proof export contains 684 declarations. Nanoda reports
`no typechecker errors`; this installed version also reports a nonfatal
`Unable to print axioms` pretty-printer error, unrelated to proof checking.

`Controls.lean` supplies valid proofs of `True` and `0 = 0`; both kernels must
accept their export first. The script then preserves the proof terms but
changes their statements to `False` and `0 = 1`, respectively. It moves each
changed theorem after its new type's dependencies, so the resulting export
is syntactically well formed. **Both kernels reject both false proofs.**
The script requires a Lean declaration-type-mismatch diagnostic and a Nanoda
type-checker diagnostic; mere parse errors or missing executables do not count
as rejection. A deliberately false Wasmtime assertion also must fail, after
the genuine runtime suite succeeds.

## Review and trust size

The local formal statements, specification, concrete witnesses, and proofs
occupy **70 lines / 2,923 bytes**, all of `Proofs/Format.lean`. This includes
every project-specific definition in their dependency closure. Only `Init`
is imported; Mathlib is available but unnecessary. Standard Lean natural-number,
list, option, logic, and termination machinery are additional dependencies:
the exported closure is 684 declarations, 21,965 NDJSON lines / 1,213,539 bytes.
The 70-line figure is not a claim about the size of the entire trusted base.

The complete local checking code, including controls and the one-line library
root, is **324 lines / 14,497 bytes**:

| File | Lines | Bytes | Review purpose |
| --- | ---: | ---: | --- |
| `Proofs/Format.lean` | 70 | 2923 | Format definitions, witnesses, statements and proofs |
| `Proofs.lean` | 1 | 21 | Library import |
| `EmitCases.lean` | 10 | 323 | Connect proved lists to runtime cases |
| `Controls.lean` | 8 | 183 | Valid seeds for false-proof controls |
| `runtime-check.mjs` | 100 | 4908 | Real-binary invocation, assertions, WAST generation |
| `verify.py` | 131 | 6074 | Hash checks, compilation, export audit, kernel replay, controls |
| `check.sh` | 4 | 65 | Single command; Python isolated mode keeps assertions enabled |

The unchanged Lake configuration, toolchain, and manifest add 130 lines /
3,825 bytes. Runtime/kernel/tool binaries, their parsers, Lean's standard
foundation, Python/Node, and the operating system are external trust
dependencies, not included in the local-source counts. The format document
and README are the requirements authority. The generated `.verification/sizes.txt`
reports source sizes on each run. Generated exports and WAST are reproducible
evidence, not additional handwritten semantic models.
