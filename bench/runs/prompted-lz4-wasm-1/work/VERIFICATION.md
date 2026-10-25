All three requirements are false for the shipped artifact. `./check` reproduces
counterexamples in **both Wasmtime and V8**, replays supporting Lean proofs in
**Lean's kernel and the independent Rust Con-Ron kernel**, and checks that both
kernels reject deliberately false proofs. No codec source or binary was changed.

Run from this directory, without network access:

```sh
./check
```

Success means exit status 0 and the final line:

```text
PASS: R1, R2, R3 REFUTED; independent replays and negative controls passed
```

A successful check confirms the failures, not compliance with the requirements.
The command requires Python 3, Node, Lake/Lean 4.35, wasm-tools, Wasmtime, and the
installed `leanexport`, `leanchecker`, and `con-ron` beside the Lean executable.
This run used Wasmtime 50.0.0, Node v26.11.1, and wasm-tools 1.262.0.
Logs, exported proofs, false proofs, and the generated WAST are in `.verification/`.

1. **R1 — refuted: the encoder emits an invalid block.**

   Grow the initially one-page memory by five pages. Fill the 65,536 little-endian
   four-byte words starting at 0 with −65536, exactly as README requires. Put the
   13 ASCII bytes `abcdeabcdWXYZ` at 262144 and call:

   ```text
   lz4BlockEncode(262144, 13, 300000) = 13
   output = 50 61 62 63 64 65 05 00 40 57 58 59 5a   (hex)
   ```

   The input, output, and hash table are disjoint and fully allocated. The input
   remains unchanged. The output parses as five literals `abcde`, offset 5,
   a four-byte match `abcd`, and four final literals `WXYZ`.
   Its decoded content is the original 13 bytes, but it violates BOTH mandatory
   end conditions: it has only four final literals, and the last match starts
   only eight decoded bytes before the end, rather than at least twelve.
   Invalid format alone refutes the conjunction in R1.

2. **R2 — refuted: a valid block returns the wrong decoded length.**

   In the original one-page memory, put this ten-byte block at 1024:

   ```text
   13 41 01 00 50 31 32 33 34 35   (hex)
   ```

   It means one literal `A`, offset 1, a seven-byte overlapping match, and five
   final literals `12345`. Thus its content is `AAAAAAAA12345`, length 13.
   Offset 1 refers to previously produced content, the final five bytes are
   literals, and the last match begins exactly twelve bytes before decoded end.

   ```text
   lz4BlockDecode(1024, 10, 0) = 1       (required: 13)
   ```

   The first output byte is `A`. The buffers are disjoint and memory is
   sufficient. As a control, decoding the identical block to 2048
   returns 13 and writes all expected bytes. The implementation incorrectly
   compares the match source address with the compressed input's end address.

   The valid empty block in R3 supplies an additional R2 failure: depending on
   placement and neighboring bytes, it returns 4 or traps instead of returning 0.

3. **R3 — refuted: the decoder successfully reads outside a valid block.**

   Use the valid one-byte empty block `00` at 1024, with `n = 1`, output at 2048,
   byte 2047 set to `41`, byte 1026 set to zero, and bytes 2048–2051 cleared.
   Change only byte 1025, which is OUTSIDE the block:

   ```text
   byte 1025 = 00: lz4BlockDecode(1024, 1, 2048) = 0
   byte 1025 = 01: lz4BlockDecode(1024, 1, 2048) = 4
   ```

   In the second case V8 additionally checks the four written bytes are `AAAA`.
   The decoder consumes bytes 1025 and 1026 as an offset, although the block
   ended at 1025. This is successful out-of-block reading, not merely a trap.

   There is also a boundary witness requiring no initialization at all: on a
   fresh instance, all memory is zero, so byte 65535 is a valid empty block.
   `lz4BlockDecode(65535, 1, 0)` traps. A direct Wasmtime invocation of the raw
   artifact identifies bytecode offset `0x32c`, an `i32.load8_u`, attempting to
   read address 65536 in a 65536-byte memory. The script checks the instruction's
   actual bytes `2d 00 00`, trap location, address, and trap classification.
   Thus an output-buffer shortage cannot explain this failure.

The exact supporting theorem statements in [Proofs/FormatFacts.lean](Proofs/FormatFacts.lean)
are below, inside namespace `FormatFacts`:

```lean
r1_bad_tail : ¬ TailOK (5 + 4 + 4) 4
r1_bad_match : ¬ LastMatchOK 4 4
r2_end_rules : TailOK (1 + 7 + 5) 5 ∧ LastMatchOK 7 5
empty_literal_block : LiteralBlock [0] []
empty_tail : TailOK 0 0
kernel_control : (0 : Nat) = 0
```

Their three specification definitions are:

```lean
def TailOK (decodedSize finalLiterals : Nat) : Prop :=
  5 ≤ finalLiterals ∨ (decodedSize < 5 ∧ finalLiterals = decodedSize)
def LastMatchOK (matchLength finalLiterals : Nat) : Prop :=
  12 ≤ matchLength + finalLiterals
def LiteralBlock (block content : List Nat) : Prop :=
  content.length < 15 ∧ block = (16 * content.length) :: content
```

These are small format facts, not a complete definition of LZ4 validity.
`TailOK` states a necessary numerical condition; the parser also checks the
single-sequence small-input exception. `LiteralBlock` states the short literal
sequence's token/length shape; the empty witness contains actual byte 0.
The Lean proofs establish these specification facts, **not WebAssembly execution**.
The conclusions about the artifact are concrete execution demonstrations, as
permitted by the task. No universal implementation correctness theorem is claimed.

The execution link is the actual 1,226-byte `lz4-block-codec.wasm`, SHA-256
`4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf`.
[verification/check.py](verification/check.py) checks this digest, embeds those
exact bytes as a binary module in WAST, and runs assertions through Wasmtime.
[verification/runtime.js](verification/runtime.js) directly instantiates the
same file through V8. Neither path executes a handwritten codec model, recompiles
from WAT, or instruments the artifact. The WAT, README, CHECK, and local format
document are also hash-pinned. Their correspondence to the binary is not assumed.
The Python parser is a specification oracle for the three explicit blocks, not
an execution model of the shipped implementation.

For proof replay, `leanexport` exports the six roots and their entire dependency
closure. Lean's kernel (`leanchecker --from-export`) and Con-Ron (`--verified
--jobs=1`) independently accept the same stream. It contains **no axiom records**;
Lean also reports no axioms for every theorem. The closure is 153 declaration
records, 5,748 NDJSON lines, 311,545 bytes, including standard-library dependencies
and proof terms. Replay starts from each checker's own kernel foundations.
Mathlib is available but these elementary proofs do not need it.

The checking setup has positive AND negative controls. After accepting the genuine
stream, each kernel receives two well-formed mutated streams retaining the proof
`Eq.refl 0` but changing its claimed type to `0 = 1` and to `False`, respectively.
Both must exit 1 with a type mismatch naming `FormatFacts.kernel_control`; a crash,
parse failure, or missing tool does not count as rejection. Both execution
engines must also reject a false expected final encoder byte, `00` in place of
actual `5a`. All these checks passed. Generated negative streams are retained for
inspection and regenerated on every run.

The local review surface, including proof bodies and harnesses, is:

| File | Lines | Bytes | What must be reviewed |
|---|---:|---:|---|
| `Proofs/FormatFacts.lean` | 40 | 1,581 | Three format definitions, six statements, proofs |
| `Proofs.lean` | 1 | 26 | Library import |
| `verification/cases.json` | 6 | 155 | Exact counterexample bytes |
| `verification/check.py` | 228 | 10,947 | Hash pins, specification parser, WAST generation, replay, negative controls |
| `verification/runtime.js` | 43 | 2,199 | Independent direct artifact execution and assertions |
| `check` | 4 | 77 | Single-command launcher |
| **Total** | **322** | **14,985** | Excludes this report and generated files |

The complete local formal file is 40 lines; all transitive formal dependencies
are additionally available in the exported closure sized above, rather than
hidden behind trusted imports during replay. For interpreting the requirements,
review README (18 lines, 1,798 bytes), CHECK (8 lines, 784 bytes), and the local
format document (244 lines, 10,683 bytes), especially its three end conditions.
Execution evidence additionally trusts Python/Node, the two independent Wasm
engines, the WAST machinery, wasm-tools, SHA-256, and the host platform. Formal
replay trusts the two independent proof-kernel implementations and their built-in
foundations. The exporter is cross-checked by both kernels but the mapping from
source names to exported statements remains part of the tooling boundary.
The codec's WAT is 745 lines, 21,827 bytes; it is pinned for preservation and is
not a premise of any result. These demonstrations do not enumerate other bugs
or establish any universal property beyond refuting R1–R3.
