All three requirements fail. These are counterexample demonstrations on the
shipped binary, supplemented by kernel-checked facts about the witnesses. No
universal correctness theorem or formal WebAssembly interpreter is claimed.

Run everything, offline, from this directory:

```sh
python3 check.py
```

Exit status 0 and the final `SUCCESS: R1, R2, R3 refuted; ...` line mean success.
The `REJECTED as required` lines are successful negative controls. Any unexpected
acceptance, failed assertion, missing tool, or failed positive check stops the
command. Generated evidence is in `.verification/`.

R1 fails: invalid encoder output
-------------------------------

Start with six WebAssembly memory pages. Fill the 65,536 little-endian i32 words
at address 0 with −65536. Put the following 13 bytes at address 262144:

```text
61 62 63 64 64 64 64 64 65 66 67 68 69   (abcdddddefghi)
```

`lz4BlockEncode(262144, 13, 327680)` returns **13** and writes exactly:

```text
40 61 62 63 64 01 00 50 65 66 67 68 69
```

Token `40` gives four literals (`abcd`) and a four-byte match. Offset `01 00`
is 1. Token `50` introduces the five final literals (`efghi`). The match starts
at decoded offset 4, only **9 bytes** before the end of the 13-byte content.
This violates end-of-block condition 3 in `lz4_Block_format.md`, which requires
at least 12. The compressed length is also 13, so counting from the compressed
end would not rescue this example. Decoding this output at address 350000 does
return the original input; the format-validity conjunct of R1 is what fails.

Both Wasmtime and V8 assert the returned size, every emitted byte, and that
round trip. The exact accompanying theorem in `Proofs/Counterexamples.lean`,
inside namespace `Counterexamples`, is:

```lean
theorem r1 :
    wire [97,98,99,100] 4 [101,102,103,104,105] = encoderBlock ∧
    content [97,98,99,100] 4 [101,102,103,104,105] = encoderInput ∧
    ¬ EndOK 4 [101,102,103,104,105]
```

R2 fails: valid input, incorrect content and length
--------------------------------------------------

In a one-page memory put this ten-byte block at address 4096:

```text
13 61 01 00 50 62 63 64 65 66
```

It describes one literal `a`, a seven-byte offset-1 match, and five literals
`bcdef`. Its decoded content is `aaaaaaaabcdef`, 13 bytes. The final match
starts at offset 1, exactly 12 bytes before the end, and the five final bytes
are literals. It is a valid independent block with no length extensions.

`lz4BlockDecode(4096, 10, 1024)` returns **1**, writes `61`, and leaves the next
12 output bytes unchanged. Both runtimes check this; V8 uses sentinel `cc`
and Wasmtime uses initially zero memory. The input and output buffers are
disjoint and fit in memory. The README imposes no ordering between these buffers.
As a control, decoding the identical block to address 8192 correctly writes all
13 expected bytes. The binary compares the match pointer with the compressed
input end (`0x340`–`0x345`), which explains the dependence on buffer placement.

The exact theorem is:

```lean
theorem r2 :
    RunValid [97] 7 [98,99,100,101,102] ∧
    wire [97] 7 [98,99,100,101,102] = decoderBlock ∧
    content [97] 7 [98,99,100,101,102] = decoderContent ∧
    decoderContent.length = 13 ∧ (1 : Nat) ≠ decoderContent.length
```

`RunValid` is a sufficient validity condition for this small fragment of the
format, with literal lengths below 15, match lengths 4–18, and offset 1.
`wire` constructs its bytes; `content` describes the offset-1 copy, including
overlap; `EndOK` states the two numerical end conditions. These definitions
describe the specification fragment, not an implementation of the Wasm codec.
Their correspondence with the supplied prose specification must be reviewed.

R3 fails: read beyond a valid empty block
----------------------------------------

Use a one-page memory (65,536 bytes), put `00` at address 65535, and call:

```text
lz4BlockDecode(65535, 1, 1024)
```

The format explicitly allows `00` to represent empty content (end-of-block
condition 2). Both runtimes report an out-of-bounds memory trap. V8's stack
identifies function 3, binary offset **0x32c**, which is `i32.load8_u` with
offset 0. The instruction tries to load address **65536**, outside the supplied
block `[65535,65536)` and outside memory. This is a read, not an output overflow.
The script checks the instruction bytes at `0x32a`–`0x32e` and the V8 trap
location; `.verification/r3-trace.txt` and `.verification/artifact.dump` retain
the evidence. This valid-block trap also independently violates R2.

The exact auxiliary theorem checks the placement arithmetic only:

```lean
theorem r3 : 65535 + [0].length = 65536 ∧
    ¬ (65536 < 65535 + [0].length) ∧ ¬ (65536 < 65536)
```

It does not prove a Wasm execution or formalize the empty-block rule. The rule
is explicit in the supplied format document; the actual load is demonstrated
by the runtimes and the binary instruction evidence.

Artifact connection and independent checks
------------------------------------------

`check.py` requires exactly **1,226 bytes** with SHA-256:

```text
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

It embeds those exact bytes in `.verification/runtime.wast`. The harness
imports the shipped exports and memory. `verification/runtime.cjs` separately
instantiates those same original bytes in V8. Neither uses the hand-written
`.wat`, recompiles the implementation, patches the artifact, or runs a codec
model. The fixture arrays for both runtimes are extracted from the four literal
data definitions in the Lean file, preventing separate fixture copies from
silently diverging. All codec source and binary files are unchanged.

The command checks the Lean source afresh, builds the Lake target, and exports
`r1`, `r2`, `r3` and two checking canaries, together with all their dependencies.
The same `.verification/proofs.ndjson` is replayed by:

- **con-ron**, Rust kernel, `--verified --jobs=2`;
- **con-leche**, Lean implementation, `--verified --jobs=2`;
- **Nanoda**, separate Rust kernel, with an empty permitted-axiom list.

Con-ron and con-leche are separate implementations of the same checker design;
Nanoda supplies an additional independent design. All three accept. The closed
export contains **zero axiom declarations**, including no `sorryAx` or
`Lean.trustCompiler`. Proofs use kernel-reduced `decide`, not `native_decide`.

For negative controls the command changes the exported `kernelCanary` theorem
from `True.intro : True` to `True.intro : False`. The export remains syntactically
well formed. Con-ron and con-leche must return rejection status 1 with a theorem
type-mismatch diagnostic. Nanoda must reject with its definitional-equality
assertion diagnostic (status 101); its panic is not counted as proof acceptance
or as a generic parse failure. The Lean frontend separately rejects
`False := True.intro` and `(0 : Nat) = 1 := rfl`. Wasmtime rejects a valid WAST
script changed to falsely expect R2's result to be 13, and the V8 harness checks
that the corresponding false assertion raises an assertion error.

Required tools are Python 3, Node, `wasmtime`, `wasm-tools`, Lean/Lake, and
`leanexport`, `con-ron`, `con-leche`, `nanoda_bin` alongside the resolved Lean
binary. No network or installation is used. Tested here with Lean 4.35.0,
Wasmtime 50.0.0, wasm-tools 1.262.0 and Node v26.11.1.

Review surface and limits of the evidence
-----------------------------------------

The complete local mathematical file, including all eight custom definitions,
the statements, proofs, comments, and two canaries, is
**56 lines / 2,371 UTF-8 bytes** (`Proofs/Counterexamples.lean`). It imports only
`Init`; Mathlib is not needed for these counterexamples. The local files a
reviewer must inspect for the claims and their artifact linkage are:

| File | Lines | Bytes | Purpose |
| --- | ---: | ---: | --- |
| `Proofs/Counterexamples.lean` | 56 | 2,371 | Specification fragment, data, exact statements and proofs |
| `Proofs.lean` | 1 | 30 | Library import |
| `check.py` | 162 | 8,058 | Artifact identity, witness extraction, WAST, export, replay and negative controls |
| `verification/runtime.cjs` | 41 | 2,031 | Separate V8 execution and read-site evidence |
| **Total** | **260** | **12,490** | Includes comments and blank lines |

The custom specification is deliberately restricted to the witnesses. It is
not a formalization of every LZ4 block, nor a claim that passing a test proves
universal correctness. A single exhibited counterexample suffices to refute
each universal requirement.

The 56-line figure does **not** hide imported mathematical dependencies: the
entire transitive exported proof closure is **214 declaration records**
(148 definitions, 41 theorems, 25 inductive blocks), **8,750 JSON records /
470,402 bytes**. It includes core natural-number arithmetic and order, lists,
booleans, equality, propositional connectives, decision procedures and their
helpers. That bundle is a conservative superset of all definitions needed to
interpret the statements, and is available in `.verification/proofs.ndjson`;
all its proof terms are rechecked. Fully auditing meanings also requires reading
the relevant core definitions, rather than treating the local line count as
the entire mathematical review surface. `.verification/sizes.json` recomputes
the file sizes and full closure census on every run.

The supplied README (18 lines / 1,798 bytes), format document (244 lines /
10,683 bytes), and CHECK.md (8 lines / 784 bytes) establish the intended claims.
The existing Lake configuration and toolchain files select the compiler and
package environment. Also trusted are the host tools, runtime implementations,
binary validation/disassembly, proof export machinery, OS and hardware; their
implementations are not included in the local source-size totals. Replaying
through multiple kernels and runtimes and testing false claims reduces reliance
on any one checker but is not a formal proof of those tools' soundness. In
particular, execution observations are runtime-checked evidence, not Lean
theorems about WebAssembly semantics. No handwritten implementation model is
substituted for the shipped artifact.
