# Verification results

**R1, R2, and R3 are false for the shipped artifact.** Each has a concrete
counterexample executed by Wasmtime. Lean checks the format interpretation of
the witness blocks. These are demonstrations of failure, not a universal
correctness proof or a formalization of WebAssembly execution in Lean.

## Artifact and connection to the results

The tested file is `lz4-block-codec.wasm`, exactly **1,226 bytes**, SHA-256
`4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf`.
`verification.py` rejects a different size or digest, validates the module with
`wasm-tools`, and embeds those exact bytes in WAST `module ... binary`
declarations. WAST wrappers import the exported memory and functions; they do
not replace or modify the module. All observations below are checked with
`assert_return` or `assert_trap`, including individual output bytes.

The supplied `.wat` is not used to execute the tests, and no source/binary
equivalence claim is needed. For code inspection, use
`wasm-tools print lz4-block-codec.wasm`, which disassembles the tested binary.

`Proofs/Counterexamples.lean` defines an independent reference interpretation
of `lz4_Block_format.md`: token nibbles, extension lengths, literal copying,
little-endian nonzero offsets into prior output, forward overlapping match
copying, and end-of-block restrictions. Its `decode` returns `some content`
only when the block passes those checks. Parsing fuel is based on the number
of compressed bytes; each sequence/extension step consumes a byte. Lengths
use unbounded naturals. The optional relaxed interpretation disables only
the final literal-count and last-match-distance checks.

The reference interpretation is a specification model, not a model of the
shipped encoder/decoder. Its general correspondence to the prose specification
is a review obligation; it is not itself proved. Only the concrete calculations
listed below are claimed as Lean theorems. The concrete decimal byte lists in
Lean and `verification.py` must also be compared during review. The binary's
observed behavior is connected to those lists by the WAST assertions, rather
than by a Lean refinement theorem.

## R1: encoder returns an invalid block

Initialize all 65,536 four-byte hash entries at addresses `[0, 262144)` to
`-65536`, as required. Grow memory from one to six pages. Place these 13 bytes
at address 262144, immediately after the table:

```text
ASCII: abcdabcd12345
hex:   61 62 63 64 61 62 63 64 31 32 33 34 35
```

Call `lz4BlockEncode(262144, 13, 300000)`. It returns **13**, and writes:

```text
40 61 62 63 64 04 00 50 31 32 33 34 35
```

The first sequence has four literals, offset 4, and match length 4. The last
sequence has five literals. The last match starts at decoded position **4**;
the decoded end is **13**, only **9** bytes later. The specification's end
condition 3 requires at least **12**. The block is therefore invalid. All
buffers are disjoint and within allocated memory, and input size 13 is allowed.

The artifact also decodes these returned bytes back to the input when output
is at 340000, as the harness checks. The failure of R1 is its validity clause;
this witness does not allege a round-trip failure.

Exact theorem statements, in namespace `LZ4` in
`Proofs/Counterexamples.lean`:

```lean
theorem r1_rejected : decode r1Wire = none
theorem r1_content : decodeIgnoringEndConditions r1Wire = some r1Input
theorem r1_last_match_too_late : ¬ (4 + 12 ≤ r1Input.length)
```

Here `r1Input` and `r1Wire` are exactly the input and output byte lists above.
The failure is also visible in the disassembly: the inner match-search loop
allows searches through `inputEnd - 5`, rather than stopping sufficiently early
to enforce the last-match condition.

## R2: valid block is decoded incorrectly

In a fresh one-page memory, place this valid ten-byte block at address 1024:

```text
13 61 01 00 50 61 61 61 61 61
```

The first token specifies one literal `61`, offset 1, and match length 7.
The last sequence supplies five more literal `61` bytes. Its content is
exactly thirteen ASCII `a` bytes. The last match starts at position 1, exactly
12 bytes before the decoded end. All end conditions hold.

Fill output addresses `[0, 13)` with `cc`, and call
`lz4BlockDecode(1024, 10, 0)`. The artifact returns **1**, and the thirteen
output bytes are:

```text
61 cc cc cc cc cc cc cc cc cc cc cc cc
```

The expected return is **13**, with all thirteen bytes equal to `61`.
Output and compressed input do not overlap, and both have sufficient memory.
The README imposes no requirement that decoder output follow compressed input
in memory. In the binary, the first match source address is 0; the decoder
prematurely exits because it compares this address with compressed-input end
1034. This is the wrong boundary for prior decoded output.

Exact theorem statements in `Proofs/Counterexamples.lean`, namespace `LZ4`:

```lean
theorem r2_valid_content : decode r2Wire = some r2Content
theorem r2_length : r2Content.length = 13
theorem r2_wrong_return : (1 : Nat) ≠ r2Content.length
```

`r2Wire` is the ten-byte list above; `r2Content = List.replicate 13 97`.
The R3 witnesses below independently violate R2 for the explicitly permitted
empty block.

## R3: decoder reads outside even a valid block

The single byte `00` is a valid empty block, explicitly described by the
specification's end condition 2. In a fresh one-page memory (65,536 bytes),
place it at address **65535** and call
`lz4BlockDecode(65535, 1, 0)`. The artifact **traps with an out-of-bounds
memory access**, instead of returning 0. The declared block itself is entirely
within memory. After reading its token, the decoder takes the zero-literal
branch and tries to read a match offset starting at **65536**, outside both
the block and memory. It has performed no output copy at that point.

The harness additionally demonstrates dependence on out-of-block bytes
without any memory trap. Before each call it resets the entire one-page memory
to zero, sets address 4095 to `61`, and fills `[4096, 4109)` with `cc`.
In both cases, the supplied block is `00` at address 1024, length 1, with
output at 4096. Only address **1025**, outside the block, differs:

| Bytes at 1025–1026 | Return | Output observation |
| --- | --- | --- |
| `00 00` | 0 | No decoded bytes |
| `01 00` | 4 | `61 61 61 61` at 4096–4099 |

The module has no hidden imports or mutable globals. The differing return
values from these otherwise identical initial memories demonstrate a read
outside the declared one-byte block. This witness involves no address wrap,
overlapping input/output, or malformed compressed input. It also avoids the
possible ambiguity of counting legitimate match reads from decoded output:
an empty block has no match at all.

Exact theorem statements in `Proofs/Counterexamples.lean`, namespace `LZ4`:

```lean
theorem empty_valid_content : decode [0] = some []
theorem boundary_address_outside :
    ¬ (65535 ≤ (65536 : Nat) ∧ 65536 < 65535 + 1)
```

## Reproduce every check

Run from this directory, with the installed Lean/Mathlib v4.35.0 and tools
on PATH. No network or additional packages are used:

```sh
lake build
lake env lean Proofs/Counterexamples.lean
python3 verification.py --emit /tmp/lz4-counterexamples.wast
```

`lake build` must exit 0 with `Build completed successfully`; the direct Lean
check must exit 0 without errors. Proofs use kernel-checked `by decide`, not
`native_decide`, `sorry`, or project-specific axioms. The Python check must
exit 0 and print:

```text
PASS: exact 1226-byte artifact SHA-256 verified; Wasm validation succeeded
PASS R1 counterexample: encode returns 13 and the asserted nonconforming bytes
PASS R2 counterexample: valid 13-byte content is truncated to one byte
PASS R3 counterexample: valid empty block traps at the memory boundary
PASS R3 additional check: outside-block bytes change empty decode return 0 -> 4
All counterexample assertions passed. R1, R2, and R3 are FALSE.
```

The emitted WAST can be inspected and rerun directly:

```sh
wasmtime wast -C cache=n /tmp/lz4-counterexamples.wast
```

Exit 0 means every assertion passed; an assertion mismatch or unexpected trap
is an error. Caching is disabled because the default cache location is
read-only in the supplied environment. The boundary trap is an *expected*
`assert_trap`; Wasmtime accepting it is evidence of failure, not codec success.

To audit the exact logical axiom dependencies after building:

```sh
lake env lean --stdin <<'LEAN'
import Proofs
#print axioms LZ4.r1_rejected
#print axioms LZ4.r1_content
#print axioms LZ4.r1_last_match_too_late
#print axioms LZ4.r2_valid_content
#print axioms LZ4.r2_length
#print axioms LZ4.r2_wrong_return
#print axioms LZ4.empty_valid_content
#print axioms LZ4.boundary_address_outside
LEAN
```

The four reference-decoder calculations report only Lean's standard `propext`;
the other four theorems report no axioms. No theorem depends on `sorryAx`.

## Review and trust boundary

Task-specific files to read, with sizes measured as lines / bytes:

| File | Size | Role |
| --- | ---: | --- |
| `README.md` | 18 / 1,798 | Requirements and caller contract |
| `CHECK.md` | 8 / 784 | Reporting contract |
| `lz4_Block_format.md` | 244 / 10,683 | Authoritative prose format definition |
| `Proofs/Counterexamples.lean` | 83 / 3,534 | Reference definitions, witness constants, eight theorems |
| `Proofs.lean` | 1 / 30 | Imports the proof module into the Lake target |
| `verification.py` | 134 / 5,802 | Hash check, binary embedding, memory setup, assertions, tool invocation |
| `lakefile.toml` | 12 / 264 | Lake configuration |
| `lean-toolchain` | 1 / 25 | Lean version |
| `lake-manifest.json` | 117 / 3,536 | Dependency versions |
| `lz4-block-codec.wasm` | 1,226 bytes | Exact subject; identified by digest above |

The generated WAST is fully determined by the artifact and Python script;
`--emit` exposes it for independent review. The original WAT (21,827 bytes)
is unnecessary to the evidence.

Beyond these files, the result trusts the Lean 4.35.0 kernel and standard
logical foundations, the imported Lean/Mathlib definitions used by the proof,
Wasmtime's implementation of WebAssembly and WAST assertions, wasm-tools'
binary validation, Python's standard library (including hashing and process
execution), and the host environment. Those toolchains have not been formally
verified or source-audited here; the file sizes above describe the local
review surface, not the complete toolchain trusted computing base. Tested
runtime versions were Wasmtime 50.0.0, wasm-tools 1.262.0, and Python 3.14.8.

There is no claim that Lean proves the runtime engine correct or proves an
instruction-level property of the binary. The conclusions combine checked
format calculations with direct, reproducible executions of the exact
artifact. One counterexample suffices for each universally quantified
requirement, so no remaining universal correctness proof is claimed.
