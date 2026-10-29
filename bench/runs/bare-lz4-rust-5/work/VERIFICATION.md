# Verification of `lz4-flex.wasm`

**Status: partial verification. R1, R2, and R3 remain unproved in their full
generality. No counterexample was found.** The `PASS` messages below certify
only the explicitly described results; they are not a certification of the
three universal requirements.

The artifact was not changed. Its size is 7,161 bytes and its SHA-256 is
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.
All work is offline, using Lean 4.35.0 and the existing Mathlib v4.35.0 project.

## Results for each requirement

| Requirement | Established results | What remains open |
| --- | --- | --- |
| R1: confinement of reads and writes | Kernel theorem `Verification.zero_length_rejected` covers **every call with `n = 0`**, for arbitrary memory and arguments. `Verification.short_cases_checked` checks all memory accesses in the first five fixtures. The Lean execution checker checks every load, store, bulk-copy read/write, and fill in all 31 fixtures. Direct Wasm tests also check writes as described below. | Confinement for arbitrary nonempty input, capacity, buffer placement, and initial memory. Tests of unchanged surrounding memory cannot establish read confinement. |
| R2: correct decoding of every valid independent block that fits | `Verification.short_cases_checked` establishes successful decoding of `[0]`, `[15]` (empty final sequence), and `[16,97]` (one literal), with the specific capacities and initial states in the fixtures. The Lean execution checker checks 19 fixtures with valid end conditions against explicit sequence certificates and expected output. Wasmtime checks the exact artifact's return values and output bytes for these and the other fixtures. | Completeness and output correctness for **all** valid blocks and **all** capacities in which they fit. No full refinement theorem from the Wasm loops to LZ4 decoding was established. |
| R3: successful returns have bounded length and a valid independent sequence decoding | The same kernel theorem checks this implication for the successful first-five fixtures. The Lean execution checker checks it for all 20 successful fixtures, including a block that breaks the end conditions. Its certificates check exact input consumption, match offsets, decoded content, and output length/capacity. | Soundness for every possible successful return, including arbitrary malicious inputs and arbitrary initial destination bytes. No universal invariant proves this implication. |

The two arithmetic theorems below establish a useful bound for the missing
proof: the caller's memory-size limit rules out 32-bit overflow of the sum of
extension bytes and of that sum plus a bounded output position and 19. Applying
the bound to every reachable Wasm state still requires a loop invariant.

The missing proof is substantive: it must relate the input cursor, emitted
prefix, offset checks, extended lengths, fast-path speculative copies, slow
path, and termination for arbitrary data. The finite results here do not
discharge that obligation. Nor is this an impossibility result for proving it.

## Exact kernel-checked statements

In these statements, `Wasm.word = 4294967296`, memory is a function
`Nat → Nat`, `Wasm.run` executes the extracted instructions with a step bound,
and access records contain direction, address, and width. The raw i32 bit
pattern `4294967295` represents `-1`.

`Proofs/Results.lean`:

```lean
theorem Verification.zero_length_rejected
    (src dst cap : Nat) (m : Wasm.Memory) :
    ∃ s, Wasm.run Artifact.decoder 5 (Wasm.initial src dst 0 cap m) =
      Wasm.Outcome.returned 4294967295 s ∧
      s.mem = m ∧ s.accesses = []
```

This is stronger than merely checking unchanged output: there are no reads
or writes at all. Restricting its arguments to the README preconditions gives
the stated R1 result for `n = 0`. Empty compressed input is not the valid
encoding of empty content; that encoding is `[0]`.

`Proofs/Corpus.lean`:

```lean
theorem Verification.short_cases_checked :
    (Verification.cases.take 5).all Verification.check = true
```

The first five fixtures, in order, are:

| Name | Input bytes, hexadecimal | Capacity | Return | Successful content |
| --- | --- | ---: | ---: | --- |
| `no-token` | empty | 0 | -1 | — |
| `empty-block` | `00` | 0 | 0 | empty |
| `final-low-nibble` | `0f` | 0 | 0 | empty |
| `one-literal` | `10 61` | 1 | 1 | `61` |
| `one-literal-capacity-zero` | `10 61` | 0 | -1 | — |

These have source address 131072 and destination address 262144. Initial
destination bytes are 165; other caller memory is zero except for the source.
`Verification.check` is defined in `Proofs/Checks.lean`. It requires:

* byte-valued input, nonoverlap, and buffers within the caller region;
* an actual returned outcome, excluding traps, unsupported instructions/calls,
  and fuel exhaustion;
* the specified return value;
* every recorded read inside source or destination, and every write inside
  destination; all accessed addresses are in the caller region;
* for success, `r ≤ cap`, exact output bytes and length, and a valid independent
  sequence certificate; valid-end fixtures must also satisfy the end conditions.

`Proofs/Format.lean`:

```lean
theorem LZ4.extension_sum_bound (xs : List Nat)
    (h : ∀ x ∈ xs, x ≤ 255) :
    xs.sum ≤ 255 * xs.length

theorem LZ4.lengths_fit_i32 (n cap pos extra : Nat)
    (hn : n ≤ 2097152 - 131072)
    (hc : cap ≤ 2097152 - 131072)
    (hp : pos ≤ cap) (he : extra ≤ 255 * n) :
    extra + 19 < Wasm.word ∧ pos + extra + 19 < Wasm.word
```

These are arithmetic facts, not separate theorems that the artifact maintains
their hypotheses. The four proofs use no `sorry`, admitted assumptions, or
`native_decide`. `verification/Audit.lean` prints their statements and axiom
dependencies. The two execution theorems depend only on `propext`; the arithmetic proofs
use `propext`, `Quot.sound`, and (for `lengths_fit_i32`) `Classical.choice`,
as reported by that audit.

## Other machine-checked results

1. `Verification.main` in `Proofs/Corpus.lean` executes
   `Verification.check` on **all 31** fixtures in `verification/cases.json`.
   This is a Lean executable computation, rather than a kernel proof of the
   all-31 proposition. Each run has a 50,000-instruction fuel limit; an exhausted
   or unsupported run fails. Success prints
   `PASS: 31 artifact executions, access traces, and sequence certificates`.
   Fixtures include both decoder paths, overlapping matches, offsets one and
   greater than one, 32/64-byte speculative copies, bulk copying, extended
   literal and match lengths, malformed blocks, insufficient output capacity,
   unaligned source buffers, and destinations ending at the memory boundary.
2. `verification/wasmtime_cases.py` embeds the **unmodified artifact bytes** in
   fresh Wasm instances in a generated WAST file. Wasmtime checks all 31 return
   values and all **1,154** successful output bytes. This independently checks
   those observations against the Lean model's fixtures. It does not observe
   memory reads or establish semantic equivalence of the model in general.
3. `verification/test.mjs` directly instantiates the exact artifact in Node's
   Wasm engine and makes **468,582 calls**. It checks return values and successful
   bytes against an independent slow LZ4 parser. Coverage is:
   * the 31 fixtures, with snapshots checking every caller-region byte outside
     destination for changes;
   * all 65,793 inputs of lengths zero through two, at capacities
     `0, 1, 2, 4, 18, 34, 64`;
   * 5,000 deterministically generated arbitrary inputs;
   * 1,000 deterministically generated independent valid blocks, each at three
     capacities: decoded length minus one, decoded length, and length plus 64.
   All calls check source preservation; non-fixture calls check 32-byte
   destination guards where those addresses exist. **These are tests, not a
   universal proof, and they do not check reads.** The random seed is fixed.

There is no failing input to report: none of these checks found one.

## Connection to the shipped bytes and specification

`verification/extract.py` reads `lz4-flex.wasm` itself. It checks its length and
SHA-256, absence of imports, fixed 32-page memory, decoder export index and
signature, and local declarations. It decodes the bytecode of function 7 into
`Proofs/Artifact.lean`, retaining every instruction and resolving block ends.
It fails on an unexpected opcode, block signature, or memory immediate. Its
`--check` mode regenerates in memory and requires byte-for-byte equality with
the checked-in Lean file. No Rust rebuild, source-to-binary assumption, or WAT
pretty-printer is used for the Lean connection.

`Proofs/Wasm.lean` is a **handwritten instruction-semantics model**. It handles
the encountered instructions, unsigned comparisons, i32 wrapping arithmetic,
little-endian loads/stores, structured branches, overlapping `memory.copy`,
and `memory.fill`. It bounds accesses by the actual 2 MiB memory and records
their complete widths, including speculative bytes. Calls are unsupported;
none of the accepted checked executions reaches one. This deliberately does
not treat an unsupported call as a successful return or a benign error.

The model is not proved equivalent to an existing formal Wasm semantics. The
extractor and this semantics must therefore be reviewed and trusted for the
kernel results to describe the artifact. The independent Wasmtime and Node
checks supply bounded cross-checks, not a proof of this bridge.

The modeled fixture memory omits private module data below 131072.
`Verification.check` requires every recorded access to be at least 131072,
which justifies that omission for these executions. The zero-length theorem
uses arbitrary memory and accesses none of it. Caller preconditions ensure all
parameters are representable as i32. The source, Rust compiler, crate feature
claims, and `build.sh` are not used as proof premises.

`Proofs/Format.lean` interprets explicit sequence certificates against the local
`lz4_Block_format.md`: token nibbles, terminated 255-byte length extensions,
literals, 16-bit little-endian offsets, minimum match length four, independent
offset bounds, and byte-by-byte overlapping match generation. The final low
nibble has no match to describe. `certificate` requires exact re-encoding of
the entire input and exact decoded content; `endConditions` is a separate check
so R3 can allow violations only of those end conditions. This specification's
correspondence to the English document is also a human review obligation.

## Reproduction

From this directory, with the installed offline toolchain:

```sh
bash verification/check.sh
```

The script runs these exact checks, stopping on any nonzero exit status:

```sh
python3 verification/extract.py --check
python3 verification/gen_cases.py --check
wasm-tools validate lz4-flex.wasm
lake build
lake env lean verification/Audit.lean
lake env lean --run Proofs/Corpus.lean
python3 verification/wasmtime_cases.py
node verification/test.mjs
```

Success means every command exits zero, Lake reports a successful build, the
axiom audit contains no `sorryAx` or native-reduction axiom, and the final line
is `PASS: all documented checks (the universal R1-R3 obligations remain open)`.
`wasm-tools validate` is silent on success. Wasmtime is invoked with
`-C cache=n` to avoid needing a writable home cache. Temporary WAST files are
created in the system temporary directory and removed automatically.
No network, Cargo build, or modification of the artifact is required.

## Review and trust inventory

Sizes below are physical lines and bytes. Generated files are included so a
reviewer can inspect exactly what Lean checked. The inventory does not imply
that fixture selection gives complete coverage.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 199 | 7088 | Trusted partial Wasm semantics and access trace |
| `verification/extract.py` | 155 | 5552 | Trusted binary-to-instruction bridge and identity guard |
| `Proofs/Artifact.lean` | 992 | 18840 | Generated decoder instructions |
| `Proofs/Format.lean` | 86 | 3397 | Trusted LZ4 specification and arithmetic proofs |
| `Proofs/Checks.lean` | 50 | 1760 | Exact meaning of fixture success |
| `Proofs/Results.lean` | 15 | 484 | Universal zero-length theorem |
| `Proofs/Corpus.lean` | 23 | 719 | Kernel theorem and executable corpus check |
| `Proofs/Cases.lean` | 411 | 18317 | Generated explicit fixture definitions |
| `verification/cases.json` | 3063 | 36356 | Explicit input/output/certificate fixture data |
| `verification/gen_cases.py` | 41 | 1681 | JSON-to-Lean fixture renderer |
| `verification/test.mjs` | 119 | 4750 | Direct artifact tests and independent slow parser |
| `verification/wasmtime_cases.py` | 36 | 1872 | Exact-byte Wasmtime assertion generator/runner |
| `verification/check.sh` | 12 | 413 | Reproduction entry point |
| `verification/Audit.lean` | 11 | 322 | Statements and axiom audit |
| `Proofs.lean` | 2 | 43 | Library imports |
| `lz4_Block_format.md` | 244 | 10683 | English format specification |

The conventional proof trust base is Lean 4.35.0's kernel and standard logical
axioms; Mathlib tactics produce kernel-checked proofs. The executable checks
add trust in the Lean compiler/evaluator, Node v26.12.1's Wasm engine, Wasmtime
50.0.0, Python 3.14, `wasm-tools` 1.262.0, and their runtime dependencies.
SHA-256 identity checking relies on Python's hashing implementation and the
usual collision-resistance assumption. These installed tools/libraries are
external dependencies, not small formally verified components of this work.
