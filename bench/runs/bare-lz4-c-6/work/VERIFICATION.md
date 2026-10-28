# Verification results

**R1, R2, and R3 remain unproved in full. None has been refuted.** This delivery contains machine-checked boundary theorems, a kernel-checked certificate for 33 concrete executions, and exhaustive executable checks of short inputs against the original Wasm. Passing these checks is not a proof of the three general requirements.

The software, README, and format document have not been modified.

## Artifact and connection to the proofs

The artifact checked is `lz4-c.wasm`, 8,469 bytes, SHA-256:

```
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`verification/extract.py --check` checks that length and hash, parses the binary directly, and compares its generated Lean text with `Proofs/Artifact.lean`. It checks the module's types, function indices, exports, fixed 32-page memory, global, and data segment. It extracts function 2 (`LZ4_decompress_safe`) and its only callees, functions 3 and 4 (the copy helpers). Unsupported instructions or call targets cause failure. Structured control is flattened to instruction indices. A control-flow stack-height check verifies that reachable branches have no residual operands to discard. The instruction lookup is represented as a balanced decision tree for efficient kernel reduction.

`Proofs/Wasm.lean` defines the executable instruction semantics: wrapping i32 arithmetic, signed comparisons, locals, operand and call stacks, branches, byte memory, little-endian loads/stores, memory bounds, and traces of every load/store. Effective-address addition for memory instructions does not wrap. Fuel exhaustion or a modeled trap gives `none`; certificates require a completed return.

**The Lean theorems are about this extracted model.** The binary parser/extractor and the correspondence of these semantics to WebAssembly have not themselves been formally verified. Their correctness is part of the trusted connection to the artifact. There is no proof of C compilation or reliance on rebuilding the C source.

An additional, independent connection is provided by `verification/replay.py`: it embeds the original binary bytes unchanged in a WAST script and runs them using Wasmtime. A separate importing module prepares and inspects the exported memory. This validates concrete behavior without using the Lean interpreter to execute the decoder.

## Exact theorem statements

The following statements use `Wasm` and `Artifact` definitions. They are in `Proofs/Boundary.lean`:

```lean
Boundary.zero_capacity_one_byte (m : Memory) :
  observe (run 40 program (initial 131072 262144 1 0 m)) =
    some ((if m.get 131072 != 0 then 4294967295 else 0),
      [⟨false, 131072, 1⟩], m)
```

```lean
Boundary.zero_capacity (src dst size : Nat) (m : Memory)
    (hs : 131072 ≤ src) (he : src < 2097152) :
  observe (run 40 program (initial src dst size 0 m)) =
    some (if size = 1 then (if m.get src = 0 then 0 else 4294967295)
          else 4294967295,
      if size = 1 then [⟨false, src, 1⟩] else [], m)
```

```lean
Boundary.zero_source (src dst capacity : Nat) (m : Memory)
    (hs : 131072 ≤ src) (hc : capacity < 2147483648) :
  observe (run 40 program (initial src dst 0 capacity m)) =
    some (4294967295, [], m)
```

```lean
Boundary.empty_block (src dst : Nat) (m : Memory)
    (hs : 131072 ≤ src) (he : src < 2097152)
    (hz : m.get src = 0) :
  observe (run 40 program (initial src dst 1 0 m)) =
    some (0, [⟨false, src, 1⟩], m)
```

`observe` returns the unsigned i32 result, the complete access trace in reverse execution order, and the complete final memory. Here `4294967295` represents signed `-1`. An access `⟨false, a, n⟩` reads `n` bytes starting at `a`; `true` denotes a write. Thus these equalities also establish termination within the given fuel and preservation of the entire memory, for arbitrary initial memory.

The concrete certificate, in `Proofs/Certificates.lean`, is:

```lean
Certificates.checked_examples :
  Cases.examples.all Cases.conforms = true
```

It is proved with `decide +kernel`. This uses Lean's kernel to reduce the decision procedure; it does not use `native_decide`, an external solver, or an assumed execution result. The definitions of `Cases.examples` and `Cases.conforms` are in `Proofs/Cases.lean` and are part of this statement. There are exactly 33 cases.

For each case, `conforms` checks all of the following:

1. The buffers satisfy the README's address, size, and non-overlap preconditions.
2. The modeled execution terminates and returns the exact signed integer specified in the case.
3. Every byte of every load/store in the trace obeys R1's caller-region access restriction.
4. If the separate format specification considers the input valid and its output fits, subject to R2's capacity condition, the return value is its decoded length.
5. For every nonnegative return, the return is within capacity, the entire input parses with independent offsets, its decoded length equals the return, and all returned output bytes match that decoding. This parsing allows zero offsets with zero-filled matches and relaxes end conditions, as R3 permits.

`Proofs/Format.lean` defines that separate specification (`LZ4Spec.decode`, `validIndependent`, and associated definitions). It parses tokens, terminated length extensions, literal bytes, little-endian offsets, and matches. Matches copy sequentially to support overlap. Independence is checked before each match. `validIndependent` additionally excludes offset zero and enforces the final-literal and last-match-distance conditions. The equivalence of these definitions to the prose format document is a review obligation, not a separately proved theorem.

The cases include empty buffers, empty blocks, truncated lengths/literals, literal lengths 14 and 15, insufficient capacity, overlapping offsets 1–7, offset 8, a match-length extension, a shortcut copy, offset zero, an offset beyond the decoded prefix, end-condition rejection, adjacent buffers in both orders, and buffers ending at address 2097152. Initial destination bytes are 165, so an incorrect zero-offset copy cannot pass merely because the destination started zeroed.

## Status of each requirement

| Requirement | Established results | What remains open |
| --- | --- | --- |
| R1 | `zero_capacity` covers every zero-capacity call satisfying the README preconditions: either no access, or one in-source byte read, and no writes. `zero_source` covers every zero-source-size call under those preconditions: no access at all. `checked_examples` checks the full access trace for each of the 33 cases. | Arbitrary nonempty inputs with positive capacity. No general loop invariants establish bounds for literal extensions, speculative copies, match copies, and all error paths. |
| R2 | `empty_block` establishes the stated zero-capacity exception for the valid one-byte empty block, with arbitrary memory and caller addresses. `checked_examples` checks R2's implication for its valid fitting examples. | All valid blocks and all allowed layouts/capacities. A general relation between the format decoder and the implementation's cursor/output state, including overlap copying and end-condition handling, has not been proved. |
| R3 | `zero_capacity` characterizes every success at zero capacity: size 1, source byte 0, result 0, empty output. `zero_source` shows the premise cannot hold for a zero-sized source. `checked_examples` checks R3's entire parsing/content obligation on every successful example, including offset zero. | All successful executions with positive capacity. A general invariant relating input consumption, decoded prefixes, offsets, and returned lengths has not been proved. |

These are partial verification results, not demonstrations that a requirement fails. There is no failure input to report.

## Additional machine-checked executable results

`verification/replay.py` succeeds only if Wasmtime passes every WAST assertion:

- For the same 33 concrete cases, it checks exact returns and successful output bytes. It also scans **every byte** of the caller region outside the destination buffer and checks preservation of its initial value. This is a write-frame check; it cannot observe reads or detect a write that restores the old value. The Lean certificates provide access traces for their modeled executions.
- It checks every byte string of lengths 0, 1, and 2 at capacities **0, 1, 2, 12, 32, and 64**, with `src = 131072` and `dst = 262144`: 65,793 strings and **394,758 decoder calls**. It checks exact returns and output contents. These exhaustive bounds do not extend to longer strings or other capacities/layouts.

The exact expectations for the short-input checks are:

| Source size | Capacity | Expected signed return/output |
| --- | --- | --- |
| 0 | Any tested capacity | `-1` |
| 1 | 0 | `0` for byte 0; otherwise `-1` |
| 1 | Positive | `0` for token < 16; otherwise `-2` |
| 2 | 0 | `-1` |
| 2 | Positive | `1`, output equal to the second byte, if the first byte's high nibble is 1; otherwise `-2` |

These assertions are executable checks of the actual artifact, not Lean theorems about all inputs.

## Reproduction

From this directory, with the supplied offline Lean/Mathlib installation:

```sh
python3 verification/extract.py --check
wasm-tools validate lz4-c.wasm
lake build
lake env lean --run verification/Export.lean --check
python3 verification/replay.py
```

Every command must exit zero. The extractor prints `PASS: exact artifact SHA-256, structure, and generated instructions`; Wasm validation is silent on success; Lake reports `Build completed successfully`; the export check prints `PASS: runtime cases agree with Lean definitions`. Replay prints:

```
PASS: Wasmtime original-byte replay of 33 cases, including full caller-region write frame
PASS: all 65,793 byte strings of length 0..2, capacities 0,1,2,12,32,64 (394,758 calls)
```

The default Lake target imports all proof modules. To force rechecking the theorem source files even when Lake has cached them, run:

```sh
lake env lean Proofs/Boundary.lean
lake env lean Proofs/Certificates.lean
```

Successful checking prints the axioms of the reported general theorems and certificate: only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms, `sorry` proofs, or native-evaluation axioms. Kernel checking the concrete certificate can take a few minutes; it has an increased recursion limit and no heartbeat limit. The fuel in the executable statement remains finite.

No network, C compiler, or package downloads are needed. Replay disables Wasmtime's compilation cache so it works without a writable home cache directory. `verification/Export.lean --check` checks that `verification/cases.json` agrees with the Lean case definitions. Without `--check`, that helper regenerates the JSON; likewise, running the extractor without `--check` regenerates `Proofs/Artifact.lean`.

## Review and trust inventory

Besides Lean 4.35.0's kernel and its standard logical axioms, the result depends on these definitions and scripts. Sizes below are lines / bytes, including comments and whitespace.

| File | Size | Review purpose |
| --- | ---: | --- |
| `Proofs/Wasm.lean` | 176 / 5,827 | Instruction semantics, memory, access restrictions, execution and termination convention |
| `verification/extract.py` | 213 / 8,159 | Trusted binary parsing, instruction/control translation, module identity and structure checks |
| `Proofs/Artifact.lean` | 2,699 / 108,049 | Generated instruction lookup, data bytes, and prefix lookup lemmas; reproducible by the extractor |
| `Proofs/Format.lean` | 71 / 2,475 | Independent formal interpretation of the format, overlap, offset-zero extension, and validity |
| `Proofs/Cases.lean` | 81 / 4,396 | Exact test inputs, initial memories, expected results, and certificate predicate |
| `Proofs/Boundary.lean` | 68 / 2,671 | Boundary theorem statements and proofs |
| `Proofs/Certificates.lean` | 17 / 433 | Kernel certificate statement and proof |
| `Proofs.lean` | 2 / 50 | Default library's proof imports |
| `verification/Export.lean` | 20 / 768 | Connection between Lean cases and replay data |
| `verification/cases.json` | 1 / 5,140 | Generated replay data, checked by the export helper |
| `verification/replay.py` | 120 / 4,978 | Actual-byte WAST construction, concrete write-frame and short-input assertions |
| `README.md` | 18 / 2,872 | Requirements and interface interpretation |
| `lz4_Block_format.md` | 244 / 10,683 | Prose format against which the formal specification must be reviewed |

The build also uses the installed Lean/Mathlib environment and the existing Lake configuration. The replay additionally trusts Python, its SHA-256 implementation, Wasmtime, and the host running them. `wasm-tools validate` is an auxiliary binary-validity check. No verification result depends on trusting the supplied C source or its build script.
