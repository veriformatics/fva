# Verification results

**Incomplete verification. R1, R2 and R3 are neither proved nor refuted for all permitted calls to the shipped artifact.** The results below are checked source fragments, a restricted model, and finite executions. None is a substitute for a universal artifact proof. No counterexample was found in the executions performed.

The artifact checked is `lz4-c.wasm`, exactly 8,469 bytes, SHA-256:

```
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

**Requirement coverage**

| Requirement | Machine-checked results relevant to it | What remains unproved |
| --- | --- | --- |
| R1: caller-memory access bounds for arbitrary input | E proves no memory modification in an early-exit C slice. M proves the helper contracts below. L proves bounds for every read/write in a literal-only model. T checks access bounds dynamically in 3,234 concrete calls to an instrumented copy of the artifact. | All inputs, buffer placements, destination initial states and decoder paths. In particular, no invariant covering the general decoder's speculative copies and match copies has been proved. T is finite testing and its instrumentation is trusted. |
| R2: successful, correct decoding of every valid fitting independent block | E covers the zero-capacity empty-block case in its source slice. L proves the content/length statement below for a model of blocks with 0–14 literals and no matches. T requires success for 721 valid fitting cases on each module and compares every returned byte. | General literal/match length extensions, arbitrary numbers of sequences, match-copy induction, and a formal connection between the implementation and the complete format definition. |
| R3: every successful result describes a permissible decoding | L proves the literal-only model's exact length, content and frame. T checks every successful concrete result against an independent parser, including zero-offset matches interpreted as zeros and allowing end-condition violations. | The implication from any successful artifact execution to the required sequence decomposition and output, including malformed inputs outside the finite cases. |

**E — early-exit source slice**

Files: [`verification/prepare_wp.py`](verification/prepare_wp.py), generated [`verification/lz4-sliced.c`](verification/lz4-sliced.c), and [`verification/decoder_wp.c`](verification/decoder_wp.c). The exact ACSL statements are immediately before `LZ4_decompress_generic` and `LZ4_decompress_safe` in the generated file.

The public function contract states: for a nonnull source `s`, sizes `0 ≤ n,c ≤ 1966080`, with `n = 0 ∨ c = 0`, and readable `s[0..n)` when `n > 0`, the function terminates, modifies no memory, and returns

```
0   if c = 0 and n = 1 and s[0] = 0;
-1  otherwise.
```

The internal function has the additional preconditions `partialDecoding = decode_full_block`, `dict = noDict`, `dictSize = 0`, `dictStart = NULL`, and `lowPrefix = (const BYTE*)dst`.

The generator retains the original decoder prefix through `if (unlikely(srcSize==0)) { return -1; }`. It replaces the residual body with `assert \false; return -1;`. WP proves that assertion unreachable under the contract; it is not an assumption. The public wrapper is retained and checked against the internal contract. **31/31 WP goals proved**, including the generated RTE goals. See [`verification/decoder.log`](verification/decoder.log).

This is a proof about a mechanically sliced C program under WP's memory semantics. Reading the small slicing transformation is necessary to transfer it to the corresponding paths of the original source. It does not verify the removed decoder body or C-to-Wasm compilation. In particular, it is not a complete ISO C definedness proof: RTE does not check every possible pointer-formation issue in the original pointer setup.

**M — shipped memory-helper source with annotations**

Files: [`verification/memory-contracts.h`](verification/memory-contracts.h) and generated [`verification/memory-annotated.c`](verification/memory-annotated.c). The generator checks that, after removing inserted ACSL annotations and restoring the include name, the helper source is unchanged apart from whitespace.

Exact contract meanings, with byte-indexed buffers `d,s`, initial memory denoted by `old`, and `0 ≤ n ≤ 1966080`:

- `memcpy(d,s,n)` and `memmove(d,s,n)`: require valid `d[0..n)`, readable `s[0..n)`, and separation of these ranges. Return `d`, modify only `d[0..n)`, and ensure `∀ k, 0 ≤ k < n → d[k] = old(s[k])`.
- `memset(d,b,n)`: require valid `d[0..n)`. Return `d`, modify only that range, and ensure `∀ k, 0 ≤ k < n → d[k] = (unsigned char)b`.

**60/60 WP goals proved**, including loop invariants, variants, frame conditions and generated RTE goals. See [`verification/memory.log`](verification/memory.log). These contracts deliberately restrict `memmove` to disjoint buffers; overlapping `memmove` calls have not been proved. They do not by themselves establish that all decoder calls satisfy the contracts.

**L — short literal-block model**

File: [`verification/literals_model.c`](verification/literals_model.c), function `literal_path`. This is a manually written projection, **not** the complete source or a verified translation of the Wasm.

Its exact statement uses an arbitrary byte array `memory[2097152]`. For integer offsets `src,dst`, compressed length `size`, and output capacity `capacity`, require:

```
131072 ≤ src,dst < 2097152
1 ≤ size ≤ 15
src + size ≤ 2097152
0 ≤ capacity ≤ 2097152 - dst
src + size ≤ dst OR dst + capacity ≤ src
memory[src] / 16 = size - 1
size - 1 ≤ capacity
capacity = 0 → memory[src] = 0
```

Then the function terminates, returns `r = size - 1` with `0 ≤ r ≤ capacity`, modifies only `memory[dst..dst+r)`, and ensures

```
∀ k, 0 ≤ k < r → memory[dst+k] = old(memory[src+1+k]).
```

The assertions at accesses also establish that every read belongs to the input range and every write belongs to the destination range. **73/73 WP goals proved**, including RTE goals. See [`verification/literals.log`](verification/literals.log).

The model uses integer division by 16 for the high token nibble and a forward byte copy in place of the final `memmove`; its ranges are disjoint. It omits other decoder paths. These modeling choices and their correspondence to the source require review; no machine-checked equivalence theorem is supplied.

**T — executions of the exact artifact and an instrumented copy**

File: [`verification/check_artifact.py`](verification/check_artifact.py); output: [`verification/artifact.log`](verification/artifact.log).

The script checks the artifact's size/hash, runs `wasm-tools validate`, and embeds its bytes verbatim in a Wasmtime WAST script. An adapter imports its memory/function without changing the module. A separate run uses a copy with guards around all 280 static load/store instructions, including those in memory helpers. Guards check each accessed byte: private addresses below 131072 are allowed; caller-memory reads must lie in source or destination, and caller-memory writes must lie in destination. The script rejects unrecognized memory instruction forms.

There are 3,234 cases per module, **6,468 calls total**, all passing. Cases include every single-byte input at capacities 0, 1, 14 and 64; literal and match length boundaries; extension bytes; offsets through 65535; overlapping match copies; zero offsets; truncated/malformed blocks; and deterministic random/multiple-sequence cases. Buffer orders and placements include unaligned starts and ends at the 2 MiB boundary. Caller memory is initialized to `0xa5` before source initialization. This does not quantify over all initial memories.

For each case, a separate byte-at-a-time Python parser computes the sequence decoding. Every nonnegative result must equal that decoded length, fit the capacity and match every output byte; parser-invalid input must return negative. Valid independent blocks satisfying the end conditions and capacity exception must succeed (721 cases per module). Source preservation is also checked. The instrumented run traps on a forbidden access. The parser, instrumentation and harness are trusted test code, not WP proofs. Generated WAST/Wasm files are temporary and recreated by the script.

**Reproduction**

From this directory, with the supplied offline tools:

```sh
bash verification/run.sh
```

This regenerates source models, verifies input source hashes, runs all three WP checks with caching disabled, and runs the artifact executions. It exits nonzero on a failed check. Success is exit status 0, WP summaries `60 / 60`, `31 / 31`, `73 / 73`, and:

```
Checking 3234 cases on exact artifact and instrumented copy (280 guarded instructions).
PASS: 6468 concrete calls, including 721 required-success cases per module.
```

The exact individual commands are also recorded here:

```sh
python3 verification/prepare_wp.py
frama-c --check-wp . verification/memory-annotated.c -machdep gcc_x86_32 -wp -wp-model Bytes -wp-rte -wp-prover alt-ergo -wp-timeout 30 -wp-cache none
frama-c --check-wp . verification/decoder_wp.c -machdep gcc_x86_32 -cpp-extra-args=-I./src -wp -wp-model Bytes -wp-fct LZ4_decompress_generic,LZ4_decompress_safe -wp-rte -wp-prover alt-ergo -wp-timeout 10 -wp-cache none
frama-c --check-wp . verification/literals_model.c -machdep gcc_x86_32 -wp -wp-rte -wp-split -wp-prover alt-ergo -wp-timeout 10 -wp-cache none
python3 verification/check_artifact.py
```

All WP results use Frama-C 33.0 and Alt-Ergo 2.5.4. The C model is `gcc_x86_32`; the fast decoder loop is disabled to match the Wasm target's source configuration. E and M use WP's experimental Bytes memory model; L uses Typed. WP reports globally unsupported alignment and indirect-function-call RTE guards. The verified fragments use byte accesses and direct calls. Pointer-return dependency warnings for the helpers do not suppress their checked content/frame postconditions. There are no added axioms, admitted lemmas or unchecked decoder contracts used to assert the full requirements. No Lean proof is claimed.

**Review and trust boundary, with sizes**

Sizes are lines / bytes, measured with `wc -l -c`:

| File | Size | Review purpose |
| --- | ---: | --- |
| `verification/prepare_wp.py` | 83 / 4172 | Source hashes, annotation insertion and early-exit slicing |
| `verification/memory-contracts.h` | 34 / 1350 | Exact helper preconditions and postconditions |
| `verification/decoder_wp.c` | 8 / 223 | Source configuration |
| `verification/literals_model.c` | 55 / 2160 | Restricted flat-memory decoder model and specification |
| `verification/check_artifact.py` | 254 / 12576 | Independent parser, input generation, instrumentation and execution assertions |
| `verification/run.sh` | 18 / 887 | Commands and failure propagation |
| generated `verification/memory-annotated.c` | 53 / 1742 | Helper bodies and inductive annotations |
| generated `verification/lz4-sliced.c` | 2482 / 101340 | Source slice and exact E contracts; much of this file is unused compression/API code |
| original `src/lz4.c` | 2829 / 118145 | Source-to-slice correspondence |
| original `src/lz4.h` | 884 / 46014 | Types, configuration and interface |
| original `src/c-memory.c` | 26 / 716 | Helper bodies |
| original `src/c-memory.h` | 7 / 231 | Helper declarations |
| `lz4_Block_format.md` | 244 / 10683 | Natural-language format against which the test parser/model must be reviewed |
| `README.md` | 18 / 2872 | Requirements and artifact identity |

The custom checking/model files total 452 lines / 21,368 bytes before generated C and logs. The standard trusted components are Frama-C's parser, WP, Qed and memory models, Alt-Ergo, the C preprocessor, Python, wasm-tools, Wasmtime and their execution environment. WP/SMT success is not an independently replayed Lean certificate. Artifact execution uses the exact hash above; the C proofs rely on source hashes checked by the generator. There is no proved compiler correspondence or full artifact model connecting E, M or L to all executions of those bytes.
