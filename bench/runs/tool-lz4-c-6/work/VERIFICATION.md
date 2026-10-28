# Verification results

**Status: partial verification. None of R1, R2, or R3 has been discharged in full, and no counterexample to them was found.** The completed WP results below cover entry boundary cases and the disjoint-buffer copy helper. Regression tests are listed separately and are not proofs of the general requirements.

## Requirement coverage

| Requirement | Completed result | Remaining obligation |
| --- | --- | --- |
| R1 | T0 checks the entry cases `srcSize == 0 || dstCapacity == 0`: no writes, and the only possible load is `src[0]` when `srcSize == 1`. T1/T2 independently check these cases in the C source. T3 checks the copy helper's write frame and copied content. | No general proof of the decoder's read or write bounds for arbitrary compressed bytes. In particular, C memory validity inside a 2 MiB allocation would not establish R1's narrower permitted read set. |
| R2 | T0/T2 establish successful decoding of the valid block `00` with zero output capacity, returning 0 and changing no memory. T3 establishes the disjoint copy helper used by the decoder. | No general theorem relating all valid independent LZ4 blocks to their decoded content, return length, and termination. |
| R3 | In T0's domain, success occurs exactly for `srcSize == 1`, `dstCapacity == 0`, and `src[0] == 0`. That is the empty block, with output length 0. Empty sources are rejected. | No general successful-return soundness theorem. Sequence parsing, match offsets, overlapping matches, and the permitted zero-offset interpretation remain unproved. |

The format interpretation of `00` as the empty block is the explicit empty-input case in `lz4_Block_format.md`, under “End of block conditions.” There is no machine-checked formalization of the entire format in this submission.

## Exact completed statements

All C proofs use Frama-C 33.0 WP, with 32-bit `int`, `unsigned int`, pointers, and `size_t` (`-machdep x86_32`). ACSL contracts in the cited files are the normative machine-readable statements. No Lean theorem is claimed.

### T0: artifact entry-prefix model

File: `verification/prefix.c`, function `wasm_entry_prefix`.

Let `s`, `d`, `size`, and `cap` be unsigned 32-bit integers. Assume:

- `131072 <= s,d <= 2097151`;
- `size <= 2097152-s` and `cap <= 2097152-d`;
- `cap == 0 || size == 0`;
- if `size == 1`, byte `m[s]` is readable.

Then this function terminates, writes no memory, and returns

```text
(cap == 0 && size == 1 && m[s] == 0) ? 0 : -1.
```

WP also proves the named assertion `read_in_source`, which requires `size == 1` at the model's only load, and the named assertion `unreachable_tail`, which excludes entry into the unmodeled decoder tail. The completed run reports **14/14 proved**, including termination and the unreachable cut.

This is a C model of exactly the first 27 Wasm instructions, not a formal Wasm interpreter or a theorem about the complete decoder. The connection to those instructions is described below.

### T1 and T2: C-source boundary cases

File: `verification/boundaries.c`, functions `empty_source` and `zero_capacity`. Their bodies call the shipped `LZ4_decompress_safe`; Frama-C inlines it and `LZ4_decompress_generic`.

For both statements, assume `m[0..2097152)` is a valid C byte array, `131072 <= s,d <= 2097151`, and the C allocation containing `m` is separated from the C allocations for the static `inc32table` and `dec64table` arrays. The latter is an explicit contract condition and is also printed as a WP memory-model hypothesis.

- **T1:** For every integer `cap` with `0 <= cap <= 2097152-d`, calling the decoder with source `m+s`, destination `m+d`, source size 0, and capacity `cap` terminates with return value **-1** and writes no memory.
- **T2:** For every integer `size` with `0 <= size <= 2097152-s`, calling the decoder with those pointers, source size `size`, and capacity 0 terminates with return value **`(size == 1 && m[s] == 0) ? 0 : -1`**, and writes no memory.

The completed boundary run reports **354/354 proved**.

These are C-array model results. The source proof uses the WP Bytes memory model; the array is not itself a formal model identifying the C global allocations with addresses in Wasm linear memory. T0 supplies a separate, small entry-prefix model for the actual module.

### T3: the shipped disjoint copy helper

Files: `src/c-memory.c` and its generated annotated copy `verification/memory.annotated.c`, function `memmove`.

Let `N` be the initial unsigned 32-bit `n`. Assume:

- `N <= 2097152`;
- bytes `dst[0..N)` are writable;
- bytes `src[0..N)` are readable;
- those two ranges are separated.

Then `memmove(dst,src,N)` terminates, returns `dst`, changes no memory outside `dst[0..N)`, and for every integer `k` with `0 <= k < N`, the final byte `dst[k]` equals the initial byte `src[k]`.

Both address-order branches of the actual helper are proved. The postcondition uses `\old(n)` because the backward branch modifies its local parameter `n`. The completed run reports **37/37 proved**. This theorem deliberately has a disjointness precondition; it does not prove the helper for overlapping ranges.

## Connection to the shipped artifact

The artifact remains the original **8,469-byte** `lz4-c.wasm`, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`verification/artifact.py` checks that digest, reads the compile command from `build.sh`, redirects only its output filename to `verification/rebuilt.wasm`, and compares the complete rebuilt binary against the artifact. The installed clang 23.1.4 reproduces it **byte for byte**. `wasm-tools validate` also succeeds. Neither script replaces the original artifact.

For T0, `verification/check_prefix.py` checks the digest, the memory declaration `(memory 32 32)`, the decoder export pointing to function 2, and every instruction of the entry prefix obtained with `wasm-tools print`. It writes those instructions to `verification/prefix.instructions`. A reviewer must check the small translation in `prefix.c`:

- the first two conditional branches return local 4, initialized to -1;
- the zero-capacity branch returns -1 unless the size is 1;
- its `load8_u` and `select` return -1 for a nonzero byte and 0 for a zero byte;
- the zero-size branch returns -1;
- the cut is immediately before computation of `dst+cap` and the rest of the decoder.

The instruction comparison is machine checked; **correctness of this translation is reviewed/trusted, not a machine-checked Wasm-to-C refinement proof**. The model's signed return values represent the corresponding Wasm `i32` bit patterns.

For the source results, `verification/prepare.py` copies the original sources and adds ACSL comments. It checks equality of the non-comment token sequences against the originals. The C instructions are preserved. The proof harness disables `LZ4_FAST_DEC_LOOP`, as does the Wasm target used by the shipped build. The helper proof uses the shipped loop bodies, including integer address comparison.

A byte-identical rebuild establishes provenance, not compiler correctness. Transferring source theorems through compilation still trusts clang/linker semantics and Frama-C's C model. There is no proof of the complete compilation or binary refinement.

## Checks to run

From this directory:

```sh
bash verification/check.sh
```

This regenerates annotations, verifies the artifact and its prefix, runs every completed WP proof with `frama-c --check-wp`, and executes the exact-artifact regression tests. It uses no network and disables WP proof-result caches (`-wp-cache none`). Exit status 0 and the final message

```text
Completed checks passed. General R1, R2 and R3 remain unproved.
```

mean that the **limited results in this report** pass. The script is not a checker for full compliance with R1–R3. Every WP invocation must report all its goals proved; an open WP goal makes the script fail.

The exact constituent commands, including selected proof functions and memory models, are in the 18-line `verification/check.sh`. It does not select the unfinished decoder proof described below.

WP prints generic warnings about skipped alignment and indirect-function-call RTE guards. T0 and T3 access byte elements and make no indirect calls. The boundary cases do not reach the decoder's wider accesses. Source runs also print memory-model separation hypotheses, missing annotations on unreachable loops/helpers, and missing dependency (`assigns ... \from ...`) specifications. These warnings are not a proof of the general decoder's memory behavior; all goals selected for the completed boundary and helper results must still pass.

### Exact-artifact regression tests

`verification/replay.py` embeds the exact original binary in a generated WAST module and runs it with `wasmtime wast -C cache=n`. It checks **124 decoder invocations**, in two address arrangements, including sources ending at the memory limit. Cases include:

- literal lengths 0–16, 269–271, and 525–526, and undersized destinations;
- matches with offsets 0 and 1, including overlapping and extended matches;
- empty sources, zero capacity, ignored low token bits on a final empty sequence;
- an offset before the beginning of output and truncated input fields.

Each invocation checks its expected return (or negativity for selected errors), expected decoded bytes on success, and one guard byte on each side of the destination. These tests neither observe every read nor establish that all other memory bytes are unchanged. They are not an exhaustive search and do not discharge any universal requirement.

## Unfinished work

`verification/literals.c` contains proposed contracts for short literal blocks and for successful-return soundness with small output capacities. They are retained as **unfinished proof attempts**, not proved theorems. To reproduce the attempt after `prepare.py`:

```sh
frama-c --check-wp . verification/literals.c -cpp-extra-args=-Isrc \
  -machdep x86_32 -inline-calls LZ4_decompress_safe,LZ4_decompress_generic \
  -wp -wp-model Bytes -wp-fct literal_block,small_output \
  -wp-rte -wp-timeout 10 -wp-par 8
```

The last restricted attempt reported **372/380 proved**, with eight timeout goals, including output postconditions, frame conditions, and unreachable-call preconditions. The transcript is `verification/literals-final-wp.log`. These restricted proof attempts do not cover general blocks, even if their remaining goals are subsequently discharged. Their decoder annotations assert that no match is reached, and use false preconditions for helper calls intended to be unreachable in that restricted domain. Such a precondition is **not permission to assume a decoder property**: WP must prove every call unreachable. Any unproved call precondition invalidates the attempted result. Likewise the assertion at `_copy_match` must be proved. There are no added axioms or `assume` annotations.

Full verification would additionally require invariants relating the input cursor, literal and extended lengths, decoded output prefix, offset checks, speculative copies, and overlapping match copies to a formal definition of the block format. None of that general refinement has been established here. Timeouts/open goals in an attempted proof are not demonstrations that the software violates a requirement.

## Review and trust inventory

The sizes below count physical lines and bytes. Generated sources contain copies of the shipped code plus annotations; their generation, rather than an independently edited copy, is part of the check.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `README.md` | 18 | 2872 | Requirements |
| `CHECK.md` | 8 | 784 | Delivery instructions |
| `lz4_Block_format.md` | 244 | 10683 | Format and empty-block interpretation |
| `build.sh` | 10 | 635 | Reproduction command |
| `src/lz4.c` | 2829 | 118145 | Shipped decoder source |
| `src/lz4.h` | 884 | 46014 | Shipped declarations/configuration |
| `src/c-memory.c` | 26 | 716 | Shipped copy helper source |
| `src/c-memory.h` | 7 | 231 | Helper declarations |
| `verification/prefix.c` | 32 | 1149 | Reviewed Wasm-prefix model and T0 contract |
| `verification/boundaries.c` | 38 | 1292 | T1/T2 harness and contracts |
| `verification/literals.c` | 49 | 1785 | Unfinished restricted decoder contracts |
| `verification/prepare.py` | 79 | 4763 | Annotation generator and token comparison |
| `verification/check_prefix.py` | 48 | 1446 | Exact prefix comparison |
| `verification/artifact.py` | 21 | 961 | Exact artifact hash/rebuild/validation |
| `verification/replay.py` | 82 | 3725 | Test generation and expected examples |
| `verification/check.sh` | 18 | 898 | Completed-results checker |
| `verification/lz4.annotated.c` | 2840 | 118696 | Generated decoder and restricted annotations |
| `verification/memory.annotated.c` | 58 | 2614 | Generated helper, invariants, and T3 contract |
| `verification/prefix.instructions` | 27 | 260 | Generated prefix listing to review |

The original and rebuilt Wasm binaries are each 8,469 bytes. The generated `replay.wast` is test output; its generator and expected examples, rather than all of the expanded WAST, are the review input. `verification/final-checks.log` is the final successful transcript; logs and WP caches are not proof premises or certificates.

Also trusted are Frama-C 33.0 (parser, inlining, RTE, WP, Qed, Bytes/Typed memory models and installed C headers), Alt-Ergo 2.5.4, the supplied `--check-wp` wrapper, Python, Bash, clang/linker for the source-to-artifact connection, and wasm-tools 1.262.0 / Wasmtime 50.0.0 for binary decoding and execution. These installed toolchains are external dependencies, not locally supplied proof-source files. WP/SMT results are not independently checked Lean proof terms. In particular, the prefix model and its relationship to Wasm semantics must be reviewed; a passing instruction comparison alone cannot prove a translation correct.
