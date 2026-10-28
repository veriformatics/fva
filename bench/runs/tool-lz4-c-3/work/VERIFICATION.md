This is a **partial verification**, not a proof of all the README requirements. No counterexample was found. The general cases of R1, R2, and R3 remain unproved.

The artifact checked is the 8,469-byte `lz4-c.wasm`, SHA-256
`8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`.
The original software and requirements were not modified.

**Requirement coverage**

| Requirement | Machine-checked result | Remaining gap |
| --- | --- | --- |
| R1 | For the extracted source entry cases `dstCapacity = 0` or `srcSize = 0`, execution terminates without writes. The only possible caller-byte read is `src[0]`, when capacity is zero and source size is one. See the entry contracts and accessor proof below. All accesses were also monitored in 349,083 finite artifact executions. | No universal buffer-access proof for calls with both sizes positive. The loop invariants and access premises needed for all literal, match, and speculative-copy paths were not established. |
| R2 | The specific valid block `00`, with `srcSize = 1` and `dstCapacity = 0`, returns zero and leaves memory unchanged in the entry model. This is the format's empty content. Finite artifact checks exercised 25,949 calls satisfying the executable reference parser's R2 antecedent. | No general theorem about valid independent blocks, including empty blocks with positive capacity. There is no proved refinement from the complete decoder to the format's sequence and overlapping-match semantics. |
| R3 | With zero capacity, nonnegative return occurs exactly for the one-byte block `00`, with result zero and empty decoded content. Empty source always returns negative. In finite artifact checks, all 25,982 nonnegative returns satisfied the executable relaxed parser and output comparison. | No universal theorem for successful calls with positive capacity and nonempty source. The parser used in testing is not itself formally verified against the format document. |

The source-to-artifact connection below requires trusting the compiler and extraction. None of these source results is a machine-checked theorem in a formal WebAssembly semantics.

**Exact source proof statements**

Let `M = 2097152`. The mutable array `memory` in [verification/entry.c](verification/entry.c) represents the entire linear memory; its initial bytes are arbitrary. The exact statements are the ACSL contracts in that file:

1. `verify_zero_capacity(src, dst, size)`: assuming `131072 <= src < M`, `131072 <= dst < M`, and `0 <= size <= M-src`, the function terminates, has no abnormal exit, changes no memory, and returns
   `((size == 1 && memory[src] == 0) ? 0 : -1)`.
2. `verify_empty_source(src, dst, cap)`: assuming the same address bounds and `0 <= cap <= M-dst`, the function terminates, has no abnormal exit, changes no memory, and returns `-1`.

These wrappers call the original exported function body, extracted into [verification/entry_prefix.c](verification/entry_prefix.c). Its generic decoder contract additionally fixes full decoding, no dictionary, `lowPrefix = dst`, null dictionary start, and dictionary size zero. It requires nonnull pointers, sizes in `[0,M]`, `outputSize = 0 || srcSize = 0`, readable source offsets `[-32,srcSize-1]`, and writable destination offsets `[-32,outputSize-1]`. It proves termination, no abnormal exit, no writes, and result
`((outputSize == 0 && srcSize == 1 && *(const BYTE*)src == 0) ? 0 : -1)`.
The extra 32-byte headroom permits the original shortcut-pointer calculations; it exists inside the flat memory for every README caller address.

The prefix's single byte dereference is replaced by a call to `entry_read`. Its checked contract requires `count == 1`, `p == begin`, and `\valid_read(p)`; it terminates, changes nothing, has no abnormal exit, and returns `*p`. Thus the call-precondition obligations establish the source-buffer bound at that read. The accessor body contains exactly that one byte read. The `assigns` clauses alone would not prove a read footprint: the read result also depends on reviewing the extractor and prefix to confirm that they cover every caller-byte read.

The omitted decoder suffix is replaced by `omitted_decoder_tail`, whose precondition is **false** and whose termination is not assumed. WP proves its call unreachable. The suffix's correctness is not assumed. Consequently these proofs provide no information about calls that enter that suffix.

There are also supporting contracts in [verification/memory.c](verification/memory.c), generated from the shipped `src/c-memory.c`:

- `proof_memcpy(dst, src, n)` and `proof_memmove(dst, src, n)`: for `size_t n <= M`, valid destination bytes `[0,n)`, readable source bytes `[0,n)`, and disjoint ranges, terminate without abnormal exit, return `dst`, modify only destination bytes `[0,n)`, and establish `dst[k] = old(src[k])` for every integer `0 <= k < old(n)`.
- `proof_memset(dst, byte, n)`: for `size_t n <= M` and valid destination bytes `[0,n)`, terminates without abnormal exit, returns `dst`, modifies only those bytes, and establishes `dst[k] = (unsigned char)byte` for every integer `0 <= k < old(n)`.

The copy contracts deliberately cover disjoint ranges. They do not prove general overlapping `memmove`, or prove that every decoder call satisfies these preconditions. All loop invariants, assertions, frame conditions, termination obligations, and generated runtime-error obligations in the selected proof scopes are checked; no proof uses an `admit`, an unchecked invariant, or an assumed decoding-correctness axiom.

**Connection to the shipped bytes**

[verification/inputs.sha256](verification/inputs.sha256) binds the original README, CHECK, format document, build script, artifact, and all four C source/header files. [verification/artifact.py](verification/artifact.py) checks the artifact's exact size/hash, validates it with `wasm-tools`, and runs the original `build.sh` in a temporary directory. With the installed Clang 23.1.4, the rebuilt module equals the shipped bytes byte for byte. This checks build correspondence; it is not a proof that compilation preserves C semantics.

[verification/prepare.py](verification/prepare.py) hash-checks its source inputs. For the memory proofs, it inserts ACSL annotations and macro-renames the three functions; a token comparison checks that removing annotations and renaming recovers the shipped C body. It generates the declaration contracts from the same strings as the definition contracts.

For the entry proofs, the script copies the generic decoder prefix through its `srcSize == 0` case and the original `LZ4_decompress_safe` body. It copies the relevant enums and constant, supplies the byte type and disabled-debug macros, substitutes the proved pure accessor for the single `*ip` read, and guards the omitted suffix with the false precondition. Trusting this extraction and the accessor substitution is necessary to transfer the model's results to the source. `x86_32` supplies Frama-C's 32-bit integers, pointers, and `size_t`; the relevant byte operations and entry control flow agree with the Wasm build. No claim is made about the complete C library under this proof configuration.

**Finite execution evidence**

[verification/artifact.py](verification/artifact.py) also generates `verification/monitored.wasm`. It replaces the artifact's load/store instructions with wrappers that check every accessed byte: addresses at least 131072 must be inside source or destination for reads, and inside destination for writes. Original function/global indices are retained; monitor functions and globals are appended. Monitor state does not occupy linear memory.

[verification/runtime.mjs](verification/runtime.mjs) executes the original and monitored modules, compares their return values and destination bytes, and compares successful output with an independent executable parser. Strict parsing supplies R2 test antecedents; relaxed parsing allows R3's end-condition and zero-offset exceptions. Cases include all one- and two-byte strings at capacities 0, 1, 11, 32, and 64; empty input; literal-length boundaries; offsets 0 through 9 and selected larger offsets through 65535; extended and overlapping matches; generated valid blocks; mutations; and random byte strings. Placements exercise both buffer orders and the ends of caller memory. Destination bytes initially contain `a5`.

The observed result was:

```text
Finite artifact checks: PASS (349083 calls; 25949 R2 antecedents; 25982 nonnegative returns)
Every tested decoder access was monitored; this is not an exhaustive proof of R1, R2, or R3.
```

This is finite evidence, not a theorem about all inputs, placements, capacities, initial memories, or histories of calls. Its interpretation also requires trusting the instrumentation and reference parser.

**Reproduction**

From this directory, run:

```sh
bash verification/check.sh
```

The script contains the exact component commands. It checks input hashes, regenerates proof inputs, runs Frama-C 33.0 WP with runtime-error checks and Alt-Ergo 2.5.4, checks artifact identity/rebuilding, and runs the finite execution checks. It uses `--check-wp` and disables the WP cache; any unproved reported goal or failed execution assertion makes it exit unsuccessfully. The finite checks use Node 26.12.1, `wasm-tools` 1.262.0, Python 3, and Bash; rebuilding uses Clang 23.1.4 and its linker. These are installed in the supplied environment. No network or Lean proof is required.

Success requires both WP invocations to report every goal proved, artifact identity/rebuild `PASS`, the finite result above, and script exit status zero. The checked entry proof has 58/58 goals and the memory proof has 69/69 goals. Counts can vary with tool versions; a timeout is not success. Recorded logs are in [verification/results](verification/results), but rerunning the commands is the check.

WP warns that alignment and function-pointer-call guards are unsupported. The proved entry paths and memory routines access bytes and make no indirect calls. The omitted tail has no implementation/assigns contract because its call must be unreachable. Diagnostic warnings about pointer-result dependency clauses do not supply correctness assumptions; return values are proved by postconditions.

**Review and trust**

In addition to Frama-C/WP's Bytes memory model, RTE, its preprocessor and machine description, Why3/Alt-Ergo, and their host runtime, review the following files. The artifact connection additionally trusts Clang/the linker and SHA-256; the finite evidence additionally trusts Python, `wasm-tools`, Node's WebAssembly engine, the monitor, and the parser. The format-to-contract interpretation for the proved empty block is the format document's explicit representation of empty input. General format correctness was not formalized.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| [README.md](README.md) | 18 | 2872 | Requirements |
| [CHECK.md](CHECK.md) | 8 | 784 | Delivery instructions |
| [lz4_Block_format.md](lz4_Block_format.md) | 244 | 10683 | Format, especially empty content |
| [build.sh](build.sh) | 10 | 635 | Build correspondence |
| [src/lz4.c](src/lz4.c) | 2829 | 118145 | Original decoder; prefix/export and macro context for these proofs |
| [src/lz4.h](src/lz4.h) | 884 | 46014 | Original declarations and configuration |
| [src/c-memory.c](src/c-memory.c) | 26 | 716 | Original copy/fill bodies |
| [src/c-memory.h](src/c-memory.h) | 7 | 231 | Original declarations |
| [verification/inputs.sha256](verification/inputs.sha256) | 9 | 703 | Input identity manifest |
| [verification/prepare.py](verification/prepare.py) | 180 | 7611 | Extraction, annotations, token comparison, generation |
| [verification/entry.c](verification/entry.c) | 30 | 956 | Entry-case contracts and flat-memory model |
| [verification/entry_prefix.c](verification/entry_prefix.c) | 102 | 3561 | Generated prefix, accessor and unreachable-tail contracts |
| [verification/memory.c](verification/memory.c) | 99 | 3807 | Generated primitive contracts and invariants |
| [verification/memory.h](verification/memory.h) | 37 | 1499 | Generated convenience declarations; unused by checked scopes |
| [verification/artifact.py](verification/artifact.py) | 86 | 3613 | Identity, rebuilding and access instrumentation |
| [verification/runtime.mjs](verification/runtime.mjs) | 130 | 6132 | Finite cases and executable reference parser |
| [verification/check.sh](verification/check.sh) | 18 | 968 | Reproduction and failure propagation |

Generated C files must be regenerated before checking; their generators and exact source slices are part of the review. Logs and generated Wasm are evidence/output, not additional axioms or proof certificates. There is no machine-checked compiler, source-extraction, or complete decoder-to-format refinement theorem in this deliverable.
