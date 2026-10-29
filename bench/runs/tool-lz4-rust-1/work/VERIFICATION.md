**Status: partial verification. Universal R1, R2, and R3 for the shipped WebAssembly artifact remain unproved. No failing input was found.** The results below comprise Verus proofs about an explicit reference model, general lemmas relevant to the optimized copies, and finite checks against the exact artifact. They do not certify that the shipped artifact meets every requirement.

The artifact checked is [lz4-flex.wasm](lz4-flex.wasm), 7,161 bytes, SHA-256
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.
The checking script refuses a different length or digest. The artifact and shipped source were not changed.

| Requirement | Proved or checked | Remaining gap for the shipped artifact |
| --- | --- | --- |
| R1 | Verus checks every input/output index and arithmetic operation in the reference decoder, under its stated bounds. The copy contracts and optimization lemmas below hold for all their arguments. Instrumented execution of all 2,762 cases checks every executed load, store, bulk copy, and fill in the Wasm module. | No invariant proof establishes the permitted address ranges for every reachable Wasm instruction on every admissible input. Finite instrumentation checks are insufficient for this universal claim. |
| R2 | `model_complete` proves completeness and exact output for the reference semantics whenever the decoded output fits. Original-artifact executions agree byte-for-byte with the verified model on all successful cases in the finite corpus. | There is no proved refinement from Wasm function 7 to `model_decompress`, including all its optimized branches. The relation between the mathematical format definition and the supplied English format specification is reviewed, not mechanically proved. |
| R3 | `model_decompress` proves soundness, output length at most capacity, and complete parsing according to `decode` for every successful model return. All 2,762 original-artifact cases have the same return and successful output as the model. | No proved refinement transfers that result to all successful Wasm executions, including all malformed inputs. |

All proof code is in [verification/model.rs](verification/model.rs). The definitions `extension`, `length`, `grow`, and `decode` interpret the supplied format: high token nibble for literals; mandatory terminating extension byte when a nibble is 15; little-endian two-byte offsets; nonzero offsets at most the current decoded length; minimum match length four; and sequential, potentially overlapping match copies. `decode` consumes every compressed byte and requires a final literal-only sequence. It deliberately permits violations of the additional final-five-literals and last-match-distance conditions, as R3 allows. Its relaxed language includes valid independent blocks. There is no external dictionary.

`decode(s, 0, Seq::empty()) == Some(expected)` is the formal format/content premise used here. It is not a reference to the shipped binary. In particular, the model has no formal predicate separately encoding all the end-of-block restrictions from the English specification. `grow(pre, off, count)` defines a match by repeated one-byte appends from the output at the specified offset. `blit` models a copy from a snapshot of the source, as with memmove. Review those definitions to judge the scope of the statements below.

The executable reference decoder follows the general path of `decompress_safe.rs`, using checked vector accesses and byte-at-a-time copies. It is a separately written program: it does not include or verify the vendored Rust crate, the shim's raw pointers, or the compiled Wasm instructions. It uses native `usize` under the installed x86_64 toolchain. The bounds use 2,097,152 bytes independently for input and output, a superset of the lengths possible under the README's placement restrictions. `length_arithmetic` addresses 32-bit length calculations, but is not an equivalence proof between native and Wasm arithmetic. The recursive sequence decoder also has no verified native stack-resource bound; its logical termination is checked, and the supplied executions complete.

The following are the exact primary contracts checked by Verus; function bodies are omitted here and present in the linked file. `input@` denotes the byte sequence of a vector, `old(output)` its entry value, and `final(output)` its exit value. `Some(r)` models success; `None` models the shim's error result -1.

For R1, the checked literal and match loops have these contracts. Verus additionally checks the safety of every vector index and machine arithmetic operation in their bodies, and at every call from `decode_from`:

```rust
pub fn copy_literals(input: &Vec<u8>, output: &mut Vec<u8>, q: usize, pos: usize, n: usize)
    requires q + n <= input.len(), pos + n <= old(output).len(),
    ensures final(output).len() == old(output).len(),
        final(output)@.subrange(0, (pos + n) as int)
            == old(output)@.subrange(0, pos as int) + input@.subrange(q as int, (q + n) as int),
```

```rust
pub fn copy_match(output: &mut Vec<u8>, pos: usize, off: usize, n: usize)
    requires 1 <= off <= pos, pos + n <= old(output).len(),
    ensures final(output).len() == old(output).len(),
        final(output)@.subrange(0, (pos + n) as int)
            == grow(old(output)@.subrange(0, pos as int), off as int, n as nat),
```

The following general optimization obligations are proved. They establish implications under the written premises; no theorem establishes that every corresponding Wasm path satisfies those premises.

```rust
pub proof fn hot_loop_bounds(n: int, cap: int, ip: int, pos: int, literals: int, ml: int)
    requires 0 <= n <= 2097152, 0 <= cap <= 2097152,
        1 <= ip <= if n >= 18 { n - 18 } else { 0 },
        0 <= pos < if cap >= 34 { cap - 34 } else { 0 },
        0 <= literals <= 14, 4 <= ml <= 18,
    ensures ip + 16 <= n, ip + literals + 2 <= n,
        pos + 16 <= cap, pos + literals + 18 <= cap,
        pos + literals + ml <= cap,
```

```rust
pub proof fn wild_match_bounds(pos: int, off: int, w: int, ml: int, cap: int)
    requires 1 <= off <= pos, 0 <= ml <= w, ml <= off,
        0 <= pos, pos + w <= cap,
    ensures 0 <= pos - off, pos - off + w <= cap,
        pos + ml <= cap,
```

```rust
pub proof fn length_arithmetic(n: int, pos: int, count: int)
    requires 0 <= n <= 2097152, 0 <= pos <= 2097152,
        0 <= count <= 19 + 255 * n,
    ensures count < 4294967296int, pos + count < 4294967296int,
```

```rust
pub proof fn wild_literals(before: Seq<u8>, source: Seq<u8>, pos: int, ll: int)
    requires 0 <= pos, pos + source.len() <= before.len(), 0 <= ll <= source.len(),
    ensures blit(before, pos, source).len() == before.len(),
        blit(before, pos, source).subrange(0, pos + ll)
            == before.subrange(0, pos) + source.subrange(0, ll),
        forall |k: int| 0 <= k < before.len() && (k < pos || k >= pos + source.len())
            ==> #[trigger] blit(before, pos, source)[k] == before[k],
```

```rust
pub proof fn wild_match(before: Seq<u8>, pos: int, off: int, w: int, ml: nat)
    requires 1 <= off <= pos, pos + w <= before.len(), ml <= w, ml <= off,
    ensures blit(before, pos, before.subrange(pos - off, pos - off + w)).len() == before.len(),
        blit(before, pos, before.subrange(pos - off, pos - off + w)).subrange(0, pos + ml)
            == grow(before.subrange(0, pos), off, ml),
```

For R2, completeness of the reference decoder is the following contract. It imposes no premise on the initial destination contents and applies to every block accepted by the relaxed format semantics, including valid independent blocks:

```rust
pub fn model_complete(input: &Vec<u8>, output: &mut Vec<u8>, Ghost(expected): Ghost<Seq<u8>>)
    -> (r: usize)
    requires input.len() <= 2097152, old(output).len() <= 2097152,
        decode(input@, 0, Seq::empty()) == Some(expected),
        expected.len() <= old(output).len(),
    ensures r == expected.len(), final(output).len() == old(output).len(),
        final(output)@.subrange(0, r as int) == expected,
```

For R3, and also the reference model's capacity/error behavior, the exact contract is:

```rust
pub fn model_decompress(input: &Vec<u8>, output: &mut Vec<u8>) -> (res: Option<usize>)
    requires input.len() <= 2097152, old(output).len() <= 2097152,
    ensures final(output).len() == old(output).len(),
        match res {
            Some(r) => r <= final(output).len()
                && decode(input@, 0, Seq::empty()) == Some(final(output)@.subrange(0, r as int)),
            None => match decode(input@, 0, Seq::empty()) {
                None => true,
                Some(out) => out.len() > final(output).len(),
            },
        },
```

Consequently a successful model return specifies an output sequence of length `r <= cap` whose parse has only independent matches with valid nonzero offsets, by the definition of `decode`. A fitting `Some(expected)` parse cannot produce `None`. This is a theorem about the model's definitions and code, with the artifact refinement gap stated above.

The following checked examples make the formal premises concrete. The second input is a valid independent block with eight `A` bytes followed by `BCDEF`: its last match begins exactly 12 decoded bytes before the end. The last two examples respectively reject offset zero and an offset larger than the available decoded prefix.

```rust
pub proof fn format_examples()
    ensures
        decode(seq![0u8], 0, Seq::empty()) == Some(Seq::<u8>::empty()),
        decode(seq![0x13u8, 65, 1, 0, 0x50, 66, 67, 68, 69, 70], 0, Seq::empty())
            == Some(seq![65u8, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]),
        decode(seq![0x10u8, 65, 0, 0, 0], 0, Seq::empty()) == None,
        decode(seq![0x10u8, 65, 2, 0, 0], 0, Seq::empty()) == None,
```

The finite artifact result is established by [verification/check_artifact.py](verification/check_artifact.py). Precisely, for each tuple `(label, data, cap, src, dst, expected)` returned by its deterministic `cases()` function:

- the script checks the README's placement and non-overlap conditions;
- a freshly verified and compiled `model_decompress` computes a result, compared byte-for-byte against the Python format interpreter;
- a Wasmtime WAST assertion calls the original binary's exported `lz4_decompress(src, dst, len(data), cap)` and checks the exact expected result (-1 or output length);
- on success every output byte is compared with the model's bytes, using a separate oracle memory;
- every source byte and the explicitly initialized guards outside the two buffers are checked after the call;
- the same checks run on a second module that instruments every original memory operation, trapping on any observed caller-region access outside the R1 ranges.

There are **2,762 cases**, hence 2,762 original calls and 2,762 instrumented calls. These include all 256 final token values at two capacities, extended literal lengths, offsets 1 through 64, overlapping and non-overlapping matches around the 18/32/64-byte copy boundaries, multiple sequences, insufficient capacity, truncations, mutations, arbitrary bytes from a fixed random seed, zero offsets, excessive offsets, long unterminated extensions, both address orderings, adjacent buffers, and maximum admissible input and destination extents. Coverage is finite; it is not an exhaustive enumeration of the README's domain. Source/output buffers are initialized for each case, but all possible initial memory states are not enumerated. Error-path output contents have no specified value and are not compared.

The instrumenter starts from `wasm-tools print` of the hash-checked artifact, preserves original function indices and numeric local indices, and adds checks without replacing the original loads/stores. It handles 104 load instructions, 107 store instructions, five `memory.copy` instructions, and three `memory.fill` instructions across the module; it refuses unrecognized memory operations and unexpected counts. Checks use unsigned 64-bit effective addresses, include instruction offsets and full access widths, and restrict the intersection with `[131072, 2097152)`. Reads must lie in source or destination; writes must lie in destination. A zero-width access is permitted. The read checker conservatively requires an individual access to fit one buffer; this is sufficient for the passing cases. Its helpers have no memory accesses. The transformation and checker are not formally verified, so their correctness must be reviewed for the dynamic R1 evidence. Wasm validation by itself does not prove R1.

As a concrete original-binary result, source bytes `13 41 01 00 50 42 43 44 45 46`, `src=131088`, `dst=1048592`, `n=10`, `cap=13`, return 13 and produce `41 41 41 41 41 41 41 41 42 43 44 45 46`. This is a passing example, not a counterexample. No requirement is reported as false.

To replay every result, run these exact commands from this directory, without network access:

```sh
verus --no-cheating verification/model.rs
python3 -I verification/check_artifact.py
```

The first command must exit 0 and print:

```text
verification results:: 24 verified, 0 errors
```

The second command checks the artifact digest, runs `wasm-tools validate`, invokes `verus --no-cheating --compile verification/model.rs -o TEMP/model-oracle`, executes the compiled model, generates and validates the instrumented module, and runs both generated WAST scripts with `wasmtime wast -C cache=n`. Caching is disabled so no writes to a user cache are required. Temporary binaries and WAST files are created under the configured temporary directory and removed. A successful run exits 0 and prints:

```text
artifact: 7161 bytes, sha256 1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
verification results:: 24 verified, 0 errors
PASS: Python format oracle agrees byte-for-byte with compiled Verus model
checking 2762 cases on original Wasm...
PASS: all returns, successful output bytes, source bytes, and guards match
checking 2762 cases on instrumented Wasm...
PASS: all returns, successful output bytes, source bytes, and guards match
PASS: every instrumented high-memory access stayed within the R1 buffers in these executions
These finite execution checks do not prove universal R1, R2, or R3.
```

Any nonzero exit, assertion failure, unexpected trap, or changed digest fails the corresponding check. Python assertions must remain enabled; the script rejects `-O`, and `-I` ignores Python environment overrides. `--no-cheating` rejects admitted assertions, `assume`, `assume_specification`, and external proof bodies. The unreachable `assert(false)` in `model_complete` is a checked logical consequence, not an assumption. No Lean or Mathlib proof is used.

Review/trust sizes below count physical lines and bytes, including comments and blank lines. These counts can be reproduced with `wc -l -c`.

| Component | Lines | Bytes | Role and trust |
| --- | ---: | ---: | --- |
| `verification/model.rs` | 460 | 18,459 | All definitions, checked implementation, proofs, and the I/O adapter. Review the specification definitions for fidelity to the intended format. Proof bodies and implementation are checked by Verus. |
| `verification/model.rs`, lines 428–460 | 33 | 1,331 | Unverified native I/O adapter. It checks length bounds before calling the verified decoder and frames the executable oracle's input/output. Its framing, calls, allocation, and standard I/O are trusted for execution evidence. |
| `verification/check_artifact.py` | 379 | 16,768 | Entire corpus generator, Python oracle, Verus/Wasmtime orchestration, WAST harness, memory instrumentation, hash checking, and assertions. This script is unverified and must be reviewed for the finite execution claims. Agreement with the verified model reduces reliance on its independent Python decoding logic. |
| `README.md` | 18 | 2,402 | Requirement and artifact identity being assessed. |
| `CHECK.md` | 8 | 784 | Required report contents. |
| `lz4_Block_format.md` | 244 | 10,683 | English format specification; mathematical-definition correspondence requires review. |
| `lz4-flex.wasm` | binary | 7,161 | Exact subject of the finite artifact checks. |
| `shim/src/lib.rs` | 34 | 1,167 | Source interface context; no source-to-artifact equivalence proof. |
| `shim/vendor/lz4_flex/src/block/decompress_safe.rs` | 495 | 18,526 | Source algorithm used to guide the reference implementation; not verified in place. |
| `shim/vendor/lz4_flex/src/sink.rs` | 346 | 10,339 | Source copy operations motivating the general wild-copy lemmas; not verified in place. |
| `shim/vendor/lz4_flex/src/fastcpy.rs` | 145 | 4,062 | Source copy optimizations; not verified in place. |

The source context files are useful for comparison, but trusting a Rust-to-Wasm compilation claim is unnecessary for the finite checks: those directly load the identified Wasm bytes. Conversely, reading those files and the model is not a substitute for the missing refinement proof. `build.sh` is not run; no reproducible-build or Rust-compiler-correctness result for the shipped artifact is asserted.

The external proof trusted base includes Verus release `0.2026.10.18.7d82994`, its Rust frontend/encoding, the built-in logic, Z3, and the supplied `vstd` specifications for sequences, vectors, arithmetic, and mutable references. Installed component sizes are: Verus launcher 4,685,616 bytes; `rust_verify` 25,483,272; Z3 34,954,456; `vstd.vir` 30,838,617; and `libvstd.rlib` 9,864,436. The PATH `verus` shell wrapper is 261 bytes. These sizes describe installed components, not an audit of their source or all transitive libraries.

The execution evidence additionally trusts the native Rust compiler/standard library for the oracle (toolchain `1.99.1-x86_64-unknown-linux-gnu`), Python 3.14 and its standard library, SHA-256, `wasm-tools 1.262.0` (20,431,992-byte executable), and Wasmtime `50.0.0` (67,968,088-byte executable), including its Wasm parser and compiler/runtime. It assumes their normal operation and the host's execution of these programs. Their transitive libraries and operating system are not audited or size-inventoried here. The supplied Lean 4.35/Mathlib installation is outside the proof dependency chain.
