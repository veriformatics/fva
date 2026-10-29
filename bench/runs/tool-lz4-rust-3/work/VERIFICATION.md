# Verification report

**Partial verification. R1, R2, and R3 remain unproved for the shipped artifact.**
No counterexample was found. There are 26 Verus-checked proofs about an independent
mathematical reference decoder and relevant arithmetic, plus 750 successful
executions of the original artifact. Neither establishes the missing universal
correspondence between that decoder and the optimized WebAssembly. This report
does not certify the software as meeting its requirements.

## Artifact identity and connection

The artifact tested is the unchanged `lz4-flex.wasm`, exactly 7,161 bytes, with
SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

`verification/check_artifact.py` rejects any different size or digest. Its harness
imports the memory and `lz4_decompress` function from this module using Wasmtime's
`--preload`; it neither recompiles the Rust nor rewrites the artifact. The input
and destination buffers satisfy the README's location and nonoverlap conditions.

`verification/format.rs` is **a separately written mathematical model**, not
verified shipped Rust, an extraction from the WASM, or a verified WASM interpreter.
All its parsing and decoding functions are Verus `spec fn`s. It does not execute
the artifact. Its integers and sequences are mathematical values; it omits
machine-level control flow, memory, traps, and the implementation's widened
copies. The source was inspected to identify relevant arithmetic obligations,
but inspection is not a machine-checked correspondence proof. No Rust compiler
correctness or reproducible-build argument is being substituted for that proof.

## R1: accesses confined to the supplied buffers

**Artifact status: unproved; no demonstrated failure.** In particular, Rust slice
safety and WebAssembly linear-memory safety would not alone imply the narrower
per-buffer requirement in R1.

The following exact universally quantified statements are proved in
`verification/format.rs`. Names below designate Verus proof functions; their
full declarations and bodies are in that file. `requires` is the hypothesis and
`ensures` the conclusion. These are arithmetic facts, not assertions that every
WASM access satisfies their hypotheses.

```rust
length_accumulator_fits(consumed: int, base: int)
    requires 0 <= consumed <= 2097152 - 131072, 0 <= base <= 19
    ensures 0 <= 255 * consumed + base < 4294967296

widened_copy_bounds(cap: int, pos: int, off: int, width: int)
    requires 0 <= pos, 1 <= off <= pos, 0 <= width, pos + width <= cap
    ensures 0 <= pos - off, pos - off + width <= cap,
            0 <= pos, pos + width <= cap

fast_path_bounds(n: int, cap: int, ip: int, op: int, literals: int)
    requires 0 <= ip, ip + 1 <= n - 18,
             0 <= op, op < cap - 34, 0 <= literals <= 14
    ensures ip + 1 + 16 <= n,
            ip + 1 + literals + 2 <= n,
            op + 16 <= cap,
            op + literals + 18 <= cap

placed_access(base: int, len: int, index: int, width: int)
    requires 131072 <= base, 0 <= len, base + len <= 2097152,
             0 <= index, 0 <= width, index + width <= len
    ensures 131072 <= base + index,
            base + index + width <= 2097152,
            base + index + width < 4294967296

successful_sequence_access_bounds(s: Seq<u8>, ip: int,
                                  produced: int, cap: int, x: Piece)
    requires sequence(s, ip, produced, x), produced <= cap,
             produced + x.literals + x.matches <= cap
    ensures 0 <= ip < s.len(),
            ip + 1 <= x.lit <= x.lit + x.literals <= s.len(),
            produced <= produced + x.literals <= cap,
            !x.last ==> x.lit + x.literals + 2 <= x.next <= s.len(),
            forall|i: int| 0 <= i < x.matches ==>
                0 <= match_source(produced, x, i)
                   < produced + x.literals + i < cap
```

Here `match_source(produced, x, i) = produced + x.literals + i - x.offset`.
The last theorem concerns successful grammar sequences and their logical copies;
it does not cover implementation error paths or widened accesses. SMT trigger
annotations, which do not change the propositions, are omitted in this display.

The artifact tests check that **final** memory outside `dst[0..cap)` equals its
initial value, including the source. They do not observe reads or transient
writes. Consequently, even the finite tests are not complete checks of R1.

What remains: an instruction-level access proof covering every path, including
malformed inputs, bounds failures, panic helpers, all widened loads/stores, and
bulk-memory operations. No such binary-level proof is supplied.

## R2: valid independent blocks decode correctly

**Artifact status: unproved; no demonstrated failure.** The following exact
model-level completeness theorem is checked in `verification/format.rs`:

```rust
pub proof fn model_r2(s: Seq<u8>, cap: int, xs: Seq<Piece>)
    requires trace(s, 0, Seq::empty(), xs),
             trace_output(s, Seq::empty(), xs).len() <= cap,
    ensures decode(s, 0, Seq::empty(), cap, s.len() + 1) == Some(Decoded {
        out: trace_output(s, Seq::empty(), xs), pieces: xs,
    })
```

The definitions that determine this statement's meaning are in the same file:

- `extension` describes a nonempty run of 255 bytes followed by a byte below
  255; `field` interprets the token nibble and any such extension.
- `sequence` describes the token, literal bytes, little-endian offset, and match
  length. Every match has offset between 1 and the already produced length.
- `expand` copies forward one byte at a time, including overlapping matches;
  `apply` appends a sequence's literals and match.
- `trace` describes a nonempty sequence list that consumes the entire input and
  ends in a literal-only sequence. `trace_output` is its decoded byte sequence.
- `decode` is a separate recursive parser with a capacity check. Its fuel is
  `s.len() + 1`; `trace_bounds` proves there are at most `s.len()` sequences.

The model permits relaxed end conditions. It does not require five final
literals or the last match to start twelve bytes before the decoded end. Thus
the model completeness theorem covers a broader language than the intended R2
premise, provided the English format is interpreted by this grammar. That
interpretation is a specification-review obligation, not a machine-checked
translation of English. `example_independent_block` supplies a checked,
non-vacuous witness: `13 61 01 00 50 62 63 64 65 66` decodes to eight `61` bytes
followed by `62 63 64 65 66`; it also satisfies the strict end conditions.

What remains: prove that the shipped WASM, for every valid block and permitted
placement/capacity, returns this model's output length and stores these bytes,
without trapping. The model theorem contains no such simulation claim.

## R3: every successful decode has a valid sequence interpretation

**Artifact status: unproved; no demonstrated failure.** The exact checked
model-level soundness theorem in `verification/format.rs` is:

```rust
pub proof fn model_r3(s: Seq<u8>, cap: int)
    ensures match decode(s, 0, Seq::empty(), cap, s.len() + 1) {
        None => true,
        Some(d) => 0 <= d.out.len() <= cap
                   && trace(s, 0, Seq::empty(), d.pieces)
                   && d.out == trace_output(s, Seq::empty(), d.pieces),
    }
```

The grammar's offset checks are relative to the decoded prefix, with no external
dictionary. The final literal-only sequence consumes all remaining input.
The output length bound and decoded content are both part of the conclusion.
`expand_correct` additionally proves that forward-copy output has the stated
length, preserves its prefix, and each new byte equals the earlier byte at its
offset. Auxiliary soundness/completeness lemmas relate the parser to the grammar;
the grammar is not defined simply as “whatever `decode` accepts.”

What remains: show that *every* nonnegative return from the WASM corresponds to
a model success with the same output. Finite agreement with a test oracle does
not establish this implication.

## Reproduction

Run these commands from this directory, with the installed offline tools:

```sh
verus --version
verus verification/format.rs
python3 verification/check_artifact.py
```

The Verus version used was `0.2026.10.18.7d82994` (release), as requested. The
proof command exits zero and prints:

```text
verification results:: 26 verified, 0 errors
```

The script checks identity, runs `wasm-tools validate`, constructs an importing
WASM harness, and invokes Wasmtime with compilation caching disabled to avoid
writes outside the workspace's writable temporary directory. It exits zero and
prints:

```text
artifact: 7161 bytes, SHA256 1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
PASS: 375 vectors, 750 original-artifact executions; return, successful output, and unchanged final memory outside dst checked.
LIMIT: finite executions; forbidden reads, transient writes, and universal R1/R2/R3 are not proved.
```

Wasmtime used was `50.0.0`; wasm-tools was `1.262.0`. Inputs cover literal lengths
and extension boundaries, overlapping/nonoverlapping matches, multiple sequences,
exact/insufficient/ample capacities, malformed lengths and offsets, and relaxed
end conditions. Each vector runs with opposite buffer orders at the extremes of
the caller region. Expected results come from the Python byte parser in the
script, **not from a proved equivalence to the Verus model**. The harness checks
successful output bytes, returns, source preservation, and final memory outside
the destination. Its 750 executions are finite evidence only. WASM validation
checks module well-formedness, not the README's requirements.

For independent artifact inspection:

```sh
sha256sum lz4-flex.wasm
wasm-tools print lz4-flex.wasm
```

## Review and trust

| Material | Size | Role / trust required |
| --- | ---: | --- |
| `verification/format.rs` | 450 lines; 15,851 bytes | Review the grammar, model, hypotheses, and theorem statements. All 26 proof bodies are checked by Verus. No `assume`, `admit`, or external proof bodies are used. |
| `verification/check_artifact.py` | 207 lines; 9,148 bytes | Unverified finite-test oracle and harness generator; review its input construction, assertions, module import, and identity check. Generated harnesses are temporary. |
| `lz4_Block_format.md` | 244 lines; 10,683 bytes | Authoritative supplied English format; its correspondence to the model needs human review. |
| `README.md` | 18 lines; 2,402 bytes | Required artifact, interface, memory assumptions, and R1–R3. |
| `CHECK.md` | 8 lines; 784 bytes | Report requirements. |
| `lz4-flex.wasm` | 7,161 bytes | Exact tested subject; identified above. |

Tool infrastructure trusted for the respective results comprises Verus and its
vstd, SMT solver, Rust/toolchain infrastructure used by Verus, Python and its
standard library (including SHA-256), wasm-tools, Wasmtime, and the host platform.
Their installed binaries/libraries are not included in the source-size table.
The mathematical proofs do not rely on the Python script or Wasmtime. The
artifact executions do not rely on a Rust rebuild or the Verus model.

The principal missing result is a verified refinement from the exact WASM bytes
to the model, including memory effects and exceptional behavior. Until that is
supplied, all three universal artifact requirements remain open.
