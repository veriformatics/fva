# Verification report

**Partial verification. The universal R1, R2, and R3 claims about the shipped
module remain unproved. No counterexample was found.** The deliverables include
Verus proofs of a decoder model, arithmetic lemmas for the source's copy
footprints, a restricted proof bound to the actual module's entry bytes, and
finite execution checks of the actual module. These have different scopes.

The artifact is the unchanged `lz4-flex.wasm`, 7,161 bytes, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

## R1: restricted artifact result; general claim unresolved

For **all calls with `n = 0`**, the module returns `-1` without any linear-memory
reads or writes. This includes all legal source/destination placements and all
legal capacities in the README. The exact Verus statement in
[`verification/entry.rs`](verification/entry.rs), `entry_n_zero`, is:

```rust
ensures
    execute(PREFIX@, 0, 5).control == (Control::Returned { value: -1i32 }),
    execute(PREFIX@, 0, 5).reads == Seq::<int>::empty(),
    execute(PREFIX@, 0, 5).writes == Seq::<int>::empty(),
```

Here `execute` applies five instruction steps of a deliberately small Wasm
semantics, starting at the function entry with an empty operand stack.
[`verification/check_entry.py`](verification/check_entry.py) checks the artifact
hash, parses the export and code sections, checks that there are no imports,
locates `lz4_decompress` at function index 7, skips its local declarations, and
checks that its entry bytes equal `PREFIX`:

```text
02 40 20 02 0d 00 41 7f 0f 0b
block void; local.get 2; br_if 0; i32.const -1; return; end
```

With parameter 2 equal to zero, the branch is untaken and the return executes.
The other parameters never occur on this path. The fragment has no memory
instructions or calls. The trust boundary is the binary reader and the
handwritten semantics of these instructions; this is not a complete verified
Wasm interpreter. In particular, its abstraction of a taken branch is irrelevant
to the proved path.

There are also **seven conditional arithmetic lemmas** in
[`verification/bounds.rs`](verification/bounds.rs). The exact contracts are the
`requires`/`ensures` clauses of the named declarations. For clarity, the complete
mathematical statements follow; all variables below are mathematical integers.
Define:

- `range(b,z,a,w)` to mean `131072 <= b`, `0 <= z`, `b+z <= 2097152`,
  `0 <= w`, `b <= a`, and `a+w <= b+z`.
- `W(o,c,m) = 32` if `m <= 32 && o+32 <= c`; otherwise `64` if
  `33 <= m <= 64 && o+64 <= c`; otherwise `m`.

| Lemma | Preconditions | Conclusions |
| --- | --- | --- |
| `relocate(b,z,i,w)` | `131072 <= b`, `0 <= z`, `b+z <= 2097152`, `0 <= i`, `0 <= w`, `i+w <= z` | `range(b,z,b+i,w)`, `0 <= b+i < 2^32`, `0 <= b+i+w < 2^32` |
| `hot_bounds(n,c,i,o,l,m,d)` | `0 <= n,c <= 2097152`, `1 <= i <= n`, `i <= max(n-18,0)`, `0 <= o < max(c-34,0)`, `0 <= l <= 14`, `4 <= m <= 18`, `1 <= d <= o+l` | `i+16 <= n`, `l+2 <= 16`, `i+l+2 <= n`, `o+16 <= c`, `o+l+18 <= c`, `0 <= o+l-d`, `o+l-d+18 <= c`, `o+l+m <= c` |
| `slow_wild_bounds(o,c,m,d)` | `0 <= o <= c <= 2097152`, `4 <= m`, `o+m <= c`, `m <= d <= o` | `0 <= o-d`, `m <= W(o,c,m)`, `o+W(o,c,m) <= c`, `o-d+W(o,c,m) <= c` |
| `forward_bounds(o,c,d,m,i)` | `1 <= d <= o <= c <= 2097152`, `4 <= m`, `o+m <= c`, `0 <= i < m` | `0 <= o+i-d < o+i < c`, `0 <= o-d < c` |
| `double_copy_bounds(l,k)` | `0 < k <= l` | `0 <= l-k`, `k <= l`, `(l-k)+k == l` |
| `length_no_wrap(n,u,s,b)` | `0 <= u < n <= 2097152-131072`, `0 <= s <= 255*u`, `0 <= b <= 255` | `0 <= s+b <= 255*(u+1)`, `s+b+19+2097152 < 2^32` |
| `noninterference(s,n,d,c,a)` | `0 <= n,c`, `(s+n <= d || d+c <= s)`, `d <= a < d+c` | `!(s <= a < s+n)` |

These cover the intended hot-path 16/18-byte accesses, slow-path 32/64-byte
copies, overlapping copies, fastcpy end copies, length arithmetic, and
relocation into caller memory. They do **not** prove that every actual Wasm
access satisfies their preconditions. There is no checked invariant over the
full Wasm control flow and no verified lowering of Rust slice operations,
`copy_within`, fills, or compiler-generated copies. Therefore general R1,
including restrictions on reads on malformed inputs, is unresolved.

The model helpers in `decoder.rs` also have verified indexing, overflow,
copy-content, and frame contracts. This is safety of those model operations,
not an address-trace theorem about the full shipped module.

## R2: complete model theorem; artifact claim unresolved

[`verification/decoder.rs`](verification/decoder.rs), `model_r2`, has this exact
contract (the return type is `Option<usize>`):

```rust
requires
    s.len() <= LIMIT, out.len() <= LIMIT,
    valid_independent_block(s@, content), content.len() <= old(out).len(),
ensures
    final(out).len() == old(out).len(),
    r.is_some(), r.unwrap() == content.len(),
    final(out)@.subrange(0, r.unwrap() as int) == content,
```

`LIMIT = 2097152`. The theorem is universal over the input vector, initial
output bytes, capacity, and ghost `content` satisfying these hypotheses. Model
success `Some(r)` corresponds to the shim's nonnegative return; model failure
`None` corresponds to `-1`.

The specification is independent of output capacity and of the model's fast
copy choices:

- `extension` consumes zero or more `255` bytes and a required terminating byte
  below 255; `length` handles the mandatory extension for nibble 15.
- `parse` consumes a token, the indicated literals, then either ends exactly at
  the source end or consumes a little-endian nonzero offset and match length.
  Final-sequence low token bits are ignored because there is no match field.
- `repeat` models byte-at-a-time forward match expansion, including overlap.
- `decodes(s,p,h)` recursively partitions the entire remaining source into such
  sequences. Before each match it requires `1 <= offset <= decoded_length`,
  then uses `repeat`. It returns `None` on any malformed partition or backward
  reference. It has no capacity parameter.
- `valid_independent_block(s,content)` means
  `decodes(s,0,Seq::empty()) == Some(content)` and `end_conditions`.
  The latter allows short literal-only blocks, otherwise requires at least five
  final literals and every match start at least twelve decoded bytes before
  the content end. Checking every match is equivalent to checking the last one
  here, because match start positions strictly increase.

A reviewer must check that these definitions express the supplied format prose.
`format_examples` additionally checks by Verus evaluation a valid empty block,
a valid overlapping-match block decoding to `aaaaaaaabcdef`, and rejection of
zero offsets, references before the decoded prefix, and unterminated lengths.
These examples are sanity checks, not the universal theorem.

No verified refinement connects the executable model to the full Rust decoder
or compiled Wasm. Consequently this proves R2 for the model, not general R2 for
the artifact. There is no demonstrated R2 violation.

## R3: complete model theorem; artifact claim unresolved

In the same file, `model_r3` has this exact contract:

```rust
requires s.len() <= LIMIT, out.len() <= LIMIT,
ensures
    final(out).len() == old(out).len(),
    r.is_some() ==> r.unwrap() <= final(out).len()
        && decodes(s@, 0, Seq::empty())
            == Some(final(out)@.subrange(0, r.unwrap() as int)),
```

The `decodes` conclusion includes a complete source partition, valid independent
match offsets, decoded content, and its length. It deliberately omits
`end_conditions`, as R3 permits accepting blocks that break those restrictions.
The stronger underlying function `decode` also proves the converse needed by
R2: if it returns `None`, either `decodes` is `None` or its content length exceeds
capacity. Its exact full contract is in `decoder.rs` at `decode`.

A supporting universal theorem, `snapshot_repeat`, states exactly:

```rust
requires 1 <= off <= h.len(), n <= off,
ensures repeat(h, off, n)
    == h + h.subrange((h.len() - off) as int, (h.len() - off + n) as int),
```

Thus the logical prefix of a nonoverlapping match is independent of any extra
bytes read by a wider snapshot copy. The verified `wild_match` helper uses this
lemma for physical widths 18, 32, 64, or the exact match length.

As for R2, equivalence with the full artifact remains unproved. There is no
demonstrated R3 violation. The `n=0` artifact result makes R3 vacuous for that
restricted class of calls, since the return is negative.

## How the model relates to the implementation

The model follows `decompress_internal::<false, SliceSink>` in
`shim/vendor/lz4_flex/src/block/decompress_safe.rs`, with the successful-path
16-byte literal copies, 18-byte hot match copies, and slow 32/64/exact snapshot
copies. `literals`, `matches`, and `wild_match` have proved content and frame
contracts. `word_sizes` proves
`usize::MAX == 4294967295 || usize::MAX == 18446744073709551615`; no global word-size
axiom is added, and the arithmetic checks include 32-bit `usize`.

However, the following are abstractions, not established equivalences:

1. The source uses slices into one Wasm memory; the model uses separate `Vec`s.
   No theorem transfers vector indexing to every compiled memory instruction.
2. Parsing is factored into `parse_piece`. Some errors are detected before
   writes that the source may already have performed. Output on errors is not
   specified by R2/R3; the missing R1 trace proof still matters on those paths.
3. Source loops are modeled using recursion for length parsing and sequence
   decoding. Stack exhaustion and physical allocation failure in the model are
   outside Verus's logical execution semantics and are not artifact claims.
4. A snapshot clone expresses `copy_within` semantics. Generic forward copying
   expresses overlapping matches, including the source's offset-one fill case.
   Rust/core, LLVM, and Wasm implementations of these operations are not verified
   by these model proofs.

The proofs do not import the vendor code and do not prove a Rust compilation
correctness theorem. An exploratory offline rebuild had different bytes (panic
source-path data and related constants differed). No rebuild or assumed
source-to-binary equivalence is used as evidence of full artifact correctness.
The artifact has not been replaced or patched.

## Exact-binary execution checks

[`verification/check_artifact.py`](verification/check_artifact.py) checks the
hash and length, validates the Wasm, embeds the **original binary bytes** in a
WAST module, and invokes the actual export in Wasmtime. A second module imports
its memory and decoder. For every case it initializes the caller region, writes
the input, calls the decoder, and checks:

- The exact return, against a separate Python reference parser.
- Every successful output byte against that parser's decoded bytes.
- Every source byte is unchanged.
- Every caller-region byte outside both buffers retains its initial value.

The result was **1,495 passing cases**, including **693 marked cases checked by
the Python parser to be format-valid independent blocks whose output fits**.
Other cases cover insufficient capacities, malformed and mutated inputs,
relaxed end conditions, extended lengths, multiple sequences, boundary buffer
placements, and extension chains nearly filling the entire caller region.
The seed and complete input generators are in the script; nothing is fetched.

These are finite executable assertions, not proofs of the universal
requirements. In particular, unchanged surrounding contents do not rule out
reads, writes of the same byte value, or writes later restored. The reference
parser and harness generation are trusted for the meaning of these tests.

## Reproduction

From this directory, run:

```sh
bash verification/check.sh
```

It runs these commands, stopping at the first failure:

```sh
verus --version
verus verification/entry.rs --no-cheating
python3 verification/check_entry.py
verus verification/bounds.rs --no-cheating
verus verification/decoder.rs --no-cheating
python3 verification/check_artifact.py
```

No network, Cargo build, Lean, or Mathlib is needed. Python assertions must be
enabled; both scripts refuse optimized Python execution. Temporary WAST and
Wasmtime cache files are created in a temporary directory and removed.

Success is exit status zero, Verus release `0.2026.10.18.7d82994`, and these
messages (other version metadata may also print):

```text
verification results:: 4 verified, 0 errors
PASS: export lz4_decompress = function 7; entry bytes = 024020020d00417f0f0b
verification results:: 8 verified, 0 errors
verification results:: 25 verified, 0 errors
artifact SHA-256: 1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
PASS: 1495 exact-binary cases; 693 generated format-valid cases
```

Verus's item counts include executable helpers, termination obligations, and
empty `main` functions; they are not counts of independent requirement theorems.
All proof files pass `--no-cheating`: none supplies `assume`, `admit`, an
`external_body`, or an `assume_specification`. The imported standard Verus
library and its supplied specifications remain part of the trust base.

## Review and trust inventory

The task-specific review material and sizes are listed below. All lines,
including comments and blank lines, are counted. The Rust files contain both
specifications to review and checked proof/implementation bodies. The Python
scripts and small Wasm semantics are not independently verified.

| File | Lines | Bytes |
| --- | ---: | ---: |
| `verification/entry.rs` | 68 | 2,941 |
| `verification/check_entry.py` | 74 | 2,154 |
| `verification/bounds.rs` | 86 | 3,571 |
| `verification/decoder.rs` | 501 | 19,727 |
| `verification/check_artifact.py` | 238 | 9,935 |
| `verification/check.sh` | 9 | 282 |
| `README.md` | 18 | 2,402 |
| `CHECK.md` | 8 | 784 |
| `lz4_Block_format.md` | 244 | 10,683 |
| `shim/src/lib.rs` | 34 | 1,167 |
| `shim/vendor/lz4_flex/src/block/decompress_safe.rs` | 495 | 18,526 |
| `shim/vendor/lz4_flex/src/sink.rs` | 346 | 10,339 |
| `shim/vendor/lz4_flex/src/fastcpy.rs` | 145 | 4,062 |
| `build.sh` | 10 | 604 |
| `shim/Cargo.toml` | 18 | 381 |
| `lz4-flex.wasm` (binary) | — | 7,161 |

The installed proof toolchain is also trusted: Verus and its Rust frontend,
`vstd` specifications and imported proof metadata, the SMT solver, and the
underlying operating system. Principal installed components measured here are
`rust_verify` (25,483,272 bytes), `vstd.vir` (30,838,617 bytes), `libvstd.rlib`
(9,864,436 bytes), and `z3` (34,954,456 bytes). These numbers describe the
installed binary/metadata objects, not a claim that their sources were audited.

For the binary binding and execution evidence, trust Python 3.14.8 and its
standard library (including SHA-256), wasm-tools 1.262.0 (20,431,992-byte binary),
and Wasmtime 50.0.0 (67,968,088-byte binary), including its validator and runtime.
SHA-256 identifies the intended file; the WAST runner actually receives all its
bytes. This trust list is not a verification of those tools or their system
libraries. The original Rust compiler is not needed to reproduce the reported
checks, and trusting that compiler alone would not bridge the missing
model/source equivalence proof.
