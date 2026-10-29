# Verification of `lz4-flex.wasm`

**Status: incomplete. R1, R2 and R3 are neither proved universally nor disproved.**
No counterexample was found. This directory supplies kernel-checked results about
a small subset of cases in an extracted instruction model, executable checks of
a larger model corpus, and finite execution checks of the actual artifact.
Passing these checks does **not** establish all three README requirements.

## Requirement-by-requirement results

| Requirement | Result and evidence | Remaining gap |
|---|---|---|
| R1 | `empty_input` proves that the modeled empty-input path returns -1 without any memory accesses or stores, uniformly in addresses, capacity and initial memory. `corpus_checks` and `single_byte_checks` check all recorded memory accesses for 9 selected calls. Executable model assertions check access confinement for all 570 calls, and direct execution checks unchanged memory outside the destination. | No invariant proves confinement for arbitrary input, buffer placement, capacity or initial destination bytes. Runtime memory comparisons cannot detect forbidden reads or writes that restore the original bytes. The access traces belong to the model. |
| R2 | `valid_format_checks` checks 3 selected blocks against the independent format parser, including end conditions and sufficient capacity. `corpus_checks` checks their modeled returns and bytes. Executable model assertions check all 35 valid blocks; direct binary execution agrees. | No general simulation, termination or completeness proof for the decoder loop. The parser's correspondence to the prose specification is reviewed, not formally proved. |
| R3 | The kernel certificates check expected returns, capacity bounds and content for 9 selected calls, and check the successful cases with the independent parser, including offset validity. Executable model assertions and binary executions additionally check all 570 calls. | No theorem shows that every successful execution admits such a parse. Concrete malformed-input cases do not exhaust malformed blocks. |

The empty compressed byte string is invalid; the valid encoding of empty content
is a one-byte token, such as `[0]`. These are separate cases. A match-only ending
`[16,65,1,0]` returns -1; adding a final empty sequence gives
`[16,65,1,0,0]`, which returns 5 and writes five bytes equal to 65. This acceptance
is permitted by the end-condition exception in R3; it is not a counterexample.

## Exact machine-checked theorem statements

All names below are in namespace `Verification`. The notation and definitions are
in the cited files. The proof scripts use `cbv`/`decide_cbv`, which produce proof
terms checked by Lean's kernel; they do not use `native_decide` or introduce axioms.

In `Proofs/Properties.lean`:

```lean
theorem empty_input (src dst cap : Nat) (initial : Nat → Nat) :
    let s := run decoder initial 5 (start src dst 0 cap)
    (s.result, s.accesses, s.stores, s.failed) =
      (some 4294967295, [], [], false)
```

The axiom reports are `[propext]` for `empty_input`, `valid_format_checks` and
`successful_reference_checks`, and `[propext, Quot.sound]` for `corpus_checks`
and `single_byte_checks`.

`4294967295` is the unsigned representative of the returned i32 value -1.
This theorem takes five modeled instructions, including the explicit `return`;
it is uniform in all four arguments. In particular, it implies the R1 property
for all admissible empty-input calls, **subject to the trusted model connection**.

In `Proofs/Cases.lean`:

```lean
theorem corpus_checks : certifiedCases.all checkCase = true

theorem valid_format_checks : certifiedValidCases.all validReference = true

theorem successful_reference_checks :
    (certifiedCases ++ certifiedTokens).all referenceAgrees = true

theorem single_byte_checks : certifiedTokens.all checkCase = true
```

`checkCase` requires legal, disjoint buffers; completion with the expected return
within 2,000 modeled instructions (13,000 when capacity exceeds 300); no failed/unsupported operation; all accesses
at or above 131072; R1 confinement of each accessed byte; and, on success, the
specified output length, capacity bound and every decoded byte. For expected
errors it requires the i32 result -1, and still checks memory confinement.
Exhausting the instruction budget without a return fails the check.

`validReference` requires that the independent parser returns the expected content,
that its end-condition predicate holds, and that the content fits in capacity.
`referenceAgrees` checks parser output for every case expected to succeed; it is
vacuously true for cases expected to return -1. `checkCase` independently ensures
that those error cases actually return -1 in the model.

The kernel certificates cover these explicit selections from `Proofs/Fixtures.lean`:

- `certifiedCases`: valid empty content, a one-byte literal, an offset-1 match of
  length 7 followed by five literals, rejection of offset zero, and acceptance
  of a final empty sequence after a match;
- `certifiedValidCases`: the first three of those cases;
- `certifiedTokens`: one-byte blocks `[0]`, `[15]`, `[16]`, `[240]`, each at capacity 0.

These are 9 calls counting the repeated `[0]` case. The general corpus below has
**executable assertions, not kernel certificates for all its cases**. The attempted
larger `decide_cbv` proofs were stopped because computing them was too expensive;
this is a practical limit of this interpreter/proof approach, not evidence of
any decoder failure.

The full case definitions, also in `Proofs/Fixtures.lean`, contain:

- 21 literal-only blocks, with content lengths 0 through 300 at selected boundaries;
- 14 blocks with matches, including offsets 1, 2 and 3, overlapping copies,
  lengths 4, 7, 18, 19, 32, 33, 64, 65 and 300, length extensions, and hot-path cases;
- 12 malformed inputs, including truncated lengths/offsets, offset zero, and
  offsets beyond decoded content;
- 3 insufficient-capacity calls;
- 3 end-condition probes, including the rejected match-only ending;
- 5 calls at memory boundaries, with adjacent buffers, or with reversed buffer order;
- 512 calls covering all 256 one-byte inputs, each at capacities 0 and 64.

There are 58 `corpus` cases, 35 `validCases`, and 512 `tokenCases`: 570 calls,
74 expected successes and 496 expected errors. Input/output addresses and bytes
are explicit in the definitions/builders and in regenerated `verification/cases.json`.
The model initializes destination bytes to 170, input bytes to the specified
block, and all other bytes to zero. The all-accesses-at-or-above-131072 check
means that the model's omission of the module's static data does not affect
these modeled executions. Only `empty_input` quantifies over arbitrary memory.

## Connection to the shipped artifact

The target remains the original **7,161-byte** `lz4-flex.wasm`, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

No Rust source or artifact bytes were modified or rebuilt. The results do not
assume that a Rust compiler correctly compiled `shim/`.

`verification/extract.py` checks that size and hash, obtains the text disassembly
with `wasm-tools print`, checks the memory declaration and the decoder export,
and translates function 7 into `Proofs/Decoder.lean`. It retains 981 instructions,
including structured control flow and all memory operations, with matched
block-end instruction indices. The balanced instruction table changes lookup
cost, not instruction order. `--check` regenerates the text and requires exact
agreement with the checked-in Lean file.

`Proofs/Machine.lean` is a manually written interpreter for that instruction
subset: i32 modular arithmetic and unsigned comparisons, locals, operand and
label stacks, branches, returns, little-endian i32/i64 loads/stores, memory bounds,
`memory.copy` with snapshot semantics, and `memory.fill`. It records the byte
ranges of memory operations. Calls/panic paths are deliberately unsupported
and make a check fail; they are not silently assumed safe. The validated module
supplies the typing/stack-discipline assumptions under which this subset model
is intended to match Wasm. It is not a complete verified WebAssembly semantics.

**Neither the extractor nor the interpreter has a formal refinement proof against
WebAssembly's specification.** The Lean theorems are literally about this model.
Reviewing that connection is a trust obligation, even for `empty_input`.

`verification/Export.lean` first executes Boolean assertions of `checkCase` and
`referenceAgrees` on all 570 calls and `validReference` on the 35 valid blocks.
These assertions use Lean's executable evaluator and therefore trust its compiler
and runtime; they are not additional kernel proofs. It then exports the concrete
fixtures, modeled return values, and entire modeled destination buffers.
`verification/runtime.mjs` loads the hash-pinned artifact directly into Node's
WebAssembly engine. For each call it restores pristine module memory, initializes
the caller buffers, and checks:

1. the actual signed return against the expected result and the model;
2. every byte of successful decoded content;
3. the entire destination capacity against the model, including speculative stores;
4. every byte outside the destination against the pre-call memory snapshot.

It reuses one instance and resets its memory between calls. Function 7 contains
no global-access instructions, so there is no decoder global state to reset.
The runtime checks include the module's real initialized data below 131072.
These are finite tests, not proofs of the model/binary correspondence or of
read confinement. Wasmtime separately executes the zero-length and zero-token
cases using the actual module; its cache is disabled to work within the sandbox.

## Reproduction

Run from this directory, with the installed local Lean/Mathlib dependencies:

```sh
bash verification/check.sh
```

`bash verification/check.sh` completed with exit status 0 on this installation.

For a fresh check of all local proof files, removing only this project's build
outputs first:

```sh
lake clean proofs
bash verification/check.sh
```

The script runs exactly:

```sh
python3 verification/extract.py --check
wasm-tools validate lz4-flex.wasm
lake build Proofs.Fixtures
lake env lean Proofs/Cases.lean
lake env lean verification/Export.lean
node verification/runtime.mjs
wasmtime run -C cache=n --invoke lz4_decompress lz4-flex.wasm 131072 1048576 0 0
wasmtime run -C cache=n --invoke lz4_decompress lz4-flex.wasm 131072 1048576 1 0
```

The shell script checks the last two commands' standard output against `-1` and
`0`. Wasmtime may also emit its experimental-`--invoke` warnings on standard error.
No network, Rust compilation, or skill/plugin is required.

Success means exit status zero throughout, `Build completed successfully`, no
Lean errors or `sorryAx`/`Lean.ofReduceBool` in the printed axiom reports, export of
570 cases, and these final runtime/script messages:

```text
PASS: 570 direct executions; returns, full destination memory, and unchanged memory outside destination
PASS: Wasmtime empty-input and zero-token checks
PASS: all verification checks (scope and gaps in VERIFICATION.md)
```

Intermediate runtime progress messages are expected. A successful build may reuse
previously checked local outputs; use `lake clean proofs` first to force rechecking.
Passing the script certifies only the scope stated here.

## Review and trust obligations

The reviewer must inspect the meaning of the definitions, rather than treating
Boolean theorem names as the requirements themselves. Local review surface
(exact UTF-8 bytes, including comments and whitespace):

| File | Lines | Bytes | Role |
|---|---:|---:|---|
| `Proofs/Machine.lean` | 162 | 6513 | Trusted instruction semantics and memory/access model |
| `Proofs/Fixtures.lean` | 192 | 7636 | Trusted checks, independent format parser, end conditions, fixtures |
| `Proofs/Properties.lean` | 12 | 401 | Uniform empty-input theorem/proof |
| `Proofs/Cases.lean` | 25 | 990 | Finite theorem statements, proofs and axiom reports |
| `verification/extract.py` | 56 | 3294 | Trusted disassembly-to-model translation and byte identity check |
| `verification/Export.lean` | 22 | 1024 | Model-to-runtime fixture export |
| `verification/runtime.mjs` | 43 | 2207 | Actual binary execution and memory comparisons |
| `verification/check.sh` | 14 | 709 | Reproduction orchestration |
| `Proofs.lean` | 1 | 20 | Imports the proof modules |
| `Proofs/Decoder.lean` | 1966 | 29774 | Generated 981-instruction model; regenerate instead of trusting it independently |
| `verification/cases.json` | 1 | 159019 | Generated concrete runtime inputs and expected results; regenerated by the script |
| `README.md` | 18 | 2402 | Requirements being interpreted |
| `lz4_Block_format.md` | 244 | 10683 | Prose format specification being interpreted |

The Lake configuration is 12 lines/264 bytes, the toolchain pin 1 line/25 bytes,
and the manifest 117 lines/3536 bytes. Source sizes can be rechecked with `wc -lc`.

External trust includes Lean 4.35.0's kernel and primitive reductions, its standard
logical axioms and imported library definitions (Mathlib v4.35.0), the host OS and
hardware, Python/hashlib, `wasm-tools` disassembly and validation, and the Wasm
engines for the runtime results. The compiler/evaluator running `Export.lean` is
trusted for executable model assertions and exported tests, not for proving the
Lean theorems. On this installation,
Mathlib's `Mathlib/` source tree occupies 98,879,465 bytes and Lean's `Init/` source
tree 8,706,603 bytes (`du -sb`); these are shared preinstalled dependencies, not
new verification code. Recorded external tools: wasm-tools 1.262.0
(20,431,992-byte executable), Wasmtime 50.0.0 (67,968,088 bytes),
Node v26.12.1 (59,027,744 bytes), and Python 3.14.8. These sizes describe this
installation, not a formal certificate for those tools.

Completing R1–R3 would still require a proved semantics/extraction connection and
inductive invariants covering all reachable decoder states: input consumption,
output position and capacity, extended lengths, speculative-copy bounds, match
references, decoded content, and termination. This submission does not supply
those universal proofs and does not claim that finite testing replaces them.
