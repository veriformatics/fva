# Verification results

R1, R2, and R3 remain **unresolved in their full stated generality**. I found no
counterexample. The deliverables below establish a limited quantified result,
check the extraction of the actual decompressor instructions in Lean, and check
48 concrete executions. These results do not establish the three universal
requirements. This report uses CHECK.md's option to state what could not be proved.

## Connection to the shipped artifact

The checked file is `lz4-flex.wasm`, 7,161 bytes, SHA-256
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.
The artifact and original Rust sources have not been changed or rebuilt.

`verification/extract.py --check` verifies this hash, the module header, absence
of imports/start, fixed 32-page memory, the exports, the number of functions,
and the decompressor's local declarations. It regenerates data in memory and
compares the entire generated Lean file with `Proofs/Artifact.lean`. Thus the
embedded `artifact` list is tied to every byte of the shipped file, rather than
to a recompiled crate. The Python extraction and this file comparison are part
of the trust boundary; Lean does not read the external file or prove SHA-256.

The following are the exact public theorem statements in
`Proofs/Artifact.lean` (all names are in namespace `Verification`):

```lean
theorem body_bytes :
  (artifact.drop 4437).take 2000 = rawBody
theorem local_declarations :
  rawBody.take 5 = [2, 17, 127, 7, 126]
theorem decoded_body :
  decode 2001 (rawBody.drop 5) = some program.toList
theorem instruction_count : program.size = 982
```

These use `decide`, without native evaluation axioms. In particular, an
independent Lean byte decoder checks the generated instruction sequence. The
five-byte prefix declares 17 i32 and 7 i64 locals; four parameters bring the
local array size to 28. Function index 7 is the exported decompressor.

`Proofs/Wasm.lean` defines execution of these instructions, with wrapping i32
arithmetic, little-endian loads/stores, block/loop labels, memory bounds,
snapshot `memory.copy`, `memory.fill`, and a read/write access log. This is a
handwritten model of the relevant WebAssembly subset. Its agreement with the
WebAssembly specification has **not** been formally proved. Calls return
`unsupported`, rather than being assumed to return or trap. Every concrete
check requires a normal return, so unsupported instructions, calls, traps, and
fuel exhaustion cannot silently pass. A successful finite run uses at most
20,000 modeled steps. All modeled memory accesses are logged, not just bytes
that differ at the end.

## R1: memory access confinement

The exact quantified theorem in `Proofs/Empty.lean` is:

```lean
theorem empty_input_no_access (src dst cap : Nat) (mem : Memory) :
    match run program 5 (initialState src dst 0 cap mem) with
    | .returned r s =>
        r = 4294967295 ∧ s.mem.writes = mem.writes ∧ s.accesses = []
    | _ => False
```

This establishes, in the bytecode execution model, that empty encoded input
returns i32 -1 in five instructions with no memory access. It quantifies over
arbitrary initial memory and arbitrary buffer parameters, and so includes all
README-permitted parameters with `n = 0`. Its proof uses instruction lookup
lemmas and `simp`, without native evaluation axioms. An empty byte string is
not the valid LZ4 encoding of empty decoded content; that encoding is `[0]`.

For each of the 48 finite cases, `cases_checked` below also checks every read
range lies in the supplied source or destination, and every write range lies
in the destination. This is stronger than checking only the final memory for
these executions. The initial memory is fixed for these cases: input bytes at
`src`, and byte 165 everywhere else.

The Wasmtime checks separately scan every address 131072 through 2097151
outside the destination and check its pre-call value is preserved, including
the source bytes. This observes final writes; it cannot detect reads, or
temporary writes that were restored.

**Missing:** a confinement invariant covering every loop iteration and path
for arbitrary input, buffers, and initial memory, plus a proof of the execution
model's adequacy for WebAssembly. Neither the finite access logs nor Rust's
checked source code supplies that proof. No R1 violation was demonstrated.

## R2: completeness and correct decoded content

`Proofs/LZ4.lean` supplies a separate LZ4 sequence interpreter, using natural
number lengths and byte-at-a-time overlapping matches. It checks nonzero
offsets referring to already decoded bytes. `endConditions` checks the final
literal run and the last-match distance (in decoded bytes). Its correspondence
to `lz4_Block_format.md` is a review obligation, not a proved theorem.

The exact aggregate statement in `Proofs/Cases.lean` is:

```lean
theorem cases_checked : allCases.all checkCase = true
```

The file additionally contains the individual exact statements
`checked_0 : checkCase case0 = true` through
`checked_47 : checkCase case47 = true`.
Every `caseN` is defined explicitly in that file. `allCases` lists exactly those
48 cases. Their source of truth for generation is `verification/cases.py`;
`--check` compares its output with the committed Lean data.

`checkCase`, defined in `Proofs/Checks.lean`, checks the README buffer
preconditions, the reference format classification, a normal modeled return,
the full access log, and the expected return. For each expected success it
also checks that reference decoding equals the explicitly expected bytes,
the returned length equals their length and fits capacity, and every returned
destination byte equals its expected value.

There are 32 full-format, fitting success cases. They include empty content,
literal lengths at copy-size boundaries, literal length extensions with one
and two 255 continuation bytes, overlapping matches, disjoint matches, the
optimized paths, and either buffer ending at the memory boundary. Two further
full-format cases have insufficient capacity and correctly return -1; R2 does
not require their success. The other cases are described under R3.

All 48 cases also run against the exact binary in Wasmtime, checking return
values, all expected output bytes, and the memory canaries described above.
This runtime test embeds the shipped binary verbatim in WAST and imports its
exports into a test helper; it does not replace the decoder with a model.

**Missing:** a proof that every full-format independent block fitting capacity
terminates successfully and produces its reference decoding, including all
optimization paths, length loops, and overlapping copies. Finite case proofs
are not an induction over arbitrary blocks. No R2 violation was demonstrated.

## R3: soundness of successful decoding

The same exact theorem `cases_checked` and the individual `checked_N` statements
check soundness for the 33 successful finite cases: reference sequence parsing
succeeds, offsets are nonzero and refer to decoded bytes, output is correct,
and the returned length fits capacity. Of these, 32 meet all end conditions.
The other successful case is:

```text
src bytes = 10 41 01 00 00   (hex), cap = 5
return = 5, dst[0..5) = 41 41 41 41 41
```

It contains one literal, an offset-one match of length four, and a final
zero-literal token. Only end conditions fail, so this acceptance is permitted
by R3. It is not a counterexample.

The 13 syntax-invalid cases return -1. They include missing or unterminated
length extensions, truncated literals/offsets, missing final tokens, zero
offsets, and offsets preceding decoded content, including the optimized path.
The two insufficient-capacity cases also return -1.

**Missing:** a theorem that every possible nonnegative artifact return has a
valid sequence decomposition and the stated content, bounds, and offsets.
Checking particular rejections does not establish that implication for other
inputs. No R3 violation was demonstrated.

## Reproduction and trust

From this directory, with the installed Lean 4.35/Mathlib environment and tools:

```sh
bash verification/check.sh
```

The script runs these exact checks:

```sh
python3 -B verification/extract.py --check
wasm-tools validate lz4-flex.wasm
python3 -B verification/cases.py --check --wasmtime
lake build
lake env lean verification/Audit.lean
```

Success means exit status zero, the pinned-artifact and 48-case PASS messages,
a successful Lake build, the theorem types/axioms printed by `Audit.lean`, and
`PASS: all delivered partial verification results checked`. Wasm validation
is silent on success. The Wasmtime cache is disabled, and no network or Rust
toolchain is required. For an explicit re-elaboration of the proof files after
the build, also run:

```sh
lake env lean Proofs/Artifact.lean
lake env lean Proofs/Empty.lean
lake env lean Proofs/Cases.lean
```

**Finite proofs use `native_decide`.** Lean 4.35 records a generated native
evaluation axiom for each `checked_N`; `Audit.lean` prints all these dependencies.
Those results additionally trust Lean's compiler and evaluation runtime. They
are not certificates justified solely by kernel reduction. The byte extraction
theorems and quantified empty-input proof do not have that extra dependency.
The latter uses Lean's ordinary `propext`, `Classical.choice`, and `Quot.sound`
axioms. There are no `sorry` proofs or user-supplied assumptions of R1–R3.

Review/trust inventory (physical lines and bytes, excluding build caches):

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 254 | 9376 | Byte decoder, execution and access semantics |
| `Proofs/LZ4.lean` | 60 | 2219 | Independent format definition |
| `Proofs/Checks.lean` | 58 | 1984 | Case initialization and result predicates |
| `Proofs/Empty.lean` | 17 | 851 | Quantified theorem and prefix lemmas |
| `Proofs/Artifact.lean` | 1384 | 47851 | Generated complete bytes, instructions, extraction theorems |
| `Proofs/Cases.lean` | 489 | 26797 | Generated inputs, expected outputs and finite proofs |
| `verification/extract.py` | 133 | 4982 | External-byte binding, module/container checks, generator |
| `verification/cases.py` | 178 | 8174 | Case definitions, generator, exact-binary WAST harness |
| `verification/check.sh` | 9 | 304 | Reproduction commands |
| `verification/Audit.lean` | 12 | 400 | Statement and axiom inventory |
| `Proofs.lean` | 2 | 40 | Proof library imports |
| `README.md` | 18 | 2402 | Requirements |
| `lz4_Block_format.md` | 244 | 10683 | English format specification |

Also trusted are the installed Lean kernel and standard logical foundations;
Python and its file/hash operations for external-byte binding; Wasmtime for
the runtime observations; and `wasm-tools` for validation. Lake configuration
is `lakefile.toml` (12 lines, 264 bytes), `lake-manifest.json` (117 lines,
3536 bytes), and `lean-toolchain` (1 line, 25 bytes). Mathlib v4.35.0 and the
installed toolchains are external dependencies, not included in these local
file-size counts. The Rust compiler, vendored crate, and `build.sh` are not
used to justify artifact behavior in this verification.
