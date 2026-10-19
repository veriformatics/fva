# Verification

## Run all checks

From this repository, run:

```sh
./check.sh
```

The check is offline and fail-closed. It requires Lean 4.35.0, Python 3,
Clang with the Wasm linker, `leanexport`, `leanchecker`, `nanoda_bin`, and
`con-ron`. The checker finds the replay tools on `PATH` or in Lean's `bin`
directory. They are installed in `/opt/lean/bin` in the supplied environment.
No Lake dependencies or Mathlib are used.

The command creates `.verification-build/` from scratch. It records every
subprocess command in `commands.log`, each tool's output in a separate log,
and the final measurements in `report.json`. A failed stage exits nonzero.
It does not change `isqrt.c`, `isqrt.wasm`, or `README.md`.

## What is proved

The theorem `requirements` in `verification/Requirements.lean` quantifies over
all natural numbers `n < 2^32`, not a sample of inputs. It proves:

- **R2:** A finite number of Wasm instruction steps reaches a returned result.
- **R1:** Every returned result `r` satisfies `r < 65536`, `r*r ≤ n`, and
  `∀ s : Nat, s*s ≤ n → s ≤ r`. These squares use unbounded natural-number
  multiplication, so the specification cannot pass because of overflow.

The proof maintains `lo < hi ≤ 65536` and `lo*lo ≤ n < hi*hi`.
The midpoint is strictly between the bounds. All midpoint additions,
subtractions, and products remain within their Wasm word widths, so their
wrapping semantics agree with the mathematical operations used in the proof.
Each continuing iteration strictly decreases the natural number `hi-lo`.
Strong induction proves termination. Determinism and stability of a returned
configuration prove that every returning execution has the certified result.

## Connection to the implementation

The subject of the proof is **the shipped `isqrt.wasm`**, not a separate Lean
implementation of binary search.

1. `check.sh` runs the exact README build command, with only the output path
   changed to `.verification-build/rebuilt.wasm`. It compares all resulting
   bytes with `isqrt.wasm`.
2. `verification/generate.py` reads the shipped bytes afresh and emits
   `Artifact.bytes : List Nat`. It also emits single-instruction facts.
   Each fact has a Lean `rfl` proof against the byte-level interpreter; the
   generator cannot silently assign a different meaning to an opcode.
3. `Wasm.invoke` checks the module's exact 58-byte envelope and total length.
   The envelope fixes the signature `(i32) -> i32`, function index, export
   name `isqrt`, local declarations, memory, and section/body lengths. There
   are no imports or a start function. Execution uses the remaining 72 bytes.
4. `Wasm.step` fetches instructions directly from those bytes. It models
   locals, operand stack, program counter, loop labels, unsigned comparisons,
   conditional selection and branching, and modular 32/64-bit arithmetic.
   Unsupported instructions or malformed states fail; they cannot establish
   a returning execution.
5. The proof symbolically executes initialization, loop bodies, and return
   instructions. The final theorem mentions `Artifact.bytes` directly.

The original C and Wasm files remain unchanged. The recorded SHA-256 values
are for identification, not substitutes for decoding, proof checking, or the
byte-for-byte rebuild comparison.

## Human review surface

The checker writes `REVIEW.txt`: all of `verification/Semantics.lean`, the
freshly generated `Artifact.lean`, and the final `requirements` statement
(without its proof). This is the conservative project-specific statement and
definition review surface; it includes comments, imports, and blank lines.
**Size: 109 lines, 4,027 UTF-8 bytes**, including all 130 artifact bytes as
numerals. The checker recomputes these counts in `report.json`.

The semantic definitions are `envelope`, `Config`, `immediate`, `step`,
`Runs`, `invoke`, and `IsSqrt`; the eighth definition is `Artifact.bytes`.
`Runs` is an inductively defined finite execution relation. Bounded evaluator
`steps` is proof machinery, connected to `Runs` by the proved `of_steps` lemma.
The loop invariant and auxiliary states are proof machinery, not assumptions
in the final statement. The generated instruction facts and all proof bodies
are checked, rather than trusted as translations or certificates.

The runner and byte-emission code are a separate integration review surface:
`check.sh`, `verification/check.py`, and `verification/generate.py`
(**363 lines, 16,859 UTF-8 bytes**, including comments and blank lines). Review
that they read the intended files, invoke the actual tools, and propagate
failures. Standard Lean definitions of naturals, lists, options, strings, equality,
and logical connectives are also dependencies; replay includes their
transitive proof dependencies. The export contains 1,553 declaration records (1,739 kernel constants after
expanding inductive families), all replayed. The runner also records the
replay-tool binary hashes.

## Independent kernels and false-proof controls

The checker exports only `requirements` and its transitive dependency closure.
It then replays that same export from scratch through:

- Lean's C++ kernel: `leanchecker --from-export`.
- Nanoda's independently implemented Rust kernel.
- `con-ron`'s Rust kernel, in `--verified` mode.

After the build, the exact replay commands in this environment are:

```sh
/opt/lean/bin/leanchecker --from-export .verification-build/requirements.ndjson
/opt/lean/bin/nanoda_bin .verification-build/requirements.nanoda.json
/opt/lean/bin/con-ron --verified --jobs=2 .verification-build/requirements.ndjson
```

The Lean compilation commands have the form
`lean -R verification -o .verification-build/NAME.olean verification/NAME.lean`.
The generated `Artifact` and `Bytecode` modules instead use
`-R .verification-build` and source paths inside that directory. The complete
ordered commands, including export and negative controls, are in `commands.log`.

These are not three invocations of Lean's elaborator. No compiled tactic or
native-decide result is accepted as an axiom. The export is audited with an
allowlist containing only `propext`, `Classical.choice`, and `Quot.sound`.
This proof uses **`propext` and `Quot.sound` only**; `Classical.choice` is not
needed. The runner independently audits this from the export.

The supplied Nanoda binary also reports one pretty-printer error,
`Unable to print axioms`; it reports zero type-checker errors and exits zero.
This printer message is preserved in its log.

All three replay paths must accept positive controls and reject both of
these well-formed but false proof terms:

- `False`, supplied with the proof term `True.intro`.
- `1 + 1 = 3`, supplied with the original proof term for `1 + 1 = 2`.

The test changes only the target theorem's type in an otherwise valid export.
It checks for type-checking rejection, not merely missing files or invalid
input syntax. A separate control compiles a `sorry` proof and requires the
axiom audit to reject `sorryAx`. Another control changes a shipped Wasm
constant, regenerates the bytes and valid instruction facts, and requires the
unchanged initialization proof to fail. Negative controls never overwrite the
real artifact or the accepted proof build.

The exact expanded commands and rejection diagnostics are preserved under
`.verification-build/`. `verification/check.py` specifies their arguments and
checks; `./check.sh` is the single complete entry point.

## Boundaries

The small Wasm semantics and the module envelope still require human review
against the WebAssembly instruction meanings. This is not a mechanized proof
of a complete WebAssembly standard implementation. The interpreter supports
the shipped instruction/constant subset; it is not a general Wasm validator.
The connection from these definitions to an external Wasm engine is not
proved inside Lean.

The C-to-Wasm connection is an observed exact rebuild, not a verified Clang
compiler theorem or a proof under general ISO C semantics. The result applies
to the documented shipped Wasm deployment, not every compiler, target, or
build flag. Instantiation/allocation success, hardware, operating system,
and the execution engine are outside the theorem. Abstract instruction
termination does not assert a wall-clock deadline or prevent host fuel limits.

Independent replay and negative controls do not prove the kernels themselves
bug-free. The proof uses ordinary Lean foundations and the explicitly audited
standard axioms. Neither R1 nor R2 is left unproved under the stated byte-level semantics.
