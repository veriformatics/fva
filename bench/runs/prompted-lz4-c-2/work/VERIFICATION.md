This is a **partial verification**, not a proof that the software meets R1–R3.
No counterexample to those requirements was found. The general decoding loop is
not verified. The results below comprise proofs of two general early-return
cases and 19 concrete executions of the shipped bytecode, with independent
kernel replay and runtime cross-checks.

**Requirement status**

| Requirement | Established result | Remaining obligation |
| --- | --- | --- |
| R1 | `Prefix.zero_capacity` proves at most one source-byte read and no writes for zero capacity, for arbitrary initial memory. `Prefix.zero_input` proves no accesses for zero input size. `Results.checked_cases` proves permitted access ranges for all 19 listed executions. | Safety for other inputs, buffer placements, capacities, and initial memories is unproved. In particular, no invariant covering all iterations, length extensions, arithmetic, and speculative copies is supplied. |
| R2 | The zero-capacity theorem proves the specified acceptance of the one-byte zero block. Twelve listed cases have valid independent strict-format encodings and the expected decoded bytes and lengths, by `Results.checked_cases` and `Results.strict_case_count`. | Completeness and correctness for every valid independent block are unproved. There is no induction connecting arbitrary format derivations to executions of the decoding loop. |
| R3 | For every successful execution in the finite case list, the returned length fits the capacity, equals the output length, and the output agrees with the relaxed format decoder: `Results.checked_cases` and `Results.successful_cases_parse`. The zero-capacity theorem establishes this behavior for all successful zero-capacity calls. | Soundness of every other successful execution is unproved. There is no proof recovering a sequence decomposition from an arbitrary accepting execution. |

The finite cases include empty input/output, truncated and excessive literals,
an invalid backward offset, overlapping matches, offset zero, extended literal
and match lengths, a shortcut copy, and buffers at the upper memory boundary.
Their complete inputs, addresses, capacities, expected returns, and expected
outputs are the definition `Results.cases` in [Proofs/Results.lean](Proofs/Results.lean).
The initial destination bytes are 165; other memory is initially zero except
for the artifact's data segment and the source bytes. These initial-memory
restrictions apply to the finite cases, not to the two early-return theorems.

**Exact machine-checked statements**

In [Proofs/Prefix.lean](Proofs/Prefix.lean), within namespace `Prefix`, with
`open Wasm`:

```lean
theorem decoder_is_artifact : program 2 = some decoder

theorem zero_capacity (src dst size : Nat) (mem : Memory)
    (hs : src ≠ 0) (hb : src < 2097152) :
    (invoke 100 src dst size 0 mem).map project =
      some ([if size == 1 && mem src % 256 == 0 then 0 else 4294967295],
        if size == 1 then [⟨false, src, 1⟩] else [], mem)

theorem zero_input (src dst capacity : Nat) (mem : Memory) :
    (invoke 100 src dst 0 capacity mem).map project =
      some ([4294967295], [], mem)
```

`project` returns the operand stack, the memory-access log, and the entire
final memory function. Thus these equalities also assert that memory is
unchanged. Access records contain a write flag, address, and byte count;
`⟨false, src, 1⟩` is a single-byte read. Values represent i32 bit patterns,
so 4294967295 denotes -1. For actual API calls, addresses and sizes are
represented by their unsigned i32 values. The theorem parameters impose fewer
conditions than the README preconditions, so they apply to the corresponding
legal calls.

In [Proofs/Results.lean](Proofs/Results.lean), within namespace `Results`:

```lean
theorem checked_cases : cases.all passes = true

theorem successful_cases_parse :
    cases.all (fun c => c.result ≥ 2147483648 ||
      Format.decode true false c.input == some c.output) = true

theorem strict_case_count : validCases.length = 12
```

Their key definitions are:

```lean
def passes (c : Case) : Bool :=
  observe 5000 c == some ([c.result], c.output, true) &&
    (c.result ≥ 2147483648 || (c.result ≤ c.capacity && c.result == c.output.length))

def validCases : List Case := cases.filter fun c =>
  Format.decode false true c.input == some c.output && c.result < 2147483648
```

`observe` executes the bytecode, reads the specified output bytes, and checks
every logged access byte against the README's permitted regions. A trap,
unsupported opcode, or insufficient execution fuel produces `none`, which
cannot pass. `Format.decode allowZero checkEnd` specifies independent LZ4
sequences, literal and match length extensions, little-endian offsets,
overlapping match expansion, optional zero offsets producing zero bytes, and
optional end-of-block conditions. Its complete definition is in
[Proofs/Format.lean](Proofs/Format.lean). This specification is another part of
the human review surface; no separate theorem proves it equivalent to the
English format document.

These six statements are the complete positive theorem set. In particular,
none is a universally quantified theorem claiming R1, R2, or R3 in full.

**Connection to the shipped artifact**

The checked artifact is `lz4-c.wasm`, exactly 8,469 bytes, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

[verification/extract.py](verification/extract.py) checks that hash and size,
parses the binary module sections, and checks its exports, absence of imports
and a start function, fixed memory size, global initialization, function types,
local declarations, and data segment. It extracts the raw instruction bytes of
function 2, exported as `LZ4_decompress_safe`, and functions 3 and 4, its memory
copy callees. It compares the resulting Lean input byte-for-byte with
[Proofs/Artifact.lean](Proofs/Artifact.lean). It does not compile or translate C.
The compressor is outside the requirements and is not interpreted.

[Proofs/Wasm.lean](Proofs/Wasm.lean) parses these **raw instruction bytes** and
executes a generic subset of WebAssembly, including actual helper function
calls and individual memory instructions. It is not a transcription of the
LZ4 algorithm. `decoder_is_artifact` checks the early-return decomposition
against that parsed code; its suffix is extracted from the artifact, not
assumed. The concrete execution proofs likewise execute the extracted bytes.
No shipped C source or Wasm bytes were changed.

The connection still depends on reviewing the binary extractor and the generic
Wasm semantics. There is no proved refinement from this interpreter to a
separately formalized official WebAssembly semantics. Unsupported instructions
fail closed, and the proofs establish successful executions only within the
supported subset. This is an explicit semantic trust boundary, not something
independent proof-kernel replay removes.

**Reproduction and independent checks**

From this directory run:

```sh
./check.sh
```

It uses the installed offline tools and existing Lake dependencies. It cleans
only this project's build outputs, rebuilds every positive proof, validates the
original Wasm, and checks the extracted bytes. It then:

1. Replays the project's declarations with `leanchecker-paranoid`, using the
   Lean C++ kernel. This shares an implementation with Lean's normal checker;
   it is not counted as the independent implementation.
2. Uses `leanexport` to export the six named theorems and their full dependency
   closure, then checks that closure using the independent Rust kernel
   `nanoda_bin`. The configuration permits only `propext`, `Classical.choice`,
   and `Quot.sound`; all other axioms cause failure. In particular,
   `sorryAx` and compiler-trust axioms are not permitted. The checker prints
   the checked theorem statements, and the driver checks that every requested
   name appears. Proofs use kernel reduction and ordinary proof terms, not
   `native_decide`.
3. Confirms that Lean rejects a source proof of `False` using `True.intro`.
   It deliberately constructs forged `.olean` theorems claiming `False` from
   `True.intro`, and `0 = 1` from reflexivity at 0, with initial kernel checking
   disabled. Both replay kernels must reject both forged proofs. The Rust
   checker must also reject a theorem of `False` using `sorryAx`. These
   negative modules are not imported by the positive proof library.
4. Emits the exact finite cases from the Lean definitions and executes them
   against the original binary embedded unchanged in a Wasmtime WAST script.
   It checks returns, output bytes, preserved input bytes, and adjacent
   destination canaries. It also runs a deliberately wrong expected output
   (`B` instead of `A`) and requires rejection. Runtime comparison does not
   observe reads and does not establish general interpreter equivalence.

Success is exit status zero with the final messages:

```text
CHECK PASSED: artifact-linked partial proofs replayed; all negative controls rejected.
R1, R2, R3 remain unproved in general. Read VERIFICATION.md for the exact scope.
```

Any positive-check failure, an accepted false proof, an incorrect negative-test
diagnostic, an unexpected axiom, or a runtime discrepancy makes the command
fail. This success condition confirms the stated partial results, not full
compliance. Logs, exported proof terms, kernel configurations, checked theorem
statements, WAST tests, and tool binary sizes/hashes are written under
`.lake/verification/`. Proofs are rebuilt rather than accepted from those logs.

**Review and trust size**

Physical source lines and byte counts, including comments, blank lines, and
proof bodies, are used as conservative upper bounds rather than counting only
statement lines:

| Local review component | Lines | Bytes |
| --- | ---: | ---: |
| Generic Wasm parsing and semantics: `Proofs/Wasm.lean` | 211 | 7,768 |
| Format specification: `Proofs/Format.lean` | 52 | 2,285 |
| Early-return statements, definitions, and proofs: `Proofs/Prefix.lean` | 60 | 2,176 |
| Case data, observations, statements, and proofs: `Proofs/Results.lean` | 88 | 3,816 |
| Library root: `Proofs.lean` | 2 | 43 |
| **Entire handwritten mathematical surface** | **413** | **16,088** |
| Binary extractor: `verification/extract.py` | 104 | 3,664 |
| Driver: `verification/check.py` | 101 | 5,373 |
| Runtime cross-check generator: `verification/runtime.py` | 40 | 2,308 |
| Case emitter: `verification/Emit.lean` | 10 | 363 |
| Three negative-control modules | 20 | 608 |
| Entry command: `check.sh` | 4 | 100 |
| **All handwritten verification code** | **692** | **28,504** |

Generated `Proofs/Artifact.lean` adds 13 lines / 6,759 bytes of mechanically
compared data. Review of its numeric byte list is replaced by the exact-byte
comparison and artifact hash check. The six positive theorem statements and
all their local definitions are contained in the mathematical surface above.
The proof bodies need not be trusted once replayed, but are included in these
counts to avoid understating the surface.

The English requirements and format remain necessary interpretation inputs:
`README.md` is 18 lines / 2,872 bytes; `lz4_Block_format.md` is 244 lines /
10,683 bytes; `CHECK.md` is 8 lines / 784 bytes. Lake configuration, manifest,
and toolchain selection add 130 lines / 3,825 bytes of build inputs. The installed Lean core,
kernels, exporter, Python, Wasm tools, operating system, and hardware form the
external foundation; they are not counted as project-specific specifications.
The command records sizes and SHA-256 hashes of the directly invoked tool
binaries in `tools.json`. Mathlib is available as requested but is not imported
by these proofs. The C compiler and C source are not part of the proof's trust
chain because the shipped binary itself is the input.
