# Verification result: incomplete

**None of R1, R2, or R3 has been proved in full or refuted.** No counterexample was established. The results below are machine-checked partial results about the shipped Wasm, not a certification that it satisfies the README. In particular, passing the finite examples must not be interpreted as proving R2 or R3.

## Requirement-by-requirement results

| Requirement | Result and remaining obligation |
| --- | --- |
| R1 | Partial postcondition proved for `n = 0`: the call returns `-1` and preserves the entire store, after arbitrary caller writes and for all pointers and capacities. This does **not** prove absence of reads, even for that case. No general theorem constraining every load and store to the specified buffers was obtained. |
| R2 | Exact return values and destination bytes proved for the successful concrete cases below, including literals, an extended literal length, overlapping and nonoverlapping matches, and the fast path. No theorem covers all valid independent blocks, placements, capacities, and initial destination contents. |
| R3 | The concrete malformed/undersized cases below are proved to return `-1`. Successful examples are proved to have the stated lengths and bytes, with lengths within capacity. No general implication from a nonnegative return to an LZ4 sequence decomposition was proved. |

The missing work is substantial: a formal LZ4 format/decompression relation, invariants relating it to the compiled decoder's loops and memory, and access-trace invariants for the exact buffer bounds. There is no general LZ4 parser/model hidden in the proofs. A symbolic proof attempt for a larger input family exceeded the environment's memory limit; it is not included as a result. Neither Rust's safe-decode feature nor Wasm's linear-memory bounds is being used as a substitute for R1.

## Exact checked statements

The three top-level theorem statements, in `Proofs/Proof.lean`, are:

```lean
theorem Proofs.initializes_holds : Proofs.initializes
theorem Proofs.empty_input_preserves_store_holds : Proofs.empty_input_preserves_store
theorem Proofs.concrete_examples_holds : Proofs.concrete_examples
```

Their complete definitions are in `Proofs/Spec.lean`, including `Example`, `examples`, and `ExampleCorrect`. That file is the authoritative statement, including all quantifiers and constants.

* `initializes` is exactly `Instantiable Proofs.Lifted.module`: successful fresh initialization exists under every host semantics. This prevents the other claims from being vacuous because the artifact cannot instantiate.
* `empty_input_preserves_store` conjoins instantiability with: for every host semantics, every fresh instance, every `src`, `dst`, and `cap : BitVec 32`, every `p : Nat`, and every `bytes : List UInt8`, calling `lz4_decompress(src, dst, 0, cap)` in `s.withBytes p bytes` always terminates without trapping, returns `[.i32 4294967295]` (signed `-1`), and leaves the entire store equal to `s.withBytes p bytes`. There are no pointer, capacity, or caller-write-size premises in this partial theorem.
* `concrete_examples` is exactly `∀ e ∈ examples, ExampleCorrect e`. For each listed input, `src = 131072`, `dst = 262144`, and `n = input.length`. The theorem proves disjointness/range bounds, successful initialization with room for both buffers, and the specified total, nontrapping call result from every fresh instance after writing the input. It checks every byte of the stated output. On success it also checks `result = output.length ≤ cap`. Negative cases specify no destination contents.

`CallReturns` and `Must` are FVA's total-correctness predicates: these statements cover every execution permitted by the semantics, not merely one execution. The concrete proofs use a 10,000-step computational witness; **fuel is not a premise or limitation of these theorem statements**. Supporting proofs in `Proofs/InitTrace.lean`, `InitRun.lean`, `Instantiation.lean`, `Determinism.lean`, and `Execution.lean` establish initialization and uniqueness of the fresh instance. `ConcreteRuns.lean`, `RunCheck.lean`, and `Samples.lean` connect kernel-evaluated runs to the semantic postconditions.

### Concrete cases

All numbers in the input column are hexadecimal bytes. `a`, `b`, etc. in the output column denote ASCII bytes; repetition counts are exact. These are the 16 entries of `Proofs.examples`, in order.

| # | Input bytes | cap | Signed return | Checked destination prefix |
| --- | --- | ---: | ---: | --- |
| 0 | empty byte string | 0 | -1 | unspecified |
| 1 | `00` | 0 | 0 | empty |
| 2 | `50 61 62 63 64 65` | 5 | 5 | `abcde` |
| 3 | `f0 00` followed by 15 × `61` | 15 | 15 | 15 × `a` |
| 4 | `13 61 01 00 50 62 63 64 65 66` | 13 | 13 | 8 × `a`, then `bcdef` |
| 5 | `10 61 01 00 e0` followed by 14 × `62` | 64 | 19 | 5 × `a`, then 14 × `b` |
| 6 | `40 61 62 63 64 04 00 80` followed by 8 × `65` | 64 | 16 | `abcdabcd`, then 8 × `e` |
| 7 | `f0` | 64 | -1 | unspecified |
| 8 | `f0 ff` | 64 | -1 | unspecified |
| 9 | `20 61` | 64 | -1 | unspecified |
| 10 | `10 61 01` | 64 | -1 | unspecified |
| 11 | `10 61 00 00 00` | 64 | -1 | unspecified |
| 12 | `10 61 02 00 00` | 64 | -1 | unspecified |
| 13 | `1f 61 01 00` | 64 | -1 | unspecified |
| 14 | `50 61 62 63 64 65` | 4 | -1 | unspecified |
| 15 | `13 61 01 00 50 62 63 64 65 66` | 7 | -1 | unspecified |

The LZ4 interpretation of these examples is for a human to compare with `lz4_Block_format.md`; the formal claim directly states their input/output behavior. No theorem states that the example list exhausts any of R1–R3.

The concrete-example claim starts from fresh instances with only the specified input written by the caller. It does not quantify over arbitrary prior call histories or arbitrary initial destination contents.

## Binding to the shipped artifact

The subject is the **unchanged** `lz4-flex.wasm`: 7,161 bytes, SHA-256

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

`Proofs/Lifted.lean` was generated by:

```sh
lake exe fva lift lz4-flex.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It contains the exact bytes, their length and source path, and the decoded module. Its kernel-checked binding theorem is:

```lean
Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len =
    Except.ok Proofs.Lifted.module
```

The call proofs use that module's actual exported function 7, not a Rust-source model, recompiled binary, replacement implementation, or hand-written decoder. FVA's link check separately compares the numeral to the current artifact file. The Rust compiler and correspondence of the vendored Rust sources to the binary are not premises of these behavior proofs.

## Reproduction

From this directory, with the supplied offline dependencies and tools:

```sh
python3 scripts/check.py
```

This checks the byte count and SHA-256, runs `lake build`, generates and runs the Wasmtime cases, builds the supplied FVA verifier in a separate temporary tree, and invokes its `trust` command with `--spec-module Proofs.Spec --root-module Proofs`. It writes the trust report to `verification/trust.txt`. The copied verifier uses the already installed package directory; no downloads are needed. The project copy of FVA is not modified.

Success requires exit status 0, successful Lean builds, `Wasmtime: all 16 cases passed.`, and `fva trust: PASS`. The script's final line deliberately says `PARTIAL CLAIMS CHECKED. Full R1, R2, and R3 remain unproved.` FVA's PASS applies only to the three explicitly stated partial claims. Any build, replay, link, canary, or runtime failure makes the script fail.

The final run of that command exited **0**. `verification/trust.txt` records **PASS** for exactly those three claims, acceptance by `leanchecker` (493 seconds) and the independent `con-leche` kernel (404 seconds), a matching artifact link, and a review surface of **51 code lines** in `Proofs.Spec`.

For the 72 known-false checker tests, Lean's checker rejected 71 and accepted the one documented replaced-prelude case; `con-leche` rejected 69, declined 3, and accepted none. There were no crashes or timeouts. FVA's supplied `known.tsv` explicitly records Lean's official-prelude assumption; the independent checker and FVA's prelude check guard that case. These counts, including the known acceptance and declines, are preserved in the report.

Individual checks can also be run as follows:

```sh
sha256sum lz4-flex.wasm
lake build
lake env lean --run scripts/runtime.lean /tmp/lz4-cases.wast
wasmtime wast -C cache=n /tmp/lz4-cases.wast
```

For trust checking, use the external verifier prepared by `scripts/check.py`, or an independently installed FVA 0.1.0 built from the same pinned base:

```sh
/path/to/external/fva trust . --spec-module Proofs.Spec --root-module Proofs
```

The supplementary Wasmtime harness embeds the artifact bytes verbatim, instantiates it freshly for each case, fills the caller region with `0xa5`, writes the case input, and checks returns, output bytes, source preservation, and final bytes outside the destination capacity. These are executable checks, not proofs about all inputs or about read accesses. Final-memory equality also does not rule out transient writes later restored.

## Review and trust surface

Read `Proofs/Spec.lean` for the exact meaning and limited coverage of the claims. FVA's report gives the computed review surface and axiom/replay/link results. The scripts are also reviewable if relying on their orchestration or supplementary runtime evidence. Physical sizes below include comments and blank lines:

| Item | Size / role |
| --- | --- |
| `Proofs/Spec.lean` | 76 lines, 3,832 bytes; claim definitions and finite example data. |
| `README.md` | 18 lines, 2,402 bytes; requirements being assessed. |
| `lz4_Block_format.md` | 244 lines, 10,683 bytes; intended format, not formalized completely here. |
| `scripts/check.py` | 64 lines, 2,749 bytes; orchestration and isolated verifier preparation. |
| `scripts/runtime.lean` | 49 lines, 2,719 bytes; supplementary Wasmtime harness generator. |
| FVA `FVA/Spec/**/*.lean` | 3,606 physical lines; reviewed semantics, claim vocabulary, and trust specifications. |
| FVA `FVA/Tool/**/*.lean` and `FVA/Trust/**/*.lean` | 3,781 physical lines; supplied tooling, collection, link checking, replay/canary orchestration. |
| FVA `trust/canaries/set.tsv` and `known.tsv` | 195 lines / 20,387 bytes and 3 lines / 353 bytes; pinned checker tests and known checker acceptances. |

The logical trust base also includes Lean 4.35.0's kernel and the independent replay kernel, the supplied compiler/tool binaries and operating environment, and Mathlib v4.35.0 at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. FVA's verified implementation connects its decoder/stepper to the reviewed specifications. Generated lifting code and project proof files need not be trusted as hand-written models: their proofs are checked and replayed. No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used in the project proofs.

The three claim proofs use the permitted standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, as the trust report states. The reproduction script relinks the supplied prebuilt FVA objects outside the project; a separately trusted FVA installation can instead run the direct trust command above.
