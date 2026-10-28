# Verification of lz4-c.wasm

**The full requirements R1–R3 remain unproved. No counterexample was found.**
The results below are partial: 12 exact calls have machine-checked return values,
output bytes and access restrictions, and a further theorem covers rejection of
zero-length compressed input for all 32-bit pointers and capacities. A PASS from
FVA applies to these stated claims, not to all the requirements in README.md.

The external FVA run completed with **`fva trust: PASS`** (exit 0). It found
all 13 claims proven and the artifact link matching. `leanchecker` accepted the
export in 451 seconds; the independent `con-leche` kernel accepted it in 301
seconds. FVA reports **101 review code lines**: 53 in `Proofs.Spec` and 48 in
`Proofs.MemorySpec`. The Wasmtime cross-check passed all 12 concrete cases.

Canary results must be read with FVA's pinned known-acceptance policy: of 72
known-false exports, `leanchecker` rejected 71 and accepted one listed as a known
acceptance; `con-leche` rejected 69, declined three and accepted none. Neither
kernel crashed or timed out on a canary. Thus PASS does not mean every kernel
rejected every canary. The full evidence is in `verification/trust.log` and the
pinned policies in `fva/trust/canaries/{set,known}.tsv`.

**Requirement coverage.**

| Requirement | Established result | What remains open |
| --- | --- | --- |
| R1 | For each of the 12 calls below, every configuration reachable under FVA's Wasm `Step` semantics satisfies the byte-access specification in `Proofs/MemorySpec.lean`. This includes accesses inside the C copy helpers and speculative copies beyond the logical decoded prefix. | Arbitrary compressed bytes, lengths, capacities, placements and caller memory contents. No general decoder-loop invariant or universal R1 theorem was proved. |
| R2 | Exact returned length and every decoded byte for the eight valid-block examples below (all successful examples except `zero_offset`). Empty output, extension bytes, overlapping matches and both ends of memory are exercised. | Correctness for every valid independent block. There is no formal general LZ4-format relation or proof of its correspondence to the format document. The classification of the explicit examples as valid blocks is a small manual reading of that document, not a machine-checked format-membership theorem. |
| R3 | Exact returned length and output for nine successful examples, including the allowed offset-zero case with a destination initially filled with 0xA5. Three malformed/undersized examples are proved to return the stated negative codes. | The implication from every nonnegative return to a valid sequence decomposition, permissible offsets and correct decoded content. No universal converse, parser-completeness proof or failure witness was established. |

The missing proofs would need invariants relating compressed-input position,
length-extension accumulation, output position, offset validation and overlapping
copy operations across the compiled decoder's loops and helper calls. Concrete
execution certificates do not supply those invariants. The finite input and
memory bounds do not make exhaustive enumeration practical.

**Exact statements and locations.**

Each row is the exact theorem declaration `theorem <name>_holds : <name>` in
`Proofs/Cases.lean`, in namespace `Proofs`. Its claim in `Proofs/Spec.lean` is
exactly `CheckedCase src dst input capacity result output`, with the arguments
listed below. Numbers in byte lists are decimal; `a^n` in this table abbreviates
`List.replicate n a`, and `++` denotes list concatenation. These abbreviations
are only for this table; the Lean file contains the precise expressions.

| Claim `<name>` | src | dst | input | capacity | result | output |
| --- | ---: | ---: | --- | ---: | ---: | --- |
| `empty_zero` | 131072 | 262144 | `[0]` | 0 | 0 | `[]` |
| `empty_room` | 131072 | 262144 | `[0]` | 1 | 0 | `[]` |
| `one_literal` | 131072 | 262144 | `[16,97]` | 1 | 1 | `[97]` |
| `extended_literals` | 131072 | 262144 | `[240,0] ++ 97^15` | 15 | 15 | `97^15` |
| `overlap_match` | 131072 | 262144 | `[19,97,1,0,80,98,99,100,101,102]` | 13 | 13 | `97^8 ++ [98,99,100,101,102]` |
| `extended_match` | 131072 | 262144 | `[31,97,1,0,0,80,98,99,100,101,102]` | 25 | 25 | `97^20 ++ [98,99,100,101,102]` |
| `zero_offset` | 131072 | 262144 | `[19,97,0,0,80,98,99,100,101,102]` | 13 | 13 | `[97] ++ 0^7 ++ [98,99,100,101,102]` |
| `source_at_end` | 2097150 | 131072 | `[16,97]` | 1 | 1 | `[97]` |
| `destination_at_end` | 131072 | 2097151 | `[16,97]` | 1 | 1 | `[97]` |
| `reject_no_input` | 131072 | 262144 | `[]` | 1 | -1 | `[]` |
| `reject_zero_capacity` | 131072 | 262144 | `[16,97]` | 0 | -1 | `[]` |
| `reject_past_offset` | 131072 | 262144 | `[19,97,2,0,80,98,99,100,101,102]` | 13 | -5 | `[]` |

`CheckedCase`, fully defined in `Proofs/Spec.lean`, asserts:

1. Both buffers satisfy the README's numerical bounds and non-overlap condition.
2. The module has a fresh instance under every host semantics.
3. From **every** fresh instance, both buffers fit. After filling the complete
   destination with byte 165 (0xA5), then writing `input` to `src`, every execution
   of the exported `LZ4_decompress_safe` terminates without trapping, returns
   exactly the given `i32` result and has exactly `output` in the destination
   prefix of length `output.length`.
4. At every reachable configuration of that call, each pending load/store byte
   is below 131072 or in a permitted buffer: reads may use source or destination;
   writes may use destination. The access definition also covers bulk memory
   instructions. The actual artifact uses scalar loads/stores and copy helpers.

For rejection examples, `output = []` places no restriction on partial output.
For successful examples its length is exactly the nonnegative returned length.
Negative results are 32-bit two's-complement values. Initial memory outside the
specified writes is the module's freshly initialized memory. These claims do
not quantify over arbitrary prior caller writes or previous invocations.

The additional declaration in `Proofs/General.lean` is exactly:

```lean
theorem zero_size_general_holds : zero_size_general
```

Its full statement, defined in `Proofs/Spec.lean`, is:

```lean
def zero_size_general : Prop :=
  Instantiable Lifted.module ∧
  ∀ (src dst capacity : BitVec 32) H s inst, Instance Lifted.module H s inst →
    CallReturns H s inst "LZ4_decompress_safe"
      [.i32 src, .i32 dst, .i32 0, .i32 capacity]
      (fun s' vs => s' = s ∧ vs = [.i32 (-1)])
```

Thus zero compressed bytes always produce -1 and leave the entire store
unchanged, including memory, even for pointer/capacity values outside the README
domain. This is a universal boundary theorem; unchanged final memory alone is
not a theorem that no reads or temporary writes occurred.

**Connection to the shipped bytes.**

All 13 claims mention `Proofs.Lifted.module`, decoded from the unchanged
`lz4-c.wasm`: 8,469 bytes, SHA-256
`8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`.
`Proofs/Lifted.lean` was generated by:

```sh
lake exe fva lift lz4-c.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

Its `decode_eq` theorem binds the decoded module to the packed byte numeral.
FVA checks the numeral, length, relative source path and generated-file contents
against the actual file. The proofs execute this decoded module, not a rewrite
of the C algorithm. `Proofs/Proof.lean` proves instantiability and uniqueness of
the fresh instance, including its initialized global and 64-byte data segment;
it then applies FVA's `runDet` total-correctness theorem to the concrete calls.
`Proofs/Trace.lean` proves the finite access checker implies the `Throughout`
property for **all** semantic executions, using uniqueness of each certified
step. Fuel is a certificate-construction bound, not an assumption in a claim.
The C sources and the build script are not assumptions of these proofs, and the
artifact was not rebuilt or modified.

**Reproduction, from this directory, without network access.**

```sh
bash verification/check.sh
```

The script checks the artifact hash, runs `lake build`, makes an external copy
of the supplied FVA package, configures that copy to use the existing offline
Lake dependency directory, builds FVA there and runs:

```sh
/tmp/<external-FVA-directory>/.lake/build/bin/fva trust . \
  --spec-module Proofs.Spec --root-module Proofs \
  --surface-budget 200 --kernel-limit 1200
```

The external package's Lean sources are unchanged; only its Lake package-location
metadata is adjusted. The verdict is written to `verification/trust.log`. Success
requires exit status 0 and `fva trust: PASS`, with all 13 claims proven, artifact
link checks passing, and accepting kernel replays with passing canaries. The
script then independently runs all 12 examples in Wasmtime by embedding the
original binary in a WAST script and importing its actual memory and export.
Its success line begins `PASS: 12 cases`. It checks every expected output byte,
not just the return codes. This runtime check is supplementary evidence, not a
replacement for the proofs or a full-requirement test.

Individual checks can also be run with:

```sh
lake build
python3 verification/check_wasmtime.py
```

A fresh proof build can take several minutes, and independent kernel replay
can take several more (about eight minutes in this run). `lake build` must report success
without errors. No `sorry`, custom axioms, `native_decide` or `bv_decide` are used.
The exact FVA replay outcome and review-surface count are in `verification/trust.log`.

**Review and trust surface.**

The project-specific meaning is in `Proofs/Spec.lean` (94 physical lines, 4,840
bytes) and `Proofs/MemorySpec.lean` (62 physical lines, 2,820 bytes). In particular,
a reviewer must check that the access specification enumerates the relevant
load/store byte ranges and follows the active instruction through labels and
frames as intended. The relationship of the explicit byte lists to the LZ4
format document is also a human review obligation. FVA reports its own count of
non-comment code lines for these files.

The proof files (`Proofs/Proof.lean`, `Proofs/Trace.lean`, `Proofs/Cases.lean`,
`Proofs/General.lean`) need not be trusted as an implementation or manually read:
Lean checks their terms. The generated lift need not be manually audited because
of its decoder theorem and FVA's link check. The reproduction script
`verification/check.sh` has 27 lines / 1,198 bytes; the supplementary runtime
checker `verification/check_wasmtime.py` has 68 lines / 3,173 bytes. Read them if
relying on their orchestration or Wasmtime observations; the runtime script is
not an assumption of any Lean theorem.

The supplied FVA specification directory contains 23 Lean files / 3,606 physical
lines / 161,903 bytes. Its trust-collection directory has 4 files / 887 lines /
40,918 bytes; its CLI/tool directory has 13 files / 2,894 lines / 139,610 bytes
(these totals include tools beyond the ones used here). The complete supplied
`fva/FVA` Lean source tree is 127 files / 24,102 lines / 1,102,440 bytes, including
proofs checked by the kernels. These are base-package sizes, separate from the
project-specific review surface above.

The remaining base is FVA's pinned Wasm syntax, binary grammar, instantiation,
execution and numeric specifications and claim definitions; its verified decoder,
stepper and checker proofs; FVA's fact collection, source/link checks, exporter,
replay orchestration and canaries; the Lean and independent replay kernels; and
the supplied Lean 4.35 / Mathlib v4.35.0 installation and build toolchain. The
FVA verdict prints this trust boundary. These partial results do not constitute
a verification of the complete LZ4 decoder or of all R1–R3.
