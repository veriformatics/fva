# Verification results

**INCOMPLETE: none of R1, R2, or R3 has been proved or refuted in full.**
There are twelve kernel-checked examples about the shipped Wasm. They are limited
results, not a verification of the three universal requirements. No counterexample
to those requirements was found. The C source and the shipped artifact were not changed.

## Requirements and remaining obligations

| Requirement | Result | What is missing |
| --- | --- | --- |
| R1 | Unresolved. The examples preserve the compressed input and two output guard bytes. | A proof about every read and write on every execution, for all permitted buffer addresses, sizes, and input bytes. Final guard values do not establish access safety: they detect neither reads nor temporary writes that are restored. No access-trace safety theorem is supplied. |
| R2 | Unresolved. Concrete output and return values are proved for empty, literal, overlapping-match, extended-length, and shortcut-path examples below. | A formal definition of valid independent LZ4 blocks, and a proof by induction covering every sequence, length extension, offset, buffer placement, and sufficient capacity. The format validity of the successful examples is explained by inspection of the supplied format document, not a separately formalized format predicate. |
| R3 | Unresolved. Successful examples have the listed contents; three malformed inputs and one undersized destination return negative errors. The offset-zero example produces zeros. | A proof that **every** nonnegative return admits the required sequence decomposition and decoded content, with only the two stated exceptions. Negative-return examples do not establish this implication. Offset zero is an allowed departure, not a counterexample. |

The outstanding work is the general proof, not an unavailable dependency. FVA
supplies Wasm semantics and execution soundness, but no LZ4 format relation or
invariants connecting this decoder's loops and optimized copies to that relation.
The finite-execution certificate method used here does not establish those symbolic
loop invariants or a format simulation. I did not construct that general proof.
No source-level model is substituted for these obligations.

## Exact machine-checked statements

Every theorem below is in `Proofs/Proof.lean`; its proposition is defined in
`Proofs/Spec.lean`. Here are the exact theorem statements:

```lean
theorem empty_zero_holds : empty_zero
theorem empty_positive_holds : empty_positive
theorem no_input_holds : no_input
theorem literal_holds : literal
theorem overlap_holds : overlap
theorem literal_extension_holds : literal_extension
theorem match_extension_holds : match_extension
theorem zero_offset_holds : zero_offset
theorem bad_offset_holds : bad_offset
theorem truncated_holds : truncated
theorem too_small_holds : too_small
theorem shortcut_holds : shortcut
```

All names are in namespace `Proofs`. Each proposition is exactly
`Example input capacity ret output` with the following arguments. Byte strings
are hexadecimal; `[]` is an empty list. Negative returns denote the corresponding
32-bit two's-complement `BitVec 32` values.

| Proposition | Input bytes | Capacity | Signed return | Output bytes |
| --- | --- | ---: | ---: | --- |
| `empty_zero` | `00` | 0 | 0 | `[]` |
| `empty_positive` | `00` | 1 | 0 | `[]` |
| `no_input` | `[]` | 1 | -1 | `[]` |
| `literal` | `10 41` | 1 | 1 | `41` |
| `overlap` | `18 41 01 00 50 42 43 44 45 46` | 18 | 18 | thirteen `41` bytes, then `42 43 44 45 46` |
| `literal_extension` | `f0 00`, then `41` through `4f` | 15 | 15 | `41` through `4f` |
| `match_extension` | `1f 41 01 00 00 50 42 43 44 45 46` | 25 | 25 | twenty `41` bytes, then `42 43 44 45 46` |
| `zero_offset` | `08 00 00 50 42 43 44 45 46` | 17 | 17 | twelve `00` bytes, then `42 43 44 45 46` |
| `bad_offset` | `08 01 00 50 42 43 44 45 46` | 17 | -4 | `[]` |
| `truncated` | `10` | 1 | -2 | `[]` |
| `too_small` | `20 41 42` | 1 | -2 | `[]` |
| `shortcut` | `80`, `41` through `48`, `08 00 c0`, `61` through `6c` | 32 | 24 | `ABCDEFGHABCDabcdefghijkl` (ASCII) |

For error cases, empty `output` means that no destination content is asserted;
it does not assert that the destination is unchanged. All cases also assert input
and guard preservation. Here is the exact common proposition, with the same opens
as the specification:

```lean
def Example (input : List UInt8) (capacity : Nat) (ret : BitVec 32)
    (output : List UInt8) : Prop :=
  ∀ H, ∃ s inst, Instance Lifted.module H s inst ∧
    Fits s 131072 input.length ∧ Fits s 262143 (capacity + 2) ∧
    CallReturns H ((s.withBytes 262143 (List.replicate (capacity + 2) 165)).withBytes
      131072 input) inst "LZ4_decompress_safe"
      [.i32 131072, .i32 262144, .i32 (BitVec.ofNat 32 input.length),
        .i32 (BitVec.ofNat 32 capacity)]
      (fun s' vs => vs = [.i32 ret] ∧ ∃ mem, s'.mems[0]? = some mem ∧
        (List.range output.length).map (fun k => mem.byte (262144 + k)) = output ∧
        mem.byte 262143 = 165 ∧ mem.byte (262144 + capacity) = 165 ∧
        (List.range input.length).map (fun k => mem.byte (131072 + k)) = input)
```

Thus the examples quantify over every host semantics and prove that every
execution from the exhibited fresh instance terminates, never traps, and satisfies
the postcondition. They use fixed addresses and an initialized destination filled
with `a5` (165), including guard bytes immediately before and after its capacity.
The fresh instance is **existential**, not universally quantified over all fresh
instances or caller memory contents. Its initialization is proved using FVA's
`instantiate_sound`; the run certificates use `must_returned_of_runDet`.
Fuel bounds are proof-construction parameters, not assumptions in these statements.

For the nonempty successful format examples, matches use offset one or eight,
refer only to already decoded bytes, and satisfy the end-of-block restrictions.
The offset-zero example deliberately exercises R3's exception. The extended-length
examples include the mandatory zero byte when the initial length field is 15.

## Binding to the shipped artifact

The subject is exactly `lz4-c.wasm`, 8,469 bytes, SHA-256
`8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`.
`Proofs/Lifted.lean` was generated by:

```sh
lake exe fva lift lz4-c.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

Its byte numeral and decoded module are connected by this kernel-checked theorem:

```lean
theorem Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len =
    .ok Proofs.Lifted.module
```

FVA's trust check compares that numeral, its byte count, its generated file, and the
actual artifact. The example proofs execute the lifted module, including its real
initializers, data segment, function exports, and memory helpers. They do not
execute a rewrite of the C source. The separate runtime checks instantiate the
original artifact in wasmtime and import its memory and decoder into a harness.

## Reproduction

From this directory, with the installed offline dependencies:

```sh
bash verification/check.sh
```

The script runs `lake build`, the twelve independent wasmtime examples, rebuilds
FVA outside the judged project using the already installed packages, and runs:

```sh
"$verifier_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --json > verification/trust.json
```

Success means exit status zero, twelve runtime `PASS` lines, a JSON verdict of
`"pass"` with no issues, and the final message explicitly limiting that verdict to
the finite examples. The JSON records the artifact link, each proved claim, kernel
replay and known-false canary results, and the review surface. A pass here does
**not** certify R1, R2, or R3. For the Lean results alone, run `lake build`; for runtime
checks alone, run `python3 verification/examples.py`. Runtime checks are not proofs.
The script uses a temporary verifier copy and does not need network access.

## Review and trust

The requirements are in `README.md` (18 physical lines, 2,872 bytes), and their
format reference is `lz4_Block_format.md` (244 lines, 10,683 bytes). Their prose
must be compared with the formal statements; no machine-checked equivalence
between that prose and a general LZ4 specification is claimed.

Read `Proofs/Spec.lean` (72 physical lines, 3,490 bytes), especially the quantifiers
and `Example` postcondition, and compare its concrete bytes with the format document
and the table above. This is the project-specific statement surface. The generated
`Proofs/Lifted.lean` is 67 physical lines, 135,649 bytes; its generation and byte link
are checked by FVA, so it is not a manually trusted source model.

`Proofs/Proof.lean` is 145 lines, 6,397 bytes. Its helper checker definitions are
used only to construct proofs: their soundness is proved, not assumed. The Lean
kernel checks their connection to the stated propositions. There are no `sorry`,
custom axioms, `native_decide`, or edits to FVA. The proof file need not be trusted
by inspection.

The runtime harness generator `verification/examples.py` is 62 lines, 3,137 bytes;
read it if relying on the runtime results. `verification/check.sh` is the orchestration
script (37 lines, 1,475 bytes), not an additional mathematical assumption.
FVA reports 40 project-specific code lines, all in `Proofs.Spec`.

The shared base is FVA's pinned specification of Wasm binary decoding, initialization,
execution, memory, host behavior and claims, together with its trust/check orchestration.
Its verified implementation and soundness theorems are kernel checked. Residual trust
includes Lean 4.35.0, Mathlib v4.35.0 and its standard logical axioms, the compiler and
runtime used to run the checking tools, file/link checking and orchestration, and the
external kernels and their canaries. The runtime examples additionally rely on
Python, wasm text parsing, and wasmtime; the Lean proofs do not rely on those tests.

For a concrete inventory of the shared base, `fva/FVA/Spec/` contains 23 Lean files,
3,606 physical lines and 161,903 bytes; `fva/FVA/Trust/` contains four files, 887 lines
and 40,918 bytes; `fva/FVA/Tool/` contains thirteen files, 2,894 lines and 139,610 bytes.
These totals include unused specifications and tools as well as the ones these
proofs need; they are inventory sizes, not extra project-specific review lines.
The claim vocabulary is in `fva/FVA/Spec/CAbi.lean` and `fva/FVA/Spec/Claims.lean`.

## Recorded audit

On 2026-10-28, `lake build` succeeded and all twelve runtime examples passed.
FVA 0.1.0 was rebuilt in `/tmp/fva-lz4-verifier` from the unchanged vendored
sources and run outside the judged project. `verification/trust.json` records:

- Verdict `pass`, zero issues, twelve claims with twelve proved theorems.
- Both `leanchecker` and the independent `con-leche` accepted the export,
  including `Proofs.Lifted.decode_eq`.
- Exact bytes, length, generated lift, and decoding theorem all matched.
- Project review surface: 40 code lines, entirely in `Proofs.Spec`.
- Of 72 known-false canaries, `leanchecker` rejected 71 and accepted its documented
  replaced-prelude canary; `con-leche` rejected 69 and declined three. FVA's
  documented cross-kernel coverage rules passed with no checker or prelude issue.
- Each example theorem's axiom closure is exactly
  `propext`, `Classical.choice`, and `Quot.sound`.

This is a successful audit of the stated finite examples. **The overall README
requirements remain unresolved.**
