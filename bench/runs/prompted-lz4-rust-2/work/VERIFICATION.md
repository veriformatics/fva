**Partial verification: the full requirements R1, R2 and R3 remain unproved. No counterexample to any requirement is established here.** The delivered proofs establish an unrestricted zero-input result and 38 particular executions. They do not establish general correctness of the decoder.

**Results and exact statements.**

| Requirement | Machine-checked result | Remaining gap |
|---|---|---|
| R1 | `Verification.empty_input` for every memory, address and capacity when `n = 0`; `Verification.checked0` through `Verification.checked37` check every recorded read and write for their particular inputs and initial memories. | No invariant proving the memory-access restriction for arbitrary nonempty inputs, capacities, buffer placements or initial memories. |
| R2 | The same 38 concrete theorems include the implication in `checkCase.r2`: if the format parser accepts the end conditions and its content fits, the execution returns its length and produces that content. This implication has a true antecedent in 27 cases. | No completeness proof for all valid blocks, no universal termination argument, and no general proof that the executable format definition is equivalent to the prose specification. |
| R3 | The 38 concrete theorems include `checkCase.r3`: every successful execution in these cases has a parsed sequence decomposition with positive offsets into previous output, the correct length, and the correct output bytes. There are 28 successful cases, including one that violates only the end conditions. | No soundness proof for arbitrary accepted input. |

Here `checkCase.r2` and `checkCase.r3` refer to the local bindings named `r2` and `r3` in [Proofs/Results.lean](Proofs/Results.lean), not additional theorem names. Cases with insufficient output capacity do not satisfy R2's antecedent. Error cases make R3's implication vacuous; their return values and access traces are still checked.

The exact unrestricted theorem is in [Proofs/Results.lean](Proofs/Results.lean):

```lean
theorem Verification.empty_input (src dst cap : Nat) (mem : Wasm.Memory) :
    (Verification.execute src dst 0 cap mem).status = .done 4294967295 ∧
    (Verification.execute src dst 0 cap mem).accesses = [] ∧
    (Verification.execute src dst 0 cap mem).mem = mem
```

`Wasm.Memory` is `Nat → Nat`. `4294967295` is the unsigned representation of the Wasm `i32` return value `-1`. The theorem applies, in particular, to every admissible README buffer arrangement with `n = 0`. It proves that there are no memory accesses at all, including below address 131072. Empty compressed input is not a valid block; the valid empty-content block is the single byte `00`.

For **each** integer `i` from 0 through 37, the exact concrete theorem is:

```lean
theorem Verification.checkedi :
  Verification.checkCase Verification.casei = true
```

Substitute the decimal index for `i` in both identifiers. Its declaration and complete concrete input, expected output, addresses and capacity are in `Proofs/Concrete/Casei.lean`. These are individual closed theorems, **not** a theorem quantified over inputs. `checkCase` is defined completely in [Proofs/Results.lean](Proofs/Results.lean); it checks address admissibility, the expected return, output bytes, all access events, the expected format-validity classification, and the R2/R3 implications. The corresponding cases are:

| Index/file | Exact theorem type (in namespace `Verification`) | Case | Format-valid | Expected return |
|---:|---|---|:---:|---:|
| [0](Proofs/Concrete/Case0.lean) | `checked0 : checkCase case0 = true` | empty-input | no | -1 |
| [1](Proofs/Concrete/Case1.lean) | `checked1 : checkCase case1 = true` | empty-content | yes | 0 |
| [2](Proofs/Concrete/Case2.lean) | `checked2 : checkCase case2 = true` | ignored-final-match-nibble | yes | 0 |
| [3](Proofs/Concrete/Case3.lean) | `checked3 : checkCase case3 = true` | literals-1 | yes | 1 |
| [4](Proofs/Concrete/Case4.lean) | `checked4 : checkCase case4 = true` | literals-2 | yes | 2 |
| [5](Proofs/Concrete/Case5.lean) | `checked5 : checkCase case5 = true` | literals-3 | yes | 3 |
| [6](Proofs/Concrete/Case6.lean) | `checked6 : checkCase case6 = true` | literals-4 | yes | 4 |
| [7](Proofs/Concrete/Case7.lean) | `checked7 : checkCase case7 = true` | literals-7 | yes | 7 |
| [8](Proofs/Concrete/Case8.lean) | `checked8 : checkCase case8 = true` | literals-8 | yes | 8 |
| [9](Proofs/Concrete/Case9.lean) | `checked9 : checkCase case9 = true` | literals-14 | yes | 14 |
| [10](Proofs/Concrete/Case10.lean) | `checked10 : checkCase case10 = true` | literals-15 | yes | 15 |
| [11](Proofs/Concrete/Case11.lean) | `checked11 : checkCase case11 = true` | literals-16 | yes | 16 |
| [12](Proofs/Concrete/Case12.lean) | `checked12 : checkCase case12 = true` | literals-17 | yes | 17 |
| [13](Proofs/Concrete/Case13.lean) | `checked13 : checkCase case13 = true` | literals-32 | yes | 32 |
| [14](Proofs/Concrete/Case14.lean) | `checked14 : checkCase case14 = true` | literals-33 | yes | 33 |
| [15](Proofs/Concrete/Case15.lean) | `checked15 : checkCase case15 = true` | literals-48 | yes | 48 |
| [16](Proofs/Concrete/Case16.lean) | `checked16 : checkCase case16 = true` | literals-280 | yes | 280 |
| [17](Proofs/Concrete/Case17.lean) | `checked17 : checkCase case17 = true` | hot-overlap-1 | yes | 21 |
| [18](Proofs/Concrete/Case18.lean) | `checked18 : checkCase case18 = true` | hot-wild-18 | yes | 26 |
| [19](Proofs/Concrete/Case19.lean) | `checked19 : checkCase case19 = true` | hot-offset-4 | yes | 24 |
| [20](Proofs/Concrete/Case20.lean) | `checked20 : checkCase case20 = true` | overlap-2 | yes | 25 |
| [21](Proofs/Concrete/Case21.lean) | `checked21 : checkCase case21 = true` | copy-8 | yes | 21 |
| [22](Proofs/Concrete/Case22.lean) | `checked22 : checkCase case22 = true` | wild-32 | yes | 69 |
| [23](Proofs/Concrete/Case23.lean) | `checked23 : checkCase case23 = true` | wild-64 | yes | 133 |
| [24](Proofs/Concrete/Case24.lean) | `checked24 : checkCase case24 = true` | extended-match-fill | yes | 306 |
| [25](Proofs/Concrete/Case25.lean) | `checked25 : checkCase case25 = true` | extended-match-overlap | yes | 48 |
| [26](Proofs/Concrete/Case26.lean) | `checked26 : checkCase case26 = true` | relaxed-end-conditions | no | 5 |
| [27](Proofs/Concrete/Case27.lean) | `checked27 : checkCase case27 = true` | zero-offset-cold | no | -1 |
| [28](Proofs/Concrete/Case28.lean) | `checked28 : checkCase case28 = true` | zero-offset-hot | no | -1 |
| [29](Proofs/Concrete/Case29.lean) | `checked29 : checkCase case29 = true` | offset-before-start | no | -1 |
| [30](Proofs/Concrete/Case30.lean) | `checked30 : checkCase case30 = true` | missing-literals | no | -1 |
| [31](Proofs/Concrete/Case31.lean) | `checked31 : checkCase case31 = true` | missing-literal-extension | no | -1 |
| [32](Proofs/Concrete/Case32.lean) | `checked32 : checkCase case32 = true` | missing-offset-byte | no | -1 |
| [33](Proofs/Concrete/Case33.lean) | `checked33 : checkCase case33 = true` | missing-match-extension | no | -1 |
| [34](Proofs/Concrete/Case34.lean) | `checked34 : checkCase case34 = true` | literal-output-too-small | yes | -1 |
| [35](Proofs/Concrete/Case35.lean) | `checked35 : checkCase case35 = true` | match-output-too-small | yes | -1 |
| [36](Proofs/Concrete/Case36.lean) | `checked36 : checkCase case36 = true` | source-at-memory-end | yes | 33 |
| [37](Proofs/Concrete/Case37.lean) | `checked37 : checkCase case37 = true` | destination-at-memory-end | yes | 21 |

[verification/cases.json](verification/cases.json) also contains all input and expected-output bytes in decimal, with addresses and capacities. The mathematical grammar is [Proofs/Format.lean](Proofs/Format.lean): token nibbles, extension bytes, little-endian offsets, sequential overlapping match copies, and separate end conditions. A match offset must be positive and at most the already decoded length. The final token's unused match nibble is ignored. The format definition is a specification, not the implementation being verified.

**Connection to the shipped implementation.**

The artifact is exactly `lz4-flex.wasm`, 7,161 bytes, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

[verification/extract.py](verification/extract.py) checks the size and hash, runs `wasm-tools validate`, disassembles those same bytes with `wasm-tools print`, checks the export/interface, explicit branch targets, fixed memory and initial stack global, and follows the actual call graph from function 7 (`lz4_decompress`). The reachable functions are exactly 1, 2, 7 and 8. It translates every instruction of these functions and the data segment into [Proofs/Artifact.lean](Proofs/Artifact.lean), with no algorithm summaries. Structured void blocks become numeric branch targets; function fallthrough becomes an explicit return. Small named lookup functions represent the resulting instruction table. Unknown instructions cause extraction to fail. Functions used only by the out-of-scope compressor are excluded.

[Proofs/Wasm.lean](Proofs/Wasm.lean) interprets this generated instruction table. It implements unsigned integer operations and wrapping, operand/local/global stacks, labels, calls, little-endian memory operations, bulk copy/fill and traps. Loads, stores and bulk operations record their addresses and sizes. The safety predicate permits low-memory accesses and, above that region, only the reads/writes allowed by R1. Initial concrete memories match fresh module data/zero initialization below 131072; the upper region is filled with byte 90, destination buffers with 165, then the specified input bytes are placed at `src`. Every concrete execution has a 2,000-step fuel limit. A theorem requires an actual return, so a trap or exhausted fuel cannot count as a pass.

This is an instruction-level model extracted from the artifact, not a hand-written Rust/LZ4 implementation model. Nevertheless, the extraction/disassembly bridge and the interpreter's correspondence to WebAssembly are **trusted, not themselves formally verified**. Thus the artifact interpretation is conditional on that bridge. No verified Rust compiler or rebuild equivalence is assumed. The Rust source and shipped Wasm were not modified.

As an additional check of the bridge, both V8 and Wasmtime execute the original binary on all 38 concrete cases and compare return values and every expected output byte. Wasmtime's WAST file embeds the original binary bytes. These runtime checks do not independently observe memory reads or prove that the interpreter is correct on untested instructions/states.

**One command to check all delivered results.** Run from this directory:

```sh
./verification/check.sh
```

It requires the installed Lean/Lake 4.35.0 toolchain, `wasm-tools`, `wasmtime`, Python 3, Node.js, `rg`, and the installed independent checkers `/opt/lean/bin/con-ron` and `/opt/lean/bin/nanoda_bin`. It uses no network and does not rebuild or modify the Rust software. Mathlib remains a Lake dependency; the proofs import only `Init` to keep dependencies smaller. A first build and all replays can take several minutes.

The command regenerates the instruction table and concrete statements, builds the proofs, exports the selected theorems **with their full dependency closure**, audits axioms and target presence, then replays the exported terms with:

- Lean's default C++ kernel, through `leanchecker --from-export`;
- con-ron's independent Rust kernel in `--verified` mode;
- Nanoda's independent Rust kernel with Nat/String extensions and an explicit axiom allowlist.

The full export actually uses `propext` and `Quot.sound`. Only those and `Classical.choice` are allowed as axioms. In particular, `sorryAx`, `Lean.trustCompiler` and arbitrary application axioms are rejected. Concrete proofs use definitional reduction (`rfl`) or proof-producing `decide_cbv`; the zero-input proof uses proof-producing `cbv`. No result is justified by `native_decide`, an SMT oracle, a runtime test or a mere compiler exit code. Imported `.olean` declarations are exported and rechecked too.

The checker calibration is [Proofs/Calibration.lean](Proofs/Calibration.lean). Each kernel must first accept its correct proofs. [verification/exports.py](verification/exports.py) then makes two well-formed, dependency-ordered export fixtures with intentionally false proof claims: `True.intro : False`, and the original proof of `2 + 2 = 4` given the type `2 + 2 = 5`. Each kernel must reject both. The driver checks the exit status **and a type-checking diagnostic**; a parsing error, missing command or timeout is not accepted as successful calibration. Lean and con-ron return 1 for these rejections. Nanoda's type checker asserts `self.def_eq` and returns 101; the driver requires that specific assertion diagnostic. This tests basic rejection, not a general proof of checker soundness.

Detailed exports, runtime fixtures, positive replay logs and negative replay logs are written under `verification/.build/`. Nanoda may report an auxiliary pretty-printer error while returning success with no type-checker errors; its exit status and the independent replay verdicts determine acceptance. Success ends with exactly:

```text
PASS: partial results checked; universal R1/R2/R3 remain UNPROVED (see VERIFICATION.md)
```

Any other outcome is not a successful verification run. That PASS certifies the limited results above, not all README requirements.

**Review surface and trust.** A reviewer must assess the formal statements and their definitions, the prose-to-format interpretation, the instruction semantics and artifact bridge, and the checking driver/audit. The proof terms and concrete reductions are checked independently. Standard dependent type theory, the allowed foundational axioms, the kernel implementations, OS/tool execution, Python's hash implementation and `wasm-tools` disassembly remain trusted foundations. The calibration does not eliminate these assumptions.

Current source sizes (physical lines, including comments and blanks; UTF-8 bytes) are:

| Component | Lines | Bytes |
|---|---:|---:|
| Custom instruction semantics, format and result predicates/statements (`Proofs/Wasm.lean`, `Format.lean`, `Results.lean`) | 280 | 11,280 |
| Artifact extractor, checking driver and export audit/mutation script | 237 | 11,486 |
| Additional case generation, runtime cross-checking, size reporter, calibration and root imports | 148 | 7,943 |
| Generated instruction definitions, concrete statements/input data and imports | 707 | 87,391 |

The first row is not the whole transitive mathematical dependency set: it also depends on the generated instruction definitions and Lean's standard-library definitions. `verification/sizes.py`, invoked by the check command, reports the full exported dependency-record counts and byte size as well as all custom source sizes. Generated concrete theorem files use the same small predicate; proof bodies are one tactic each. Generated instruction lookup definitions are data tied to the hash through the trusted extractor, not extra assumptions about what the decoder does. No claim is made that a small custom model removes the need to review its meaning.

A completed run on 2026-10-29 exited **0** with that PASS line. All 39 required theorem declarations passed all three kernels; each kernel rejected both false fixtures; both runtimes agreed on all 38 original-artifact executions. The full export is **570,896,189 bytes**, including proof terms. Its declaration-record counts are **793 definitions, 595 theorems, 2 axioms, 1 opaque declaration, 4 quotient records and 73 inductive-block records** (constructors and recursors occur inside those blocks). These counts include standard-library and proof-support declarations, not just the 39 required results. Con-ron reports 1,468 accepted declaration records and Nanoda reports 1,660 checked declarations under their respective counting conventions. The large proof export need not be reviewed as source; its proofs are replayed. The custom definitions, generated instruction definitions and concrete statements remain part of the stated review surface.
