# Verification report

**Status: partial verification. R1, R2, and R3 have neither been proved in full nor refuted.** The results below are two general theorems about entry paths in an extracted Wasm model, 36 kernel-checked executions of that model, and 36 corresponding executions of the exact shipped binary in Wasmtime. Passing these checks does not establish the universal README requirements.

The artifact remains `lz4-c.wasm`, 8,469 bytes, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

1. Results for each requirement

| Requirement | Machine-checked results | What remains unproved |
| --- | --- | --- |
| R1 | `zeroCapacity` and `emptySource` below establish unchanged memory and the complete read traces on these paths, for arbitrary initial memory. Their traces satisfy R1 under the README buffer assumptions. `allCases_checked` checks every byte of every modeled load/store against the allowed source/destination regions in all 36 cases, including cases returning errors. | Safety for all other inputs, capacities, placements, and initial memory. This needs invariants across the decoding loops, extension-length loops, shortcut copies, and actual memcpy/memmove helper loops. |
| R2 | `zeroCapacity` covers the entire admissible zero-capacity part of R2: the singleton zero block returns zero, with no writes. Of the 36 cases in `allCases_checked`, 24 have `valid = true`: the independent format parser checks strict validity/end conditions, and the Wasm model returns the expected length and bytes. Wasmtime independently checks those same outputs on the binary. | Completeness for every valid independent block with sufficient positive capacity. In particular, there is no induction relating arbitrary sequences and overlapping matches to the decoder's control flow. The format parser's correspondence to the prose specification also requires review. |
| R3 | `zeroCapacity` characterizes all successes on that entry path: only a singleton zero byte succeeds, returning the empty content. In the finite suite, all 28 nonnegative results have exactly consumed parses under the allowed relaxed format, offsets no larger than the decoded prefix, the specified zero-offset behavior, equal output bytes/length, and length at most capacity. The other 8 cases return negative values. | Soundness for every other successful execution. No theorem relates all possible accepting paths to a complete format parse. |

No counterexample to a README requirement was obtained. For example, the accepted short-final-match case is **not** a counterexample: R3 explicitly permits broken end conditions. The zero-offset cases likewise exercise an explicit exception.

The exact general theorem statements, in namespace `Verification`, are in [Proofs/Checks.lean](Proofs/Checks.lean):

```lean
theorem zeroCapacity (src dst size : Nat) (m : Memory)
    (hs : src ≠ 0) (hb : src + 1 ≤ memorySize) :
    effect (execute 64 src dst size 0 m) =
      some (if size = 1 then (if m src % 256 = 0 then 0 else 4294967295)
            else 4294967295, m,
        if size = 1 then [⟨false, src, 1⟩] else [])

theorem emptySource (src dst cap : Nat) (m : Memory)
    (hs : src ≠ 0) (hc : cap < 2147483648) :
    effect (execute 64 src dst 0 cap m) = some (4294967295, m, [])
```

Here `Memory = Nat → Nat`, with byte reads reduced modulo 256; `memorySize = 2097152`. The result tuple contains the unsigned i32 return word, final memory, and reverse chronological access trace. `4294967295` represents signed i32 `-1`. An access `⟨false, src, 1⟩` is a one-byte read. Failure to finish, a trap, an unresolved branch, or an unexpected result stack cannot yield a successful `effect`. `execute` runs the extracted decoder instruction body, including actual helper instructions when called. It does not substitute a high-level LZ4 algorithm for the decoder.

The exact aggregate finite theorem in [Proofs/Cases.lean](Proofs/Cases.lean) is:

```lean
theorem allCases_checked : checkedCases.all checkCase = true
```

That file also contains `case0_checked` through `case35_checked`, each with exact statement `checkCase caseN = true`. The aggregate list contains precisely those 36 cases. Each individual theorem uses `decide +kernel`, not native evaluation or an external solver. There are no `sorry` declarations or added axioms.

Read `checkCase`, `buffersOK`, `allowed`, and `testMemory` in [Proofs/Checks.lean](Proofs/Checks.lean) for the exact finite proposition. In particular:

- Buffers satisfy the README address, size, and disjointness restrictions.
- The execution must finish within the recursion fuel bound 5000.
- Every recorded access is checked byte by byte. Reads above address 131071 must be in source or destination; writes there must be in destination. The interpreter itself does not enforce this buffer policy, so this check is not true by construction.
- A successful case must return the specified content length, fit in capacity, store exactly that content, and agree with `parseBlock true`. That parser requires complete input consumption and bounded offsets, and explicitly supplies zero bytes for offset-zero matches.
- A case marked `valid` must additionally satisfy `validIndependent`, including the end conditions and the README capacity proviso. Cases expecting failure must actually return a negative i32.

[verification/cases.json](verification/cases.json) records every input, expected output or negative result, source address, destination address, capacity, and validity flag. The cases exercise literal lengths 0, 1, 14, 15, 16 and 270; continuing extension bytes; offsets 1–8 and 16; overlapping copies; multiple matches; extended matches; zero offsets; malformed/truncated input; insufficient capacity; both memmove directions; adjacent buffers; and memory's upper boundary. Other initial caller bytes are fixed to `0xa5` in these finite cases. These are not exhaustive tests of all bytes, offsets, sizes, placements, or memory states.

2. Connection to the shipped bytes

[verification/extract.py](verification/extract.py) validates the module using `wasm-tools`, checks its exact size/hash, and disassembles that binary. It extracts function 2, the exported decoder, and its reachable helpers 3 and 4, plus the active data bytes at address 65536. It rejects unsupported instructions, nonempty block signatures, and calls to other functions. It checks fixed memory size, the decoder export, and the absence of imports/start functions.

[Proofs/Artifact.lean](Proofs/Artifact.lean) contains the entire artifact's hex bytes, its hash, and those instruction trees. `extract.py --check` compares the complete generated file with a fresh extraction. The source C and `build.sh` are not used as evidence of binary correctness, and no recompilation of the artifact is needed.

[Proofs/Wasm.lean](Proofs/Wasm.lean) supplies executable semantics for the scalar instructions used by these functions: modular i32 arithmetic, locals, structured branches/loops, calls, unsigned little-endian loads, stores, and returns. It records memory operations and enforces linear-memory bounds. This is a manually written Wasm subset model. **Its equivalence to official Wasm semantics, and the extractor's correctness, have not been formally proved.** Thus even the general entry-path theorems are about this model, with an artifact connection conditional on reviewing that translation and semantics.

As an independent execution check, [verification/cases.py](verification/cases.py) places the *entire unchanged binary* in a WAST binary-module declaration, registers its exports, and instantiates wrappers importing its memory and decoder. The wrappers initialize memory, invoke the decoder, and assert signed return behavior, output bytes, and adjacent destination canaries. Wasmtime runs these assertions. This is direct finite evidence about the shipped artifact; it does not establish read confinement, full write confinement, or universal correctness. The modeled traces provide the finite access checks.

3. Reproduction

From this directory, with the installed offline toolchain:

```bash
bash verification/check.sh
```

The script runs exactly:

```bash
python3 verification/extract.py --check
python3 verification/cases.py --check --runtime
lake clean proofs
lake build
```

`lake clean proofs` removes only this project's build products, preserving the already built dependency packages, so proofs are checked afresh. Wasmtime uses a temporary cache directory. No network, C compiler, Python extension package, or external solver is required.

Success means exit status zero, three initial `PASS:` messages (exact artifact/extraction; 36 Lean fixtures; 36 Wasmtime cases), `Build completed successfully`, and the final message:

```text
PASS: all reported results checked; universal R1-R3 remain unproved
```

The root [Proofs.lean](Proofs.lean) prints the theorem axiom dependencies during the fresh build:

```text
'Verification.zeroCapacity' depends on axioms: [propext, Quot.sound]
'Verification.emptySource' depends on axioms: [propext, Classical.choice, Quot.sound]
'Verification.allCases_checked' depends on axioms: [propext]
```

These are standard Lean axioms. There is no `Lean.ofReduceBool`/native-decide axiom or assumption that the decoder meets a requirement. The success messages certify only the results stated above.

4. Review and trust boundary

Local file sizes below are lines / bytes; sizes include comments and generated hex text. All definitions that determine what was checked must be reviewed, especially the Wasm semantics and format interpretation.

| File | Lines / bytes | Role |
| --- | ---: | --- |
| `Proofs/Wasm.lean` | 172 / 5953 | Manually written execution model; primary semantic trust boundary. |
| `Proofs/Format.lean` | 74 / 2764 | Independent executable interpretation of the supplied block-format document; no proof of correspondence to prose. |
| `Proofs/Checks.lean` | 86 / 3287 | General proofs, initialization, result observation, buffer/access predicates and finite checking proposition. |
| `Proofs/Artifact.lean` | 895 / 36650 | Generated binary hex, instruction trees, data and reachable-function map. |
| `Proofs/Cases.lean` | 81 / 12754 | All concrete case definitions, kernel proofs and aggregate theorem. |
| `Proofs.lean` | 5 / 144 | Imports and axiom audit. |
| `verification/extract.py` | 109 / 4893 | Trusted artifact-to-instruction translation/checking script, using wasm-tools. |
| `verification/cases.json` | 326 / 8362 | Complete finite fixtures and expectations. |
| `verification/cases.py` | 69 / 3583 | Fixture-to-Lean consistency check and direct binary runtime harness. |
| `verification/check.sh` | 9 / 333 | Reproduction commands. |

Also trust the installed Lean 4.35.0 kernel and its standard axioms, the imported built Mathlib v4.35.0 libraries, Python's runtime/standard library including SHA-256, and `wasm-tools` for extraction/validation. The direct runtime results additionally trust Wasmtime and the host execution environment. The normative texts are `README.md` (18 lines / 2872 bytes) and `lz4_Block_format.md` (244 lines / 10683 bytes). Lean compilation checks the proofs against the supplied definitions; it does not verify those tools or the interpretation of those texts.
