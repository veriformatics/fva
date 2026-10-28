**Verification status: partial. R1, R2 and R3 are not proved in their full stated generality. No counterexample to them was found.** The results below certify the decoder's early-return paths and supply finite execution evidence for other paths. Passing the check command must not be interpreted as full verification of this decoder.

**Requirement coverage.** The theorem names below are in namespace `Artifact`, in [Proofs/EarlyReturn.lean](Proofs/EarlyReturn.lean). Their exact statements appear together below.

| Requirement | Machine-checked result | Remaining gap |
| --- | --- | --- |
| R1 | `zeroCapacity` covers every input with `dstCapacity = 0`: the only possible read is the source byte when `srcSize = 1`. `zeroInput` covers `srcSize = 0` and positive capacity. Both preserve all memory; their successful evaluation paths contain no store instruction. Thus their reads and writes satisfy R1 under the README's buffer preconditions. | No universal proof of access bounds for positive source size and positive destination capacity. The parsing and copy loops are outside the supported evaluator fragment. Runtime tests check writes, not read footprints. |
| R2 | `emptyBlock` proves successful decoding of the single-byte block `00` with zero output capacity, at every permitted address and for arbitrary other memory contents: result 0, unchanged memory, exactly one source read. The supplied format explicitly identifies this block with empty content. | No formal definition of the full LZ4 language or proof for other valid blocks, including the empty block with positive capacity. |
| R3 | `zeroCapacityConverse` proves that every nonnegative result with zero capacity comes only from the singleton byte `00`, returns 0, preserves memory and has exactly one source read. This is a valid independent block with decoded length 0. `zeroInput` additionally makes the positive-capacity, zero-source-size case vacuous. | No universal proof relating successful positive-capacity executions to LZ4 sequences, offsets or content. |

Here are all four exact theorem statements. `Memory`, `byte`, `word`, `execute` and their dependencies are defined in [Proofs/Semantics.lean](Proofs/Semantics.lean); `decoder` is generated from the artifact in [Proofs/Artifact.lean](Proofs/Artifact.lean).

```lean
theorem zeroCapacity (m : Memory) (src dst size : Nat)
    (hsrc : src ≠ 0) (hbound : src < 2097152) :
    execute decoder m src dst size 0 =
      some (if size = 1 then (if byte m src = 0 then 0 else word - 1) else word - 1,
            m, if size = 1 then [src] else [])

theorem zeroInput (m : Memory) (src dst cap : Nat)
    (hsrc : src ≠ 0) (hcap : cap < 2147483648) (hne : cap ≠ 0) :
    execute decoder m src dst 0 cap = some (word - 1, m, [])

theorem emptyBlock (m : Memory) (src dst : Nat)
    (hsrc : src ≠ 0) (hbound : src < 2097152) (hbyte : byte m src = 0) :
    execute decoder m src dst 1 0 = some (0, m, [src])

theorem zeroCapacityConverse (m finalMemory : Memory) (reads : List Nat)
    (src dst size r : Nat)
    (hsrc : src ≠ 0) (hbound : src < 2097152)
    (hr : r < 2147483648)
    (hexec : execute decoder m src dst size 0 =
      some (r, finalMemory, reads)) :
    size = 1 ∧ byte m src = 0 ∧ r = 0 ∧ finalMemory = m ∧ reads = [src]
```

The result tuple is `(unsigned i32 return value, final memory, ordered byte-read addresses)`. `word - 1` is `4294967295`, the i32 representation of -1. `r < 2147483648` means a nonnegative signed i32. Memory is an arbitrary total function, with bytes obtained modulo 256; loads additionally check the actual 2 MiB memory bound. On application to the README, all arguments are canonical i32 representatives, source addresses are nonzero and below 2097152, and capacities are below 2147483648. Thus the theorem assumptions follow from the stated buffer preconditions. No assumption fixes the bytes outside the source buffer.

**Connection to the shipped code.** The artifact is the unchanged 8,469-byte `lz4-c.wasm`, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

[verification/extract.py](verification/extract.py) reads these bytes directly. It checks the digest, length, module sections, types, absence of imports and a start function, fixed 32-page memory, decoder export at function index 2, and the decoder's fifteen i32 locals. It parses the complete decoder instruction tree, rejects unknown encodings, round-trips the function body including padded LEB encodings, and compares the resulting Lean definition byte-for-byte with the checked-in generated file. `wasm-tools validate` independently checks module validity. No C compilation or source-code translation is used for the results; the C sources and Wasm artifact have not been rewritten.

The formal theorems are about a **handwritten partial Wasm evaluator applied to extracted artifact instructions**, not a standalone LZ4 model. The evaluator implements the instructions on these early-return paths: constants, local variables, comparison, selection, byte load, branches through zero-result blocks, and return. Unsupported instructions, loops, traps and exhausted fuel return `none`. Each theorem proves a particular `some` result; it does not assume termination or treat failure as success. The evaluator models no calls or stores, and certified paths reach neither. Its fuel is 64 in the recursive evaluator, not a claim that the whole decoder terminates within 64 instructions.

The adequacy of this small evaluator fragment to WebAssembly semantics, including opcode meanings, stack order, signed comparison and block/return behavior, is a manual trust obligation. There is no machine-checked refinement theorem from an independently formalized full WebAssembly semantics. In particular, these results cannot be extended to unsupported paths by interpreting `none` as a decoder error. The extraction script is another trust obligation; round-tripping and hashing do not prove the extractor correct.

**Reproduction.** From this directory run:

```sh
./check.sh
```

This needs the already-installed Lean 4.35.0 toolchain and its `leanexport`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, and `nanoda_bin` executables, plus Python 3, Node.js, `wasm-tools`, and `wasmtime`. It uses no network and preserves the prebuilt package dependencies. It removes this project's `.lake/build` directory to force a fresh proof build. Generated exports, test scripts and logs are under `verification/`.

Success is exit status 0 and the final line:

```text
CHECK PASSED for the stated partial results. Universal R1, R2, R3: UNPROVED.
```

The command rebuilds all proof modules and exports all four theorems together with their transitive declaration dependencies. It then replays that export from scratch through:

- Lean's C++ kernel (`leanchecker --from-export`), also the installed paranoid variant;
- Lean4Lean's independently implemented Lean kernel (`lean4lean --import`);
- Nanoda's independently implemented Rust kernel, with an explicit axiom allowlist.

The successful replay checked 897 declarations in Lean4Lean and 1,080 declarations in Nanoda, whose accounting includes additional declarations. All four theorems use only `propext` and `Quot.sound`; `sorryAx`, `Lean.trustCompiler`, arbitrary axioms and native evaluation certificates are not permitted by the Nanoda configuration. Mathlib is available to the Lake project but these proofs do not import it. Nanoda reports one pretty-printer warning, `Unable to print axioms`, after reporting **no typechecker errors**. Lean4Lean's installed `.olean` reader reports an incompatible header on this toolchain; the working replay route is its `--import` export-file interface. The check command uses that route.

[verification/Forge.lean](verification/Forge.lean) injects `True.intro` as a purported proof of `False`. [verification/ForgeEq.lean](verification/ForgeEq.lean) injects reflexivity of `0` as a purported proof of `0 = 1`. They intentionally bypass the original environment's declaration checking to test replay, rather than merely testing whether the elaborator rejects an ill-typed source file. Neither is imported by the real proofs. Every replay checker rejects both exported false proofs. The command requires both nonzero status and a type-mismatch diagnostic (Nanoda's definitional-equality assertion), so a missing file or incompatible header does not count as rejection. Lean4Lean's error formatting also emits panic diagnostics on the false proofs; its final declaration-type-mismatch diagnostic is required. Full outputs are in `verification/logs/`.

**Additional execution evidence.** [verification/cases.py](verification/cases.py) constructs 1,512 finite cases. These include all single-byte inputs at capacities 0, 1 and 32; empty source buffers; literal runs and length-extension boundaries; independent overlapping matches at offsets 1, 2, 3, 4, 7, 8, 9 and 16; zero-offset matches producing zeros; malformed inputs; and reversed, adjacent and near-memory-end buffer layouts. They are not exhaustive over bytes, lengths, memory contents or addresses.

[verification/runtime.cjs](verification/runtime.cjs) executes the exact module in V8, checks successful return lengths and every output byte, and compares **all** memory at addresses 131072–2097151 outside the destination buffer before and after each call. Error cases require a negative result; they do not assert a specific negative error code. The generated WAST embeds the exact original binary and uses a separate helper module importing its exports to initialize/check memory. Wasmtime checks the same returns and outputs, unchanged source bytes and destination boundary guards. Its expected error results are normalized to -1 in the helper. A deliberately wrong WAST assertion expecting 0 when the artifact returns -1 must also fail. Both engines pass the positive suite. These are runtime demonstrations for finite inputs, not proof of the full requirements, and they do not detect out-of-buffer reads that leave no observable effect.

**Review and trust size.** Counts include blank lines and comments and are regenerated in [verification/review-size.json](verification/review-size.json). The exact formal statements are also emitted to [verification/statements.txt](verification/statements.txt).

| Custom material to review | Lines | UTF-8 bytes | Purpose |
| --- | ---: | ---: | --- |
| Four theorem statements | 21 | 978 | Precisely what is asserted |
| `Proofs/Semantics.lean`, entire file | 93 | 3,297 | All custom semantic definitions |
| `verification/extract.py` | 149 | 5,171 | Artifact-to-instruction linkage |
| `verification/check.py` plus `check.sh` | 105 | 5,269 | Build, export, replay and control orchestration |
| Both forged-proof controls plus `Audit.lean` | 36 | 1,183 | Negative controls and axiom reporting |
| `cases.py` plus `runtime.cjs` | 144 | 6,812 | Finite-test inputs, expected results and execution checks |
| Generated `Proofs/Artifact.lean` | 588 | 15,858 | Complete decoder instruction data; regenerated and compared |

The handwritten formal interface is **114 lines / 4,275 bytes** including its definitions. Adding the artifact extractor gives **263 lines / 9,446 bytes**. These figures do not conceal the generated instruction data or the testing/check orchestration, which are counted separately above. The proof bodies need not be trusted: they are replayed through independent kernels. Standard Lean logical primitives and the meanings of standard `Nat`, `Int`, `List` and `Option` definitions remain part of interpreting the statements; their proof dependencies are included in the export rather than assumed as unchecked library theorems.

Reviewers must additionally trust the translation of the README's natural-language requirements to the restricted cases described above, the supplied format's interpretation of `00` as empty content, SHA-256 and file I/O, the installed checkers/export parser and their execution platform, and the runtime engines for the finite test evidence. This is a small artifact-linked partial result, not a complete formalization of LZ4, C, or WebAssembly. Completing R1–R3 requires a semantics for the remaining instructions and calls, loop and copy invariants, and a formal LZ4 sequence/content relation; those are not supplied here.
