**Partial verification; the general requirements remain unresolved.** There are two machine-checked, universally quantified boundary-path results. There is no proof of R1, R2, or R3 for general nonempty decoding, and no counterexample was found. Passing the check below must not be interpreted as full verification of the decoder.

Run, from this directory:

```sh
./check.sh
```

It uses the installed tools offline and does not rebuild or modify `lz4-c.wasm` or the C sources. Success is exit status 0, ending with:

```text
CHECK PASSED: two scoped theorems replayed in three kernels; all negative controls and runtime tests passed.
PARTIAL RESULT: R1, R2, and R3 remain unproved for the general decoding paths.
```

The script removes only this project’s derived Lake build directory before rebuilding the proofs; dependency packages are retained. It prints every check command. Proof exports, independently printed statements, negative-control diagnostics, a Wasmtime test script, and source-size counts are written under `verification/out/`. Tools are found on PATH or beside the installed Lean binary. Besides Lean/Lake, the command requires Python 3, Node.js, wasm-tools, wasmtime, leanchecker, leanexport, con-ron, and nanoda_bin; all were available in this environment.

The exact proved statements are in [Proofs/Cases.lean](Proofs/Cases.lean), in namespace `Verification`, with `open Wasm`:

```lean
theorem zero_capacity (m : Memory) (src dst n : Nat)
    (hs : 0 < src) (hm : src < 2097152) :
    execute Artifact.decoder m src dst n 0 =
      some (if n = 1 ∧ (m src).val = 0 then 0 else 4294967295,
            if n = 1 then [src] else [])

theorem zero_source_size (m : Memory) (src dst cap : Nat)
    (hs : src ≠ 0) (hc : 0 < cap) (hc32 : cap < 2147483648) :
    execute Artifact.decoder m src dst 0 cap = some (4294967295, [])
```

`Memory` is `Nat → Fin 256`, so these results quantify over arbitrary byte values, not selected test memories. Arguments and results represent unsigned i32 words; `4294967295` represents the signed return value -1. For arguments satisfying the README, the theorems' hypotheses follow from the buffer constraints. The second component of a successful execution is the list of byte addresses read, in reverse order. The execution semantics has no successful store operation; it cannot report success after a write or any unsupported instruction. Therefore every execution covered by these two results preserves the whole memory. `none` means blocked or unsupported execution, never a successful return or a proved property.

| Requirement | Proved subcase and exact result | General status |
| --- | --- | --- |
| R1 | `zero_capacity`: when capacity is 0, exactly one source byte is read if source size is 1; otherwise no byte is read. `zero_source_size`: when source size is 0 and capacity is positive, no byte is read. Neither path writes. Thus R1 holds whenever either size is zero, under the README's other hypotheses. | Unproved when both sizes are positive. |
| R2 | `zero_capacity`, specialized to source size 1 and source byte 0, returns 0 and preserves memory. This establishes the empty block with capacity 0: its decoded content is empty. The connection between byte 0 and the format's empty-block rule is a human reading of the supplied specification. | Unproved for positive capacities, including the empty block with positive capacity, and for all other valid blocks. |
| R3 | `zero_capacity`: the only nonnegative return with capacity 0 is 0, and it occurs exactly for the one-byte block 0. Its decoded content is empty, with no matches, and its return is at most capacity. `zero_source_size` rules out a nonnegative return for an empty source with positive capacity. | Unproved for positive capacities and nonempty sources. |

No complete formal definition of valid LZ4 blocks is supplied. The general proofs would require invariants for the decoder's loops, its speculative copies and offset tables, proofs for its memory-copy helpers, and a refinement argument connecting successful decoding to the format. None of those proofs is present. The interpreter deliberately blocks on those paths. The runtime tests below do not close these gaps.

The connection to the shipped artifact is as follows:

1. [verification/extract.py](verification/extract.py) checks the length (8,469 bytes) and SHA-256 `8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6` of `lz4-c.wasm`. It checks the module header, absence of imports and a start function, fixed memory size, exported decoder index, function types and locals. It decodes function 2 directly from the binary into structured WebAssembly instructions. There is no handwritten translation of the LZ4 algorithm.
2. The extraction must reproduce [Proofs/Artifact.lean](Proofs/Artifact.lean) exactly. That file contains all of the decoder's instructions, including the unproved paths: a 1,095-byte function body, with 582 instructions counting `end` markers, represented by 519 operation nodes, 24 blocks, and 7 loops. No C compilation or assertion about compiler correctness is used.
3. [Proofs/Wasm.lean](Proofs/Wasm.lean) supplies a small instruction interpreter for the proved paths. It implements constants, local access, comparisons, selection, byte loads, conditional branches, blocks and return. Calls, loops, stores and other unsupported instructions block execution. A fuel bound of 128 suffices for the proved paths. The proofs establish successful executions, so fuel exhaustion and unsupported execution cannot be mistaken for a result.

**The extractor and the correspondence of this small interpreter to WebAssembly are trusted, not formally proved.** In particular, the branch/stack behavior on these paths must be reviewed against WebAssembly semantics. There is no machine-checked soundness theorem relating this interpreter to a complete WebAssembly semantics. These are proofs over automatically extracted artifact instructions under that explicit semantic trust boundary, not an unconditional binary-to-format refinement proof. wasm-tools validates the real module, and independent runtime checks supplement this connection.

The proof checks are:

- Lean 4.35.0 checks the source proofs; `leanchecker Proofs` replays their compiled declarations through Lean's C++ kernel.
- `leanexport` exports the two target theorems and their dependency closure. `con-ron --verified --jobs=2` and Nanoda independently check the exported proof terms. These are separate Rust kernel implementations; the additional Lean replay alone is not counted as an independent implementation. The observed acceptance counts were 1,437 declarations for con-ron and 1,635 for Nanoda; their counting conventions differ.
- An export audit allows only `propext` and `Quot.sound`, the axioms actually used. In particular, it disallows `sorryAx`, `Lean.trustCompiler`, and additional axioms. No `native_decide` or trusted native computation establishes either theorem. The independent printer writes both statements to `verification/out/statements.txt`.
- [Bad.lean](verification/negative/Bad.lean) deliberately emits `True.intro` as a proof of `False`. [BadEq.lean](verification/negative/BadEq.lean) deliberately emits reflexivity at 0 as a proof of `0 = 1`. Kernel checking is bypassed only while creating these isolated malformed fixtures; they are not imported by `Proofs`. The same three replay commands must reject both fixtures. Lean and con-ron report type mismatches; Nanoda exits 101 at its definitional-equality assertion. The harness requires those particular diagnostics, not just an arbitrary failing exit code. All six rejection checks passed.

The supplementary runtime results are reproducible tests, **not universal proofs**:

- [verification/instrument.py](verification/instrument.py) creates a separate test module wrapping all 280 memory-access sites (25 access forms) with byte-level R1 guards. All original function indices are retained. Guards permit reads in the union of source and destination and writes in the destination, considering only addresses in the README's high-memory region. Both a deliberately disallowed read and a deliberately disallowed write must trap, testing the instrumentation itself.
- [verification/test.mjs](verification/test.mjs) checks 25,219 calls against the original artifact and its instrumented copy. These include all one-byte inputs at seven capacities, empty inputs, literal and match extension boundaries, offsets 1–32, zero offsets, adjacent buffers, buffers ending at the memory boundary, 20,000 deterministic random malformed inputs, a 1,950,000-byte decoded match case, and a 900,000-byte literal case. All guards passed and both modules' returns and destination buffers agreed.
- A separate, slow JavaScript format decoder checks 1,177 generated valid-block cases for R2 and all 3,694 nonnegative returns for R3, permitting the README's zero-offset and end-condition exceptions. This handwritten format model is only a test oracle; its agreement with the format has not been proved.
- Wasmtime replays 80 selected successful and unsuccessful calls on the exact original module bytes, checking returns and successful output bytes. A deliberately false Wasmtime assertion must fail. All runtime checks and controls passed; no counterexample was found. This is not exhaustive input coverage.

The reviewer should read the theorem statements and their definitions, the extraction, and the check driver. The table counts whole files, including comments, imports, whitespace and proof scripts; it does not hide generated data behind a line count.

| Review material | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 84 | 2,963 | All project-defined instruction semantics and execution definitions |
| `Proofs/Artifact.lean` | 6 | 6,922 | Generated instruction definition; checked by re-extraction |
| `Proofs/Cases.lean` | 31 | 1,207 | Both statements and kernel-checked proofs |
| `Proofs.lean` | 1 | 20 | Library root |
| `verification/extract.py` | 101 | 3,319 | Trusted binary extraction and artifact binding |
| **Subtotal above** | **223** | **14,431** | Entire formal source and extraction |
| `verification/check.py` | 104 | 5,134 | Replay, export audit, diagnostics, test orchestration and size report |
| `check.sh` | 4 | 100 | Entry point |
| `verification/instrument.py` | 71 | 3,218 | Trusted only for the dynamic R1 tests |
| `verification/test.mjs` | 148 | 8,626 | Runtime harness and unproved format test oracle |
| Both negative fixtures | 20 | 603 | False-proof setup |

The two theorem statement texts alone are 438 UTF-8 bytes when extracted without proof bodies, with one separating blank line. All their project-defined semantic and instruction definitions are in the files counted above. Standard Lean definitions such as `Nat`, `Int`, `List`, `Fin`, equality and the two allowed axioms also need their usual intended interpretation; the exported dependency closure is checked by the independent kernels. No Mathlib-specific axiom or software model is introduced.

These counts exclude Lean, its standard library, kernel implementations, the exporter, Python, Node/V8, wasm-tools, Wasmtime, the operating system and hardware. Those tools and their correspondence to the source/bytes they consume remain part of the trust boundary; independent checking reduces reliance on one kernel but does not eliminate it. The test-only format model and instrumentation are additional trust obligations for the test claims, not for the two formal execution results. `verification/out/sizes.txt` records the actual source sizes on each run.
