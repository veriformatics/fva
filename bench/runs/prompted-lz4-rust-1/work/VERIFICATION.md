This is a **partial verification**. R1, R2 and R3 remain unproved in general. No counterexample to them has been established. A successful check of this submission must not be interpreted as certification of all three requirements.

The implementation, vendored Rust source, and shipped Wasm file were not changed.

The machine-checked results are in [Proofs/Results.lean](Proofs/Results.lean). Their exact statements, in that file's namespace `Results` with `open Wasm`, are:

```lean
theorem zero_input (src dst cap : Nat) (m : Nat → Nat) :
    observe (run 6 (initial Artifact.program ⟨src, dst, 0, cap⟩ m)) =
      some (4294967295, true, [], [])

theorem cases_valid_buffers : cases.all (fun c =>
    c.input.length ≤ 131072 && c.cap ≤ 1835008 && c.input.all (· < 256)) = true

theorem certified_cases : cases.all check = true
```

`zero_input` uses `rfl`; the other two proofs use `decide`. There is no `sorry`, new axiom, `native_decide`, or compiler-backed proof evaluation in these proofs. The axiom audit reports `propext` for `zero_input` and `certified_cases`, and no axioms for `cases_valid_buffers`. The exported dependency closure is also checked against an explicit axiom allowlist; `sorryAx` and `Lean.trustCompiler` are forbidden.

For each requirement:

| Requirement | Established result | Remaining gap |
| --- | --- | --- |
| R1 | `zero_input` covers every initial memory function, address pair and capacity when `n = 0`: i32 return value -1, no reads, no writes. `certified_cases` checks every memory access in the 11 listed executions against the supplied source and destination regions, including executions returning -1. | No universal safety proof for `n > 0`. The finite cases use fixed addresses and a fixed initial background byte. |
| R2 | Six cases in `certified_cases` have `strict = true` and a successful format decoding. For each, the artifact evaluator returns the specified decoded length, it fits the capacity, and every output byte equals the format decoder's output. | No theorem for all valid independent blocks, capacities, addresses, or initial memories. |
| R3 | All seven successful cases have the required output length and content according to the format decoder. One deliberately relaxes the end conditions. Four malformed cases are rejected, including zero offsets in the slow and fast paths, an offset before the beginning of output, and an unterminated length extension. | These checks do not establish that every accepted input has a valid sequence decomposition. |

`cases_valid_buffers` establishes the size and byte bounds for the finite cases. With the fixed `src = 131072` and `dst = 262144` in `execution`, these bounds imply that the buffers are disjoint and inside caller memory. All lengths and capacities have type `Nat`, so are nonnegative.

The missing general proofs require inductive invariants for the actual Wasm loops, including length accumulation, cursor and capacity bounds, overlapping matches, and copies wider than the logical match length. They also require a simulation argument connecting every successful execution to the format specification. These have not been constructed. The execution fuel of 2000 is sufficient for the listed cases; it is not a proved bound for arbitrary inputs.

The connection to the artifact is checked as follows:

- The whole 7,161-byte `lz4-flex.wasm` must have SHA-256 `1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.
- [verification/check.py](verification/check.py) parses its sections, verifies there are no imports or start function, resolves `lz4_decompress` to function 7, and checks the fixed 32-page memory declaration.
- Function 7's body is exactly the 2,000 bytes at file offsets `[4437, 6437)`. Every byte is compared with the generated literal in [Proofs/Artifact.lean](Proofs/Artifact.lean). Its five-byte local declaration introduces 17 i32 and seven i64 locals. `Artifact.program` parses the remaining bytes with the Lean instruction parser.
- The formal evaluator executes those instructions. It is a generic partial Wasm interpreter, not a replacement Rust decoder or a hand-written LZ4 implementation. Unsupported instructions, malformed evaluator states, out-of-memory accesses and exhausted fuel give `none`; a finite certificate requires a completed return. It does not model trap executions or calls to the panic helpers as successful returns.
- Wasmtime and WABT independently replay the same cases, initializing the caller memory to `0xa5` and installing the specified source bytes. Their WAST harness embeds the **entire original binary unchanged**, imports its exported memory for setup and inspection, invokes the original export, and checks return values, output bytes, source preservation and adjacent guards. These runtime assertions supplement the proofs; they are not universal proofs of R1–R3.

The interpreter's agreement with official Wasm semantics is **not itself proved**. Its definitions and the format decoder must be reviewed for the formal results to imply the descriptions above. In particular, the reviewer must check integer widths, signed constant decoding, empty block signatures, branches, memory operations and access accounting in [Proofs/Wasm.lean](Proofs/Wasm.lean), and sequence parsing, offset bounds, overlap copying and end conditions in [Proofs/Format.lean](Proofs/Format.lean).

Run this single command from this directory, offline:

```sh
python3 verification/check.py
```

The command pins the artifact, rebuilds local Lean modules from source, exports the three theorem roots and their dependency closure, and replays that closure through:

1. Lean's kernel, using `leanchecker --from-export`;
2. Nanoda, an independent Rust kernel;
3. con-leche in `--verified` mode;
4. con-ron in `--verified` mode.

The installed executables are taken from `/opt/lean/bin`; the remaining dependencies are Python 3, Lake/Lean 4.35.0, `wasm-tools`, `wasmtime`, `wast2json` and `spectest-interp`. No network or Rust rebuild is used. The installed `lean4lean` executable could not read the 4.35 `.olean` header; it is not counted as a successful replay.

Each of the four checking paths must also reject two poisoned proof objects: `False` with proof `True.intro`, and `(1 : Nat) = 2` with proof `Eq.refl 1`. Their isolated fixture modules deliberately disable producer-side kernel checking, so the replay checkers receive actual false theorem objects. They are never imported by the real proofs. The script requires a type-checking rejection, not merely a missing-file or usage failure. Nanoda signals these particular rejections with its failed `def_eq` assertion and a nonzero exit. Both runtime harnesses must reject a deliberately incorrect `1 = 2` result assertion too.

Success requires exit status zero and the final line:

```text
PASS: partial certificates, artifact replay, and negative controls. R1–R3 remain unproved in general.
```

Any missing tool, changed artifact, failed proof, accepted false proof, failed runtime assertion or unrecognized negative-control failure makes the command fail. Logs and exports are written under `.verification/`; local `.lake/build` is recreated to avoid relying on stale proof objects.

The following sizes include comments and blank lines. The human review surface for the newly written formal statements and their semantic definitions is **313 lines / 11,568 bytes**, plus the 82-line generated artifact module containing the exact 2,000-byte input and its parsing definition. The complete checking support is listed separately rather than hidden from the trust accounting.

| File | Lines | Bytes | Review purpose |
| --- | ---: | ---: | --- |
| `Proofs/Wasm.lean` | 196 | 7,019 | Partial Wasm semantics and access accounting |
| `Proofs/Format.lean` | 52 | 1,906 | Independent format specification |
| `Proofs/Results.lean` | 64 | 2,621 | Exact claims, test data, observation and comparison definitions |
| `Proofs.lean` | 1 | 22 | Imports the result module |
| `Proofs/Artifact.lean` | 82 | 8,285 | Generated byte data and parsing definition; mechanically compared with artifact |
| `verification/check.py` | 242 | 11,316 | Artifact binding, rebuild, export audit, checker invocation, negative controls and runtime harness |
| `verification/Emit.lean` | 11 | 454 | Transfers the checked case definitions to the runtime harness |
| `verification/Audit.lean` | 5 | 136 | Prints axiom dependencies |
| `verification/FalseProof.lean` | 9 | 407 | False-theorem rejection control |
| `verification/UnequalProof.lean` | 10 | 489 | Unequal-numerals rejection control |

All listed files total **672 lines / 32,655 bytes**. The check command records exact current file sizes in `.verification/sizes.json`.

Including standard-library dependencies, the exported transitive closure contains **656 declaration records**: 448 definitions, 69 inductive blocks, 137 theorems, one opaque declaration and the axiom `propext`. Its full serialization, including proof terms, expression tables and metadata, is **29,126 lines / 1,599,536 bytes** in `.verification/proofs.ndjson`. The 313-line figure measures the new formal review surface, not this entire library closure.

The task's `README.md` and `lz4_Block_format.md` remain the external intended specification. Standard Lean definitions reachable from the proofs, the export format/readers, the checker binaries and their runtime/platform remain dependencies; the exported closure is replayed rather than trusting imported proof declarations. Multiple accepting kernels and negative controls reduce reliance on any one checker, but do not remove the need to review the statements and semantics.
