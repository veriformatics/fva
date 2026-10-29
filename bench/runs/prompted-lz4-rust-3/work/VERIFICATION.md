This is a **partial verification**. R1, R2, and R3 remain unproved for arbitrary multi-byte inputs. No counterexample to them was found. Passing the command below does **not** certify the entire decoder or complete the requested proof/disproof of every requirement.

Run from this directory, without network access:

```sh
python3 verification/check.py
```

Exit status 0 and these final lines mean success for the partial results described here:

```text
PASS: partial artifact proofs replayed; false proofs rejected; both runtimes agree.
R1, R2 and R3 for arbitrary inputs remain UNPROVED. See VERIFICATION.md.
```

The command rebuilds only this project's `.lake/build`, using the installed dependencies, and checks every result below. Logs, exported proofs, runtime fixtures and review-size counts are written under `.verification/`. Unexpected acceptance or rejection, a changed artifact, a missing tool, a timeout, or a failed runtime assertion causes failure.

**Requirement results**

| Requirement | Established | Remaining gap |
| --- | --- | --- |
| R1 | Empty input: no memory accesses for arbitrary arguments and memory. One-byte input at address 131072: exactly one byte read there and no writes, for every byte value, output address, capacity and surrounding memory. Also checked for all 24 explicit execution cases. | No invariant covering arbitrary longer inputs, capacities, buffer placements and initial memories. |
| R2 | Every valid one-byte block at address 131072 returns zero and preserves memory for arbitrary capacity and surrounding memory. Fourteen selected valid cases additionally return precisely the format's decoded output and length. | No general termination/completeness proof relating all valid blocks to artifact executions. |
| R3 | Every nonnegative return in the one-byte family is zero and comes from a valid empty-content block. Every successful execution in the 24-case suite has a relaxed-format parse, valid backward offsets, correct output and length bounded by capacity. | No general soundness invariant relating arbitrary successful executions to a complete parse. |

For the one-byte family, the source address is fixed; this theorem does not quantify over other source addresses. Its output pointer and capacity are unrestricted naturals; interpretation as a Wasm call uses i32 arguments and the README buffer preconditions. The empty-input theorem does quantify over source addresses.

The missing general proofs require induction over the decoder loops and optimized copies, bounds and wrapping arithmetic, and their relation to the format parser. Finite executions and short-input families do not provide those invariants. There is no claim that testing or a proof of the Rust source fills this gap.

**Exact machine-checked statements**

[Proofs/Results.lean](Proofs/Results.lean) contains the following statements (names shown fully qualified):

```lean
theorem Results.empty_input (src dst cap : Nat) (mem : Nat → Nat) :
    (Wasm.run 5 (Wasm.initial src dst 0 cap mem)).map
      (fun (r,s) => (r, s.mem, s.events)) = some (Wasm.word-1, mem, [])

theorem Results.interface_cases : Results.cases.all Results.interfaceCase = true

theorem Results.expected_cases : Results.cases.all Results.expectedCase = true

theorem Results.r1_cases : Results.cases.all Results.r1Case = true

theorem Results.r2_cases : Results.cases.all Results.r2Case = true

theorem Results.r3_cases : Results.cases.all Results.r3Case = true
```

The first theorem returns the i32 pattern `0xffffffff` (-1), preserves memory and has no memory events, within five interpreter steps, without premises on the other arguments or memory.

[Proofs/OneByte.lean](Proofs/OneByte.lean) contains:

```lean
theorem Results.one_byte (b dst cap : Nat) (mem : Nat → Nat) (hb : b < 256) :
    (Wasm.run 300 (Wasm.initial 131072 dst 1 cap (Results.singleMemory b mem))).map
      (fun (r,s) => (r, s.mem, s.events)) =
    some (if b < 16 then 0 else Wasm.word-1, Results.singleMemory b mem,
          [⟨false, 131072, 1⟩])

theorem Results.one_byte_format (b : Nat) (hb : b < 256) :
    LZ4.decode [b] = if b < 16 then some ⟨[], [], 0, true⟩ else none
```

`singleMemory b mem` puts `b` at address 131072 and agrees with `mem` everywhere else. An event is `(write, address, width)`, so `false` denotes a read. The second theorem identifies exactly which one-byte blocks parse and their decoded content. On its successful result, `LZ4.endConditions` reduces to `true`; the empty output fits every nonnegative capacity. These are parametric theorems, not tests of selected capacities or surrounding memories.

The definitions in `Results.lean` give the finite theorems their meaning:

- `cases` is an explicit 24-element list. Source is 131072 and destination is 262144. Initial memory contains the listed input at source and byte 204 everywhere else. Each capacity, expected unsigned i32 return, expected output prefix and valid-block selector is in that list.
- `interfaceCase` checks byte ranges, valid buffer addresses and disjointness.
- `expectedCase` checks exact returns and listed output prefixes, including exact -1 error returns. A trap, unsupported instruction or exhausted execution fuel cannot pass.
- `r1Case` checks **every byte of every recorded read and write**, including widened copies and bulk operations. Among addresses at least 131072, reads must be in source or allocated destination; writes must be in allocated destination. The interpreter separately checks physical memory bounds. This checks reads as well as writes.
- `r2Case` requires each of the fourteen cases marked `valid` to parse, meet end conditions, fit capacity and return exactly the parsed length and bytes. It asserts validity too: marking a malformed case `valid` would fail the proof.
- `r3Case` checks the implication for each observed nonnegative return: the parser must succeed with the correct output and length, and that length must fit capacity. The parser checks nonzero offsets that refer to bytes decoded before each match. End conditions are omitted here, as README R3 permits.

The suite covers literals of lengths 0–5, 15 and 16; length extensions; overlapping matches; a hot-loop widened-copy path; a slow widened-copy path; extended matches; zero and out-of-range offsets; truncated fields; and insufficient capacity. There are fifteen successful calls and nine errors. Input `10 41 01 00 00` (hex), capacity 5, returns 5 and writes five `41` bytes. Its final empty-literal sequence violates the end conditions. This is an allowed R3 example, **not** a counterexample to a requirement.

[Proofs/Spec.lean](Proofs/Spec.lean) independently specifies `lz4_Block_format.md` using unbounded natural lengths, little-endian offsets, progressive overlapping copying and separate end conditions. It is not a translation of the Rust decoder. Its correspondence to the prose remains a human review obligation.

**Connection to the shipped artifact**

The artifact is the unchanged 7,161-byte `lz4-flex.wasm`, SHA-256:

```text
1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775
```

`verification/artifact.py` checks the hash, length, binary header, absence of imports/start function, fixed memory, export mapping, function type indices and function 7's local declarations. It extracts function 7's instruction bytes verbatim and requires equality with [Proofs/Artifact.lean](Proofs/Artifact.lean). `wasm-tools validate` checks the original module too.

[Proofs/Syntax.lean](Proofs/Syntax.lean) decodes those bytes, including LEB immediates and nested control flow. [Proofs/Program.lean](Proofs/Program.lean) contains generated instruction data and this exported theorem, proved by reflexivity:

```lean
theorem Artifact.decoded_artifact :
    Wasm.parse (Artifact.code.length+1) Artifact.code = some (Artifact.program, [])
```

Independent kernels replay this equality. Thus the instruction data used by the execution proofs is checked against the extracted bytes. The external generator that originally produced `program` is unnecessary for checking and is not trusted. Incorrect instruction data makes the equality fail.

[Proofs/Wasm.lean](Proofs/Wasm.lean) is a small **ISA interpreter**, not a hand-written LZ4 implementation. It models locals, stack, structured branches, i32 wrapping arithmetic, little-endian memory and bulk copy/fill, recording memory events. The actual blocks have empty signatures, checked during decoding and module validation. The interpreter is partial: traps, unsupported execution paths and fuel exhaustion produce `none`, never a successful observation. Calls to panic helpers are unsupported. Every execution claimed here actually returns and avoids those paths. There is no claim that all artifact paths are supported or terminate.

The Rust source, compiler and `build.sh` do not generate the proof semantics and have not been changed. The compressor is outside the results.

The command also executes the original full binary on the same 24 cases in Wasmtime and V8, comparing returns and output bytes. V8 additionally compares all caller-region memory outside the destination with its initial contents. These checks supplement the proofs; they do not formally prove the interpreter correct or observe every runtime read.

**Independent kernels and rejection controls**

After a fresh Lean 4.35.0 build with its C++ kernel, `leanexport` exports the named results and their transitive proof dependencies. The command replays those terms through:

- `nanoda_bin` 0.4.19, an independently implemented Rust Lean kernel, with Nat/String extensions and a strict axiom allowlist;
- `con-ron --verified`, an independent Rust checker in its verified mode, without custom pins or relaxed checking options.

The observed export uses only the standard `propext` axiom. The harness permits only `propext`, `Classical.choice` and `Quot.sound`. Neither `sorryAx` nor `Lean.trustCompiler` is permitted. These proofs use no admissions, `native_decide`, or solver conclusions assumed as axioms. All exported dependencies are replayed, including the artifact-decoding proof. The frontend, exporter and transport are shared infrastructure; the proof kernels are independent implementations.

The command requires these controls:

1. Both independent kernels accept an exported `0 = 0` proof, then reject well-formed export records declaring `0 = 1` with its unchanged proof `Eq.refl 0`.
2. `verification/FalseProof.lean` assigns `Eq.refl 0` to `0 = 1` through a metaprogram, bypassing elaborator type checking. Lean's kernel must reject it. This exercises the proof-construction approach used to avoid expensive elaborator reduction in the one-byte proofs.
3. Both independent kernels reject a full export in which the proof of the actual `Results.r1_cases` theorem is replaced with a Nat literal.
4. Both Wasm engines reject an intentionally false expected result for the empty-input call.

Nanoda signals the negative controls by terminating at its type-comparison assertion: `src/tc.rs:955:71`, `assertion failed: self.def_eq(u, v)`, exit 101. The harness recognizes this specific assertion failure; it does not accept arbitrary panics or nonzero exits. Con-ron reports a theorem type mismatch and exits 1. Lean reports a kernel declaration type mismatch. Nanoda's positive log also reports an incidental axiom pretty-printing error, alongside `no typechecker errors`; this is not a proof-checking error.

A declined check, resource crash, unrelated panic, timeout or missing file is not a successful rejection control. These controls show rejection of these false proofs; they do not establish that the kernels are bug-free.

**Human review and trust boundary, with size**

The primary semantic review is the statements and non-library definitions in `Syntax.lean`, `Wasm.lean`, `Spec.lean`, `Results.lean` and `OneByte.lean`: **408 lines, 15,594 bytes**, conservatively counting entire files including comments, blanks and proof bodies. Also review the `program` declaration's type and the one-line `decoded_artifact` statement; its instruction literal is checked data. The 69-line, 2,475-byte artifact extractor is the additional trusted bridge to the hash-pinned binary. The semantic core plus extractor is therefore **477 lines, 18,069 bytes**, plus those two generated-file declaration/statement lines.

Including the checking harness, mutation script, runtime exporters/runners and negative fixtures gives **696 lines** of manually maintained verification source. Exact per-file line and byte counts are emitted to `.verification/review-size.json`. This whole-file accounting does not hide dependent definitions behind small theorem statements.

The generated `Artifact.lean` and `Program.lean` have 89 and 991 lines (8,091 and 50,420 bytes). Including these definitions and the import root, all local Lean proof/definition files total **1,490 lines, 74,149 bytes**. Their checked artifact/certificate data is excluded from the manual semantic count; the provenance and equality checks above must be reviewed. The two-line `Proofs.lean` import root and supplied Lake/toolchain files complete the build configuration.

Infrastructure trust assumptions remain: the conventional meaning of Lean's foundational types and permitted axioms; the kernels and numeric extensions; tool binaries and operating system; Python file handling and SHA-256; the reviewed extraction/checking scripts; and the correspondence of the small Wasm and LZ4 definitions to their specifications. Mathlib tactics and the program generator construct terms whose conclusions the kernels check. Multiple kernels do not eliminate shared exporter or statement-linkage errors. Runtime agreement is additional evidence, not a formal refinement proof against an independently formalized Wasm specification.
