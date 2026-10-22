# U2 contract — Wasm syntax, binary grammar, decoder, `fva lift` (tier: kernel)

Purpose: tie a theorem's subject to the exact bytes of a `.wasm` artifact with no trusted lifter (Decisions: Link path, Trusted base, Self-verification). Reviewed-once spec = `FVA/Spec/Syntax.lean` + `FVA/Spec/Binary/*.lean`; verified impl = `FVA/Impl/Decode/*.lean`; untrusted glue = `fva lift` printer + `FVA/Lifted.lean` elaborators (kernel re-checks their output).

## Profile (P)
P = the productions of `FVA.Spec.Binary` = Wasm 2.0 binary format minus SIMD: types (i32 i64 f32 f64 funcref externref), multi-result func types, limits, memory/table/global types, imports + exports (func, table, memory, global), functions + local runs, tables, memories (memory index immediates = 0), globals, start, element segments (8 encodings), data segments (3), data count, custom sections (valid UTF-8 name + raw bytes, any position). Instructions: control, block types (empty | valtype | s33 index ≥ 0), reference, parametric (incl. typed select), variable, table, memory (loads/stores with memarg, size, grow, fill, copy, init, data.drop), numeric (all i32/i64/f32/f64 ops, conversions, sign extension 0xC0–0xC4, saturating truncation 0xFC 0–7). Decoding = syntax fidelity only: typing, index bounds, constant-expression validity, memory/table cardinality + limits = U6. `unsupported` = best-effort diagnostic for a recognized feature outside P (SIMD, atomics, EH, tail calls, typed function references, GC, shared/64-bit limits, multi-memory zero byte), first failure in byte order; outside T1–T3.

## Spec (reviewed once)
- S1 `Syntax`: abstract syntax of spec §2 for P; `Instr` nests `List Instr` (block/loop/if bodies); `Expr := List Instr`; `Func.locals : List (Nat × ValType)` = the encoded runs (expansion = U4, so a 2^32 − 1 run stays one entry); `Data.init : List UInt8`.
- S2 `ModuleB m bs` (+ `ULeb`/`SLeb`, `Vec`, `Name`, `InstrB`/`InstrsB`, `ElemB`, `DataB`, `CodeB`): spec §5 as relations on `List UInt8`: LEB length + unused-bit limits (non-minimal encodings allowed), IEEE bytes little-endian, names = UTF-8, sections in order with exact sizes, custom sections anywhere, func/code counts equal, data count = segment count when present, data indices only with a data count, local total < 2^32, trailing bytes forbidden.

## Implementation (kernel-shaped)
- I1 `decode : Nat → Nat → Except DecodeError Module` over a little-endian packed numeral + length. Internals use `Res` (`ok a v n | bad rem msg | unsup rem msg`, failures carry bytes-left, rebased at each sub-input, file offset = `len − rem`), `bif` on `Nat.blt`/`Nat.beq`, direct `Nat.land`/`Nat.shiftRight`/`Nat.pow` on hot paths, structural recursion on fuel = input length; instruction sequences iterate by tail calls (depth = block nesting), accumulate reversed; data segments = `Binary.leBytes k lit` (one numeral, never a byte loop); opcode dispatch = `Nat.blt` range tree + short `nth` table walks.
- I2 `decode_eq` proof = `kernel_rfl` (`FVA/Lifted.lean`): `Eq.refl` handed to the kernel's defeq check; no `DecidableEq` on the AST is needed (Lean 4.35 derives none for nested `List Instr`).
- I3 `fva lift <wasm> <Lifted.lean> --ns N`: `import FVA.Lifted`; `bytes := wasm_bytes% "<hex, file order>"` (elaborates to one raw numeral, O(n log n)); `len`; per-function `noncomputable def funcN`; `noncomputable def module`; fully qualified constructors; `theorem decode_eq : decode bytes len = .ok module := by kernel_rfl`. Same bytes → byte-identical file.

## Theorems (kernel-checked, no `sorry`, standard axioms only)
- T1 sound: `decode (pack b) b.length = .ok m → ModuleB m b`.
- T2 complete on P: `ModuleB m b → decode (pack b) b.length = .ok m` (fuel sufficiency: each step consumes ≥ 1 byte).
- T3 functional (corollary of T1–T2): `ModuleB m b → ModuleB m' b → m = m'`.
- T4 `pack` round-trip with length: `pack` + `b.length` determine `b`; `leBytes b.length (pack b) = b`.
- T5 dispatch tables (`numOp`, `loadOps`, `storeOps`, `varOps`, `fcInstr`) agree with the spec tables (`plainOps`, `memOps`, `idxOps`, `fcPlainOps`, `fcIdxOps`) on all 256 opcodes, by `decide`.

## Evidence (tests; each seen red on a planted bug first)
- E1 official testsuite @ 44f1503f9840: every `assert_malformed` binary module in the binary-format scripts → `malformed`; every binary module there in P decodes. Measured: 702/702 rejected, 56/56 decoded.
- E2 whole-module differential: Lean re-encoder (untrusted test tool) → `wasm-tools print` of original vs re-encoded match; corpus = testsuite modules in P, clang/rustc builds, uBO `lz4-block-codec.wasm` (1,226 B), R-universe `edgeR.so` 4.99.10 (96,558 B); mutant battery incl. wrong export binding + changed data/initializer byte.
- E3 planted bugs fire: overlong LEB accepted, wrong opcode mapping, dropped section-size check, wrong export binding each turn E1/E2 red.
- E4 performance (budget ≤ 1 ms/B user, edgeR ≤ 3 min), `lean <Lifted.lean>`, load ≈ 6 on 8 cores: uBO 1.3 s; lz4 C (14.5 KB) 10–12 s, 1.5 GB; edgeR (96.5 KB) 48–51 s, 3.1 GB (elaboration ≈ 21 s, kernel ≈ 28 s). Met without chunking. Before the kernel-shaped rewrite: lz4 C 32.7 s / 3.35 GB (`decide +kernel`, `Except`/`do`), edgeR 71 s with a decimal literal (28 s of it parsing the numeral). Kernel unfoldings (deterministic, lz4 C decode-only): 689K.
- E5 lift determinism: two runs → identical bytes; `fva trust` (U7) re-derives `bytes` and `len` from the file.
- Replay (U7 input): lz4 C export → `lake check --from-export` default 6.3 s; `--paranoid`: Lean paranoid, nanoda, con-leche, con-ron accept; lean4lean rejects (`unknown constant 'Char.ofNat'`: the export lacks the constant its string-literal expansion needs).

## Rulings on consultant-2 (C1–C4, D1–D6)
- C1 keep (relation `ModuleB` is the reviewed object; parser lemmas stay outside the spec). C2 keep nested syntax.
- C3/D2: P = grammar productions; validation → U6; `unsupported` diagnostics outside T1–T3 (Profile above).
- D3: side conditions live in `ModuleB` (data count presence, total locals < 2^32, section rank/uniqueness, literal `0x00` reserved bytes); each gets positive + negative fixtures.
- D4: the link binds bytes AND length (T4); U7 checks `bytes` and `len` against the file and the exact type of `decode_eq`; fixtures: appended zero byte, tampered length.
- D5/C4: `decode_eq`'s type stays fixed; chunked assembly (proved split equations + per-chunk decode theorems) only if a module exceeds the E4 budget — not triggered by the corpus.
- D6: `Func.locals` keeps encoded runs; fuel = remaining byte count, proved sufficient in T2; resource limits never report `malformed`/`unsupported`.
- D1: E2 compares the whole module (re-encoder + `wasm-tools print`) with the mutant battery above.
