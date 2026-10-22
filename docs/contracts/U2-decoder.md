# U2 contract — Wasm syntax, binary grammar, decoder, `fva lift` (tier: kernel)

Purpose: tie a theorem's subject to the exact bytes of a `.wasm` artifact with no trusted lifter (Decisions: Link path, Trusted base, Self-verification). Reviewed-once spec = `FVA/Spec/Syntax.lean` + `FVA/Spec/Binary.lean`; verified impl = `FVA/Impl/Decode.lean`; glue = `fva lift` (bytes → `Lifted.lean` text, re-checked by the kernel).

## Profile (P)
Wasm 2.0 binary format minus SIMD: types (i32 i64 f32 f64 funcref externref), func types (multi-result), limits, memory/table/global types, imports + exports (func, table, memory, global), functions + locals, tables, memories (≤ 1; memory index immediates must be 0), globals, start, element segments (all 8 encodings, active/passive/declarative), data segments (3 encodings), data count, custom sections (name + raw bytes, any position). Instructions: control (unreachable nop block loop if/else br br_if br_table return call call_indirect), block types (empty | valtype | s33 type index), reference (ref.null ref.is_null ref.func), parametric (drop select, typed select), variable, table (get set size grow fill copy init elem.drop), memory (all loads/stores with memarg, size grow, fill copy init data.drop), numeric (all i32/i64/f32/f64 ops, conversions, sign-extension 0xC0–0xC4, saturating truncation 0xFC 0–7), constant expressions. Out of P → `unsupported <feature>` (never "malformed"): SIMD (0xFD), atomics (0xFE), exception handling, tail calls, multi-memory, memory64, GC, extended-const.

## Spec (reviewed once)
- S1 `Syntax`: abstract syntax mirroring the spec's §2 for P; nested `Instr` (block/loop/if carry bodies).
- S2 `Encodes : Module → List UInt8 → Prop` mirroring the spec's §5 binary format: LEB128 relations with the spec's length + unused-bit limits (u32 ≤ 5 bytes, s33 ≤ 5, s64/u64 ≤ 10), IEEE bytes little-endian, names = vec(byte) that is well-formed UTF-8, sections in the spec's order with exact sizes, custom sections anywhere, `func`/`code` counts equal, data count = data segment count when present, trailing bytes forbidden.

## Implementation
- I1 `decode : Nat → Nat → Except DecodeError Module` over a little-endian packed byte Nat + length (kernel-fast: `% 256`, `/ 256` on GMP Nats); `DecodeError` = byte offset + reason (`malformed …` | `unsupported …`).
- I2 `Module.beq` hand-written structural equality + `LawfulBEq` (deriving rejects the nested `Instr` in Lean 4.35, checked).
- I3 `fva lift <wasm> <Lifted.lean> --ns N`: emits `bytes : Nat` (literal), `len`, readable `module : Module`, `theorem decode_eq : decode bytes len = .ok module := by decide +kernel`; re-running on the same bytes = byte-identical file.

## Theorems (all kernel-checked, no `sorry`, standard axioms only)
- T1 sound: `decode (pack b) b.length = .ok m → Encodes m b`.
- T2 complete on P: `Encodes m b → decode (pack b) b.length = .ok m`.
- T3 functional (corollary of T1–T2): `Encodes m b → Encodes m' b → m = m'`.
- T4 `pack` round-trip: the packed Nat of `b` reads back `b`.

## Evidence (tests; each seen red on a planted bug first)
- E1 official testsuite @ 44f1503f9840: every `assert_malformed` binary module in `binary.wast`, `binary-leb128.wast`, `custom.wast`, `utf8-*.wast` → `decode` = `.error` (malformed); every module in P from those scripts decodes; modules outside P → `unsupported`.
- E2 corpus differential vs `wasm-tools print`: per function, the opcode + immediate stream matches; section counts match. Corpus: testsuite modules in P, clang/rustc spike builds, uBlock Origin `lz4-block-codec.wasm` (1,226 B), R-universe `edgeR.so` 4.99.10 (96,558 B, dylink.0, imports).
- E3 planted bugs fire: an overlong LEB accepted, a wrong opcode mapping, a dropped section-size check each turn E1/E2 red.
- E4 performance: `decode_eq` kernel check time + peak RSS recorded per corpus module; budget ≤ 1 ms/byte user CPU, edgeR.so ≤ 3 min; if over, per-function chunked decode theorems (decision recorded in this file).
- E5 `fva lift` determinism: two runs → identical bytes; `fva trust` (U7) re-derives the literal from the file.

## Open for the consultant
- C1 Is `Encodes` on `List UInt8` the right reviewed object, or should the spec decode function itself be the spec (smaller review surface, weaker independence)?
- C2 Nested `Instr` vs flat instruction stream + structured-control well-formedness (semantics + type-soundness proofs downstream).
- C3 T2 completeness scope: P only, with `unsupported` outside — sufficient for "decoder sound + complete for the supported profile" (Decisions: Self-verification)?
- C4 Packed-Nat kernel decoding at 96.5 KB: risks + alternatives (chunking boundary, `Nat.toDigits`-free reads).

## Rulings on consultant-2 (C1–C4, D1–D6)
- C1 keep (relation `ModuleB` is the reviewed object; parser lemmas stay outside the spec). C2 keep (nested syntax; `Instr`/`Instrs` mutual so `DecidableEq` derives kernel-reducibly).
- C3/D2: P = the productions of `FVA.Spec.Binary` (Wasm 2.0 §5 minus SIMD). Decoding is syntax fidelity only: typing, index bounds, constant-expression validity, memory/table cardinality and limits belong to U6. `unsupported` = best-effort diagnostic for a recognized feature outside P, first error in byte order; it is outside T1–T3.
- D3: side conditions are part of `ModuleB` (data count presence when code uses data indices, total locals < 2^32, section rank/uniqueness, literal `0x00` reserved bytes); each gets positive + negative fixtures.
- D4: the link binds bytes AND length: T4 states `pack b` with `b.length`; U7 checks the literal and `len` against the file and the exact type of `decode_eq`; fixtures: appended zero byte, tampered length.
- D5/C4: the lifted theorem type stays `decode bytes len = .ok module`; when one kernel check exceeds the budget it is assembled from proved split equations (exact spans, no gaps/overlap/reordering) + per-chunk decode theorems. Measured (E4): lz4 C 14.5 KB 32 s user / 3.4 GB (decode ≈ 12 s, structural comparison ≈ 16 s, elaboration ≈ 7 s), lz4_flex 25.3 KB 49 s / 4.9 GB ⇒ chunking needed before edgeR.
- D6: `Func.locals` keeps the encoded runs `List (Nat × ValType)` (expansion = U4); fuel = remaining byte count, proved sufficient in T2 (each step consumes ≥ 1 byte); operational limits report resource exhaustion, never `malformed`/`unsupported`.
- D1: E2 compares the whole module: Lean re-encoder (untrusted test tool) → `wasm-tools print` of original vs re-encoded must match; mutant battery adds a wrong export binding and a changed data/initializer byte.
