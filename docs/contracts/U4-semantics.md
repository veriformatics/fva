# U4 contract — Wasm execution semantics + claim forms (tier: kernel) — DRAFT

Purpose: the meaning of running a decoded module (U2 `Module`) with the reviewed numerics (U3), so claims about a `.wasm` artifact are statements about its executions (Decisions: Trusted base, Link path, Self-verification). Reviewed spec = `FVA/Spec/Exec/**`; verified impl = a fuel interpreter `FVA/Impl/Exec/**` proven equivalent; claim vocabulary = `FVA/Spec/Claims.lean`. Consumers: U5 (spec suite + difftest run the interpreter), U6 (type soundness over the small-step relation), U8 (proof library: symbolic execution over the interpreter), U14 (bench claims), U16.

## Spec (reviewed once) — Wasm 2.0 §4 for profile P
- S1 Runtime structure (§4.2): values (`i32`/`i64` = `BitVec 32/64`, `f32`/`f64` = bits, references = null t | function address | extern address); store (function instances: module code or host; tables; memories = byte list + optional max; globals; element and data instances); module instances; frames (locals + module instance); configuration = store × thread (frame + instruction sequence).
- S2 Administrative instructions (§4.2.13): `trap`, `ref` values, `invoke a`, `label_n{cont} instr* end`, `frame_n{F} instr* end`; block contexts and evaluation contexts as the spec defines them.
- S3 Reduction (§4.4): one rule per instruction of P (numeric via U3 relations, including NaN nondeterminism; parametric; variable; table; memory with bounds traps and little-endian access; control: block, loop, if, br, br_if, br_table, return, call, call_indirect with the dynamic type check; label/frame exit rules; trap propagation).
- S4 Host functions (§4.4.10): a host function's step is any result its contract allows (contract = relation on store, arguments, results/trap); FVA states contracts per import, never assumes behavior beyond them.
- S5 Instantiation (§4.5.4): external values for imports (type-checked against the module's import types), allocation, global initializers (constant expressions), active element/data segments applied in order, declarative/passive segments dropped as specified, start function invoked.
- S6 Claim forms (`FVA/Spec/Claims.lean`): `Returns m imports "f" args res` (every reduction from the invocation configuration that terminates yields `res`, and some terminates? — to fix with the consultant), `Traps`, memory-effect forms for the C ABI (pointer + length buffers in linear memory, result buffers), `∀`-quantification over every NaN result and every host behavior its contract allows.
- S7 Host math assumption (reviewed once, shared with U16): libc `log`/`log1p` imports return a binary64 within a stated ulp bound of `Real.log` (bound + domain cases as data, cited to the libc used by the subject's toolchain).

## Implementation
- I1 Fuel interpreter over the same configuration, kernel-evaluable (U2 shaping lessons), deterministic given a NaN-choice and a host oracle.
- I2 Theorems: interpreter soundness (a run to a result is a reduction sequence in S3) and completeness (every terminating reduction sequence is found with enough fuel, for some NaN/host choices); instantiation impl = S5.

## Evidence
- E1 official spec tests (control, memory, calls, tables, imports, globals, conversions …) through the interpreter (U5 runner); counts pinned.
- E2 difftest vs wasmtime (U5): Lean-predicted results as WAST; 0 mismatches on the corpus functions with sampled inputs.
- E3 planted semantic bugs fire (e.g. br_table default index off by one, memory bound check `<` vs `≤`, little-endian swap, call_indirect type check dropped).

## Open for the consultant
- C1 Small-step representation: evaluation contexts as the spec writes them vs a stack-machine configuration (WasmCert-Coq/-Isabelle style `lholed` contexts); reviewability vs proof cost.
- C2 Memory in the spec (`List UInt8`, function `Nat → UInt8` + size, or bytes as one numeral) and in the interpreter (kernel cost per load/store on 10⁴–10⁶-byte memories).
- C3 Nondeterminism (NaNs, host calls): relation-valued steps vs oracle parameters; what `Returns` must quantify over so that claims are neither vacuous nor unprovable.
- C4 Imports for dylink.0 modules (edgeR.so: memory, table, `__memory_base`, `__table_base`, stack pointer, R API + libc functions): what the claim fixes vs quantifies.
- C5 Termination: total vs partial correctness in `Returns`; fuel in claims vs existential fuel.
- C6 Which interpreter ↔ small-step direction each consumer needs (proofs by symbolic execution, counterexample theorems by evaluation, U6 progress/preservation).
