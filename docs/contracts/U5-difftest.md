# U5 contract — `fva difftest`: Lean-predicted WAST checked by wasmtime (tier: data)

Purpose: per-artifact evidence that the reviewed execution spec (U4) agrees with a production engine on the instruction mix a real compiler emits (Decisions: Trusted base — difftest = evidence for the specs, not proof). The official-script runner half of U5 already ships as `scripts/test-spec` (U4 E1). Consumer = a human or agent who reads a mismatch as a spec/stepper/engine disagreement; a defect here costs a false alarm (rerun, inspect) or a missed disagreement (the official scripts still run), never a verdict.

## Behavior
- `fva difftest <file.wasm>... [--cases N] [--seed S] [--fuel F] [--export NAME]... [--keep DIR] [--json]`: per module, per exported function whose parameters are numbers or references, N cases (default 32) on a fresh instantiation; one WAST script per function, run by `wasmtime wast` (pinned) in parallel; rc 0 = every script passes, 1 = a mismatch or a module FVA cannot run, 2 = usage.
- Prediction = the reference stepper `FVA.Wasm.Exec.Ref` (proven sound vs `Step`) on the same command sequence wasmtime runs: providers, subject, probe, then per case an optional input fill and the call.
- Imports: one provider module per import module name, encoded by `FVA.Tool.Encode` and embedded as `(module binary …)`: functions = `unreachable` stubs of the import's type, memories + tables with the import's limits, globals zero except a mutable i32 `__stack_pointer` = the first memory's byte size. Every provider is wasm, so no host function runs on either side.
- Probe module (also encoded): imports the subject's memory where it is observable (the subject's export or its provider) and exports `fill(lo, len, seed)` (xorshift32 bytes) and `digest(lo, len) → i64` (FNV-1a 64). Lean evaluates `digest` natively over the predicted bytes; wasmtime runs the wasm.
- Assertions per case: the call's outcome (`assert_return` with exact values, `assert_trap`); then `digest` over each merged range the call wrote (Lean's write log); then every mutable exported global of every instance.
- Choice points (`Ref.uniqueStep` = false outside trap propagation): a NaN result makes the case a choice case: NaN float results assert their class (`nan:arithmetic` for a quiet NaN), memory + globals go unchecked, and the next case starts on fresh instances. A grow keeps exact assertions (both engines grow when it fits); the report marks such cases.
- Fuel exhaustion (default 300,000 steps per call) drops the case: wasmtime never sees it, the Lean state rolls back.
- Report: per function `✓ cases/assertions` or `✗` + the first failing directive (wasmtime stops at the first), its case, Lean's prediction and wasmtime's message; `--json` = the same data.

## Implementation notes
- Memory mirror: the stepper's memory is a closure chain over writes; the runner logs each store's range (`.store`/`.storePacked` redexes; bulk ops reduce to byte stores) and every 64 writes rewrites each memory as a 4 KiB-chunk array read back through the spec's own bytes (extensionally equal when the log is complete; a missed write shows as a mismatch, never as a silent pass on bytes it covers).
- `uniqueStep`, `seqTraps` + `runDet` move to `FVA/Impl/Exec/Det.lean` (definitions), proofs stay in `FVA/Proof/Exec/Det.lean`; WAST literal + generator helpers move from `FVATest/FloatDiff.lean` to `FVA/Tool/Wast.lean`; the module encoder moves from `FVATest/Encode.lean` to `FVA/Tool/Encode.lean`.

## Evidence
- V1 gate step `scripts/test-difftest`: the corpus (uBO codec, lz4 C + Rust builds, edgeR) at a fixed seed; per-module assertion counts pinned; rc 0.
- V2 planted bugs fire (recorded in `.claude/rules/fva-checks.md`): a spec-shared memory helper (little-endian `write` byte order) and an impl op (`i32.rotl` direction) each produce a mismatch on the corpus.
- V3 live spot-check: edgeR (dylink, 151 imports, float code) and both lz4 builds run end to end; counts + wall-clock recorded here.

## Results
- V1: `scripts/test-difftest` in the gate (after `test-spec`): fast 151 functions, 21,605 assertions ≈ 24 s; full 172,063 (pins at seed 1, fuel 300,000).
- V2 (`.scratch/u5/plant-v2.py`, 16 cases on uBO + lz4 C/Rust): big-endian `MemInst.write` → rc 1, 4 functions fail; `ishrU` filling with the sign bit → rc 1, 8 functions fail (the probe's xorshift `fill` uses `shr_u`); restored → rc 0.
- V3: uBO 4 + lz4 C 2 + lz4_flex 2 functions, 32 cases: 788 assertions, ≈ 18 s wall; edgeR (dylink.0, 151 stub imports) 143 functions: 2 cases 21,406 assertions ≈ 11 s, 16 cases 171,275 ≈ 32 s (88 s CPU); NaN choice cases occur in edgeR float code (e.g. `spline_`, `compute_offsets`) and pass under the class patterns. Most edgeR cases trap in stub imports (R API); the pure numeric helpers return.
- Cost: the stepper runs ≈ 3 µs/step on lz4 (walks + list rebuild per step); an exhausted case costs ≈ 1 s at the default fuel. The optimized machine (D30) is the lever if difftest needs longer runs.

