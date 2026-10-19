# Deferred

One row each: finding → acceptance check.

- D1 Semantics subset too small for real code: no linear memory, `call`, globals, `br_table`, multi-value/typed blocks, `clz`/`ctz`/`popcnt`/`rotl`/`rotr`, floats, imports. → `fva lift` + `fva difftest` succeed on a clang `-O2` program exercising each (array sum over memory, recursive call, switch), with 0 mismatches over ≥1000 cases.
- D2 Lifter (`src/fva/lift.py`) sits in the trusted base. → decoding moves into Lean (`decode : ByteArray → Except String Module`, proven or kernel-evaluated on the pinned bytes), `fva trust` trustedBase lists no Python lifter, and cheat 1 (tampered lift) still FAILs.
- D3 Difftest token `trap` covers both trap and out-of-fuel. → Lean side reports `trap` vs `fuel` separately; a planted non-terminating semantics bug reports `fuel`, never agreement with a wasmtime trap.
- D4 `lake check` sandbox cannot resolve the `../../lean` path dependency, so replay checks our own export, not a sandboxed build. → FVA Lean package consumable from inside a project (vendored copy or git require); `lake check` rc 0 in `examples/toy` without `--from-export`, rc 1 in `examples/cheat`.
- D5 No informalization of the review surface (Intent: claimcheck). → `fva explain <lake-dir>` back-translates each surface theorem to English without seeing its docstring, then compares; on `examples/cheat` it flags `clamp_spec` (returns `x`) as disagreeing with "clamp" intent.
- D6 Agent packaging absent (Intent: REA-style agent use). → MCP server exposing lift/trust/difftest + an agent skill; an agent session with only the MCP tools verifies a new C function end to end.
- D7 Unified-path evidence covers one source language. → Rust `#![no_std]` clamp/gcd compiled to wasm32, lifted, same `Toy.Spec`-shaped theorems proven; report shows identical trusted base.
- D8 Lean-native subjects (mesh-repo style, implementation written in Lean) unsupported by link check: `fva trust` requires a lifted module. → `--subject <Lean module>` path that skips re-lift but enforces override audit; `fva trust` on schildep/verified-3d-mesh-intersection reports a surface within ±10 % of its stated 93 lines.
- D9 Symbolic execution scales unknown: `wasm_sim` on 11-instruction bodies runs in ~1–2 s. → benchmark on a ≥200-instruction function; proof check time recorded; if superlinear, switch to a verified step-function evaluator (`decide`/`cbv`) per straight-line block.
- D10 Statement closure treats every Lean core definition as trusted (e.g. `BitVec.slt`, `Nat.gcd`). → report flags core definitions whose meaning a reviewer must know, with their docstrings, in the review surface section.
