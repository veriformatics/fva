---
paths:
  - "FVA/Proof/Lib/Block*.lean"
  - "FVATest/Subjects/Lz4C/Eval/**"
---

# Engine C (verified block evaluator) law

- Engine = `blockEval k s f es` (`FVA/Proof/Lib/BlockEval.lean`): `k` reference-stepper steps (`seqUnique` + `seq`) + each step's access; `blockEval_until` transports `Until` across the whole block from one evaluator equation, so the engine adds no execution semantics (decoder ruling: `.agent/spec.md` Decisions, U20).
- Per block: `wasm_eval k [facts]` on an `Until … (Within R W) Q (C.fill cfg)` goal with a literal configuration (`BContext.fill` keeps the operand values saved below labels/frames) → two goals: `TraceOK` (`wasm_trace [facts]`) and `Until` from the block's end. `block not computed: <term>` = simp stopped at `<term>`: supply the branch fact, memory bound or local value it names, or end the block earlier. Per loop: an invariant + induction on a decreasing count (fuel), one `wasm_eval` per iteration path. Per call: the callee contract (`Eval/S1`, `S2`) + footprint widening + `Until.trans`.
- Normal forms the engine needs:
  - i32 constants near 2^32 stay symbolic: `iadd x (2^32 − k)` rewrites to `x − k` at `block_simp` priority 2000 (`iadd_mask1`/`iadd_mask4`); a concrete state value like `ofNat32 (base + 4294967295)` with symbolic `base` drives the kernel into deep recursion (`Eval/Backward2.lean` = the repaired form: symbolic BitVec bases + modular-add equations).
  - The 19 decoder locals stay an explicit list (`Eval/SegCommon.lean` `cLocals`), so the evaluator reads and updates them by computation; an abstract `ls` is decomposed once (`c_decompose`).
  - A write-conditioned load needs its byte-range fact up front (`S1`'s eight range facts).
  - Nested labels inside one block need `maxRecDepth` 4000–6000 for the simp run (no kernel bypass).
- Fallback for a block the evaluator handles badly: checkpoint-1 stepping (`wasm_cstepu` + `wasm_within`, `AGENT.md`); both yield `Until`/`Within`, so the proofs compose. A failure in the shared evaluator or one that blocks a milestone reopens the engine ruling.
