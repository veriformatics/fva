---
paths:
  - "prototype/fva/**"
---

# FVA prototype law

- Verification claim = `uv run fva trust <lake-dir>` PASS, never `lake build` alone: lake accepts `sorry`, custom axioms, `native_decide` over `implemented_by`, kernel bypass via `debug.skipKernelTC` + `addDecl` + vacuity macros in spec imports (all seven planted in `examples/cheat`, each must keep failing).
- Spec layout: claims = `Prop` defs in `<Lib>/Spec.lean`, which imports only reviewed modules (core, `FVA.Wasm.Semantics`, `<Lib>/Lifted`, `<Lib>/Def`); `<Lib>/Proof.lean` imports `Spec` + proves `theorem _ : <claim>`; `<Lib>.lean` imports `Proof`. Reverse imports let unreviewed `macro_rules`/notation rewrite spec text (cheat 7).
- Prototype check = `cd prototype/fva && uv run fva demo` rc 0 (toy PASS, cheat FAIL, difftest 0 mismatches); no other gate until IMPLEMENT.
- `lean/FVA/Wasm/Semantics.lean` = trusted base: keep it minimal + spec-shaped; proof conveniences go to `Exec.lean`/`Arith.lean`. Any semantics change → rerun difftest; it must fire on a planted bug (e.g. `remU` → `/` gives gcd mismatches).
- Simp lemmas over `exec`/BitVec must be propositional (`:= id rfl`, `id (BitVec.toNat_add …)`): an `rfl`-proved simp lemma is applied definitionally, so the kernel re-derives the whole step by unfolding `Nat.mod` on symbolic values → minutes or deep recursion (sum_to: >300 s → 2 s). Symbolic execution = `wasm_sim` (unrolls loops) / `wasm_step` (stops at loops, for invariant induction); BitVec→Nat = `simp only [wasm_arith, …]`.
- Lifted code compares with `0`, not `0#32`: case-split as `by_cases h : x = 0` so `wasm_sim [h]` rewrites `c ≠ 0` guards. Loop proofs: strong induction on the decreasing quantity with a linear fuel bound (`gcd_loop`: `3 * b + 20 ≤ F`).
- `.wasm` under `examples/` = committed verified artifact (`.gitignore` exception); `Lifted.lean` regenerates byte-identically from it via `fva lift`.
- `lake check` sandbox mounts the project dir alone → the `../../lean` path dep is invisible; replay runs `--from-export` on `leanexport` output.
- `fva explain` = advisory, LLM text never enters a verdict; rc 0 only when trust PASS + every intent `matches`. Model-proposed inputs only — every displayed value is computed (Lean `FVA.Explain.run` / wasmtime). Pass 1 must get elaborated statements (`FVA.Explain.shapes`), since macros in spec imports rewrite source text (cheat 7 hits `sum_to_spec`, `sum_to_zero`, `sum_to_seven`). `lean/FVA/Explain.lean` = tooling outside the trusted base, kept out of the `FVA` root import (`import Lean` would enter every project's import closure); `fva explain` builds it on demand. Lean `#eval` buffers stdout → results go to a flushed file. Saved `examples/*/fva-explain.json` = committed review artifacts; a prompt/schema change in `explain.py` makes them STALE (rc 1) → regenerate with `--force` + commit them in the same unit.
