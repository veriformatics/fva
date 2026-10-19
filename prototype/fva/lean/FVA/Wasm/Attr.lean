import Lean

/-- Symbolic-execution lemma set for lifted wasm (`FVA.Wasm.Exec`). -/
register_simp_attr wasm_exec

/-- BitVec→Nat lemmas as propositional rewrites (`FVA.Wasm.Arith`). -/
register_simp_attr wasm_arith
