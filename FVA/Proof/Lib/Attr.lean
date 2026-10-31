import Lean

/-!
# The `wasm_step` and `wasm_access` simp sets (U8 L1, U19 A3)

Registered apart from its members: a simp attribute is usable only in modules that import the
one declaring it.
-/

/-- Equations of the reference stepper + the value facts a symbolic walk needs. -/
register_simp_attr wasm_step

/-- Equations of the access checker (`FVA.Wasm.Exec.Ref.access`) on symbolic configurations. -/
register_simp_attr wasm_access
