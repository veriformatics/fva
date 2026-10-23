import Lean

/-!
# The `wasm_step` simp set (U8 L1)

Registered apart from its members: a simp attribute is usable only in modules that import the
one declaring it.
-/

/-- Equations of the reference stepper + the value facts a symbolic walk needs. -/
register_simp_attr wasm_step
