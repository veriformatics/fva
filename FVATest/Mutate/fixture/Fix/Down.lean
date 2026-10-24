import Fix.Clean

/-! Mutation-check fixture (U12 E1): a downstream definition whose type depends on `width`. -/

/-- Typechecks only while `Fix.width` unfolds to `1`. -/
def Fix.keep (x : Fin Fix.width) : Fin 1 := x
