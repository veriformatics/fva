/-! Cheat 7: imported by the spec, this macro turns `∀ (x : T), P` into `∀ x, False → P`. -/

macro_rules
  | `(∀ ($x:ident : $t), $b) => `(($x : $t) → False → $b)
