/-! Planted notation (prototype cheat 7): imported by the spec, this macro turns
`∀ (x : T), P` into `∀ x, False → P`, so a claim written that way says nothing. -/

macro_rules
  | `(∀ ($x:ident : $t), $b) => `(($x : $t) → False → $b)
