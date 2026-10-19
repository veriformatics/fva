/-! Specification vocabulary for `toy.wasm` — part of the human-review surface. -/

namespace Toy

/-- `0 + 1 + … + (n - 1)`. -/
def sumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow n + n

end Toy
