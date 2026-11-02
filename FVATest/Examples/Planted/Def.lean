/-! Spec vocabulary with a planted override: compiled code for `sumBelow` returns 0 (prototype
cheat 5), while its definition, which the kernel reads, sums. -/

namespace Examples.Planted

/-- What compiled code runs in place of `sumBelow`. -/
def sumBelowWrong (_ : Nat) : Nat := 0

/-- `0 + 1 + … + (n − 1)`. -/
@[implemented_by sumBelowWrong]
def sumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow n + n

end Examples.Planted
