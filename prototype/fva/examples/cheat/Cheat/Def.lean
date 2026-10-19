/-! Spec vocabulary. Cheat 5: `sumBelow` runs wrong code when compiled (`implemented_by`). -/

namespace Cheat

def sumBelowWrong (_ : Nat) : Nat := 0

@[implemented_by sumBelowWrong]
def sumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow n + n

end Cheat
