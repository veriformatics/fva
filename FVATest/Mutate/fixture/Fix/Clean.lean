/-! Mutation-check fixture (U12 E1): one outcome per definition. -/

namespace Fix

/-- Pinned by `Fix.inc_two`: every mutant is killed by a theorem. -/
def inc (n : Nat) : Nat := n + 1

/-- Pinned by the test (`fixtest` prints `dbl 3`): killed by the test alone. -/
def dbl (n : Nat) : Nat := n * 2

/-- A literal change makes the value's proof ill-typed: unviable. -/
def mk (n : Nat) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩

/-- `Fix.keep`'s type mentions it: a change breaks that downstream definition. -/
def width : Nat := 1

end Fix
