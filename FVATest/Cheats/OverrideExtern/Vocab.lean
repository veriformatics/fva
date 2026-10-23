import FVATest.Cheats.OverrideExtern.Lifted

/-! Vocabulary of cheat OverrideExtern. -/

namespace Cheats.OverrideExtern

/-- Addition, with a C implementation. -/
@[extern "lean_nat_add"] def add2 (a b : Nat) : Nat := a + b

end Cheats.OverrideExtern
