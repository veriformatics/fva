import FVATest.Cheats.Clean.Lifted

namespace Cheats.WitnessOther

@[fva_claim] def needed : Prop :=
  ∀ n : Nat, n = Clean.Lifted.len → n = Clean.Lifted.len

@[fva_claim] def other : Prop :=
  ∀ n : Nat, n = 3 → n + Clean.Lifted.len = 3 + Clean.Lifted.len

end Cheats.WitnessOther
