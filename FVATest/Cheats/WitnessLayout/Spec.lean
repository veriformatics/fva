import FVATest.Cheats.Clean.Lifted

namespace Cheats.WitnessLayout

@[fva_claim] def length : Prop :=
  ∀ n : Nat, n = Clean.Lifted.len → n = Clean.Lifted.len

-- Exact type, wrong module. Mention the subject here too to isolate [layout].
@[fva_witness length] theorem misplaced : ∃ n : Nat, n = Clean.Lifted.len :=
  ⟨Clean.Lifted.len, rfl⟩

end Cheats.WitnessLayout
