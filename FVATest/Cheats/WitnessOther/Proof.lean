import FVATest.Cheats.WitnessOther.Spec
import FVA.Proof.Lib.Witness

namespace Cheats.WitnessOther

theorem needed_holds : needed := fun _ h => h
theorem other_holds : other := fun _ h => congrArg (· + Clean.Lifted.len) h

@[fva_witness needed] theorem wrongClaim : fva_obligation% other := ⟨3, rfl⟩

private def otherDomain : Prop := ∃ n : Nat, n = 3

-- Defeq alone would admit this constant instead of the proposition replay must check.
@[fva_witness other] theorem defeqCandidate : otherDomain := ⟨3, rfl⟩
@[fva_witness other] theorem exactCandidate : fva_obligation% other := ⟨3, rfl⟩

end Cheats.WitnessOther
