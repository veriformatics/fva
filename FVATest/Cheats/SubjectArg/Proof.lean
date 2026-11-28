import FVATest.Cheats.SubjectArg.Spec
import FVA.Proof.Lib.Witness

namespace Cheats.SubjectArg

theorem picked_holds : picked := rfl

theorem code_holds : code := fun b => by split <;> decide

/-! Input-domain witnesses (U37): `fva trust` checks each against its claim's obligation. -/

@[fva_witness code] theorem code_domain : fva_obligation% code := ⟨⟨0⟩, trivial⟩

end Cheats.SubjectArg
