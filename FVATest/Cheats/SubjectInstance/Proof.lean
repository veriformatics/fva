import FVATest.Cheats.SubjectInstance.Spec
import FVA.Proof.Lib.Witness

namespace Cheats.SubjectInstance

theorem grows_holds : grows := fun _ => trivial

theorem reads_holds : reads := fun _ => rfl

/-! Input-domain witnesses (U37): `fva trust` checks each against its claim's obligation. -/

@[fva_witness reads] theorem reads_domain : fva_obligation% reads := ⟨⟨0⟩, trivial⟩
@[fva_witness grows] theorem grows_domain : fva_obligation% grows := ⟨⟨0⟩, trivial⟩

end Cheats.SubjectInstance
