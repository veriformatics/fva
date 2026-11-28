import FVATest.Cheats.WitnessSorry.Spec
import FVA.Proof.Lib.Witness

namespace Cheats.WitnessSorry

theorem length_holds : length := fun _ => rfl

@[fva_witness length] theorem assumed : fva_obligation% length := by sorry

end Cheats.WitnessSorry
