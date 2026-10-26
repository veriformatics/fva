import FVATest.Subjects.EdgerCpm.Body
import FVATest.Subjects.EdgerCpm.Exists

/-! The S4 claim: the existence clause (`exists_admissible`, a loader-prepared witness for every
covered input) and every admissible call (`body_returns`, from the facts `Admissible` carries). -/

namespace Subjects.EdgerCpm

theorem claim_holds : claim :=
  ⟨exists_admissible, fun x H l s inst hD hadm nth => by
    obtain ⟨_, hdata, ⟨alloc, free, heap, blocks, ready, hlink, hA, hr, hsep⟩, hkc, hy, hl, hd,
      hc⟩ := hadm
    exact body_returns x H l s inst alloc free heap blocks ready hD hdata hlink hA hr hsep hkc hy
      hl hd hc nth⟩

end Subjects.EdgerCpm
