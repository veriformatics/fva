import FVATest.Subjects.EdgerCpm.Body
import FVATest.Subjects.EdgerCpm.Exists
import FVA.Proof.Lib.Witness

/-! The S4 claim: the existence clause (`exists_admissible`, a loader-prepared witness for every
covered input) and every admissible call (`body_returns`, from the facts `Admissible` carries). -/

namespace Subjects.EdgerCpm

theorem claim_holds : claim :=
  ⟨exists_admissible, fun x H l s inst hD hadm nth => by
    obtain ⟨_, hdata, ⟨alloc, free, heap, blocks, ready, hlink, hA, hr, hsep⟩, hkc, hy, hl, hd,
      hc⟩ := hadm
    exact body_returns x H l s inst alloc free heap blocks ready hD hdata hlink hA hr hsep hkc hy
      hl hd hc nth⟩

/-! Input-domain witness (U37): one gene × one library; `fva trust` checks it against the
claim's obligation. -/

private def oneGene : Input := ⟨1, 1, fun _ _ => 0, fun _ => 1⟩

private theorem oneGene_domain : Domain oneGene := by norm_num [oneGene, Domain]

@[fva_witness claim] theorem claim_domain : fva_obligation% claim := by
  obtain ⟨H, l, s, inst, h⟩ := exists_admissible oneGene oneGene_domain
  exact ⟨⟨oneGene, oneGene_domain⟩, oneGene, H, l, s, inst, oneGene_domain, h, 0, trivial⟩

end Subjects.EdgerCpm
