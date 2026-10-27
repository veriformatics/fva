-- Generated numerical witnesses; interval inclusions and logarithms checked in Lean.
import Proofs.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TMM
def rnaSummary (i : ℕ) : Box :=
  match i with
  | 0 => ⟨(549411035839 / 20000000000000 : ℚ), (27470551791951 / 1000000000000000 : ℚ)⟩
  | 1 => ⟨(29227292025373 / 100000000000000 : ℚ), (292272920253731 / 1000000000000000 : ℚ)⟩
  | 2 => ⟨(165582148247453 / 1000000000000000 : ℚ), (82791074123727 / 500000000000000 : ℚ)⟩
  | 3 => ⟨(-1 / 1000000000000000 : ℚ), (1 / 1000000000000000 : ℚ)⟩
  | 4 => ⟨(-159036908025723 / 1000000000000000 : ℚ), (-79518454012861 / 500000000000000 : ℚ)⟩
  | 5 => ⟨(-25386130001683 / 1000000000000000 : ℚ), (-12693065000841 / 500000000000000 : ℚ)⟩
  | 6 => ⟨(5190862369503 / 250000000000000 : ℚ), (20763449478013 / 1000000000000000 : ℚ)⟩
  | _ => ⟨0,0⟩
theorem rna_valid : ∀ i ∈ List.range 7, validPairs (pairsOfMask rnaMasks i) i := by
  decide +kernel
theorem rna_summary_contains : ∀ i ∈ List.range 7,
    (rnaSummary i).lo ≤ (rawBox (pairsOfMask rnaMasks i) i).lo ∧
    (rawBox (pairsOfMask rnaMasks i) i).hi ≤ (rnaSummary i).hi := by
  decide +kernel
theorem rna_summary_sound (i : ℕ) (hi : i ∈ List.range 7) :
    (rnaSummary i).Holds (raw (pairsOfMask rnaMasks i) i) := by
  exact widen_sound (rawBox_sound _ _ (rna_valid i hi))
    (rna_summary_contains i hi).1 (rna_summary_contains i hi).2
def rnaEndpoints (i : ℕ) : Box :=
  match i with
  | 0 => ⟨(2454220003911511 / 2500000000000000 : ℚ), (2454220003916511 / 2500000000000000 : ℚ)⟩
  | 1 => ⟨(2558619385723367 / 2000000000000000 : ℚ), (2558619385727367 / 2000000000000000 : ℚ)⟩
  | 2 => ⟨(2254159189727513 / 2000000000000000 : ℚ), (2254159189731513 / 2000000000000000 : ℚ)⟩
  | 3 => ⟨(2387718820226961 / 2500000000000000 : ℚ), (2387718820231961 / 2500000000000000 : ℚ)⟩
  | 4 => ⟨(4073280580271819 / 5000000000000000 : ℚ), (4073280580281819 / 5000000000000000 : ℚ)⟩
  | 5 => ⟨(4655733599463999 / 5000000000000000 : ℚ), (4655733599473999 / 5000000000000000 : ℚ)⟩
  | 6 => ⟨(4875628755702897 / 5000000000000000 : ℚ), (4875628755712897 / 5000000000000000 : ℚ)⟩
  | _ => ⟨1,1⟩
def rna_0_lo : Box := ⟨(-18481738458174179 / 1000000000000000000 : ℚ), (-9240869229087069 / 500000000000000000 : ℚ)⟩
theorem rna_0_lo_sound : rna_0_lo.Holds (Real.log ((2454220003911511 / 2500000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2454220003911511 / 2500000000000000 : ℚ) (-45779996088489 / 4954220003911511 : ℚ) 24 rna_0_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_0_hi : Box := ⟨(-2310217307017109 / 125000000000000000 : ℚ), (-18481738456136831 / 1000000000000000000 : ℚ)⟩
theorem rna_0_hi_sound : rna_0_hi.Holds (Real.log ((2454220003916511 / 2500000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2454220003916511 / 2500000000000000 : ℚ) (-45779996083489 / 4954220003916511 : ℚ) 24 rna_0_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_0_enclosed :
    (rnaEndpoints 0).Holds (factor rnaMasks 0) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 0 (by decide))
    rna_0_lo_sound rna_0_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def rna_1_lo : Box := ⟨(246320630003842733 / 1000000000000000000 : ℚ), (123160315001921387 / 500000000000000000 : ℚ)⟩
theorem rna_1_lo_sound : rna_1_lo.Holds (Real.log ((2558619385723367 / 2000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2558619385723367 / 2000000000000000 : ℚ) (558619385723367 / 4558619385723367 : ℚ) 24 rna_1_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_1_hi : Box := ⟨(61580157501351519 / 250000000000000000 : ℚ), (246320630005406117 / 1000000000000000000 : ℚ)⟩
theorem rna_1_hi_sound : rna_1_hi.Holds (Real.log ((2558619385727367 / 2000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2558619385727367 / 2000000000000000 : ℚ) (558619385727367 / 4558619385727367 : ℚ) 24 rna_1_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_1_enclosed :
    (rnaEndpoints 1).Holds (factor rnaMasks 1) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 1 (by decide))
    rna_1_lo_sound rna_1_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def rna_2_lo : Box := ⟨(119629857997459943 / 1000000000000000000 : ℚ), (7476866124841249 / 62500000000000000 : ℚ)⟩
theorem rna_2_lo_sound : rna_2_lo.Holds (Real.log ((2254159189727513 / 2000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2254159189727513 / 2000000000000000 : ℚ) (254159189727513 / 4254159189727513 : ℚ) 24 rna_2_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_2_hi : Box := ⟨(119629857999234441 / 1000000000000000000 : ℚ), (59814928999617241 / 500000000000000000 : ℚ)⟩
theorem rna_2_hi_sound : rna_2_hi.Holds (Real.log ((2254159189731513 / 2000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2254159189731513 / 2000000000000000 : ℚ) (254159189731513 / 4254159189731513 : ℚ) 24 rna_2_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_2_enclosed :
    (rnaEndpoints 2).Holds (factor rnaMasks 2) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 2 (by decide))
    rna_2_lo_sound rna_2_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def rna_3_lo : Box := ⟨(-11488072562538241 / 250000000000000000 : ℚ), (-45952290250152923 / 1000000000000000000 : ℚ)⟩
theorem rna_3_lo_sound : rna_3_lo.Holds (Real.log ((2387718820226961 / 2500000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2387718820226961 / 2500000000000000 : ℚ) (-112281179773039 / 4887718820226961 : ℚ) 24 rna_3_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_3_hi : Box := ⟨(-9190458049611783 / 200000000000000000 : ℚ), (-22976145124029437 / 500000000000000000 : ℚ)⟩
theorem rna_3_hi_sound : rna_3_hi.Holds (Real.log ((2387718820231961 / 2500000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (2387718820231961 / 2500000000000000 : ℚ) (-112281179768039 / 4887718820231961 : ℚ) 24 rna_3_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_3_enclosed :
    (rnaEndpoints 3).Holds (factor rnaMasks 3) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 3 (by decide))
    rna_3_lo_sound rna_3_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def rna_4_lo : Box := ⟨(-102494599138027957 / 500000000000000000 : ℚ), (-204989198276055873 / 1000000000000000000 : ℚ)⟩
theorem rna_4_lo_sound : rna_4_lo.Holds (Real.log ((4073280580271819 / 5000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (4073280580271819 / 5000000000000000 : ℚ) (-926719419728181 / 9073280580271819 : ℚ) 24 rna_4_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_4_hi : Box := ⟨(-20498919827360089 / 100000000000000000 : ℚ), (-204989198273600849 / 1000000000000000000 : ℚ)⟩
theorem rna_4_hi_sound : rna_4_hi.Holds (Real.log ((4073280580281819 / 5000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (4073280580281819 / 5000000000000000 : ℚ) (-926719419718181 / 9073280580281819 : ℚ) 24 rna_4_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_4_enclosed :
    (rnaEndpoints 4).Holds (factor rnaMasks 4) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 4 (by decide))
    rna_4_lo_sound rna_4_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def rna_5_lo : Box := ⟨(-14267684050372443 / 200000000000000000 : ℚ), (-35669210125931087 / 500000000000000000 : ℚ)⟩
theorem rna_5_lo_sound : rna_5_lo.Holds (Real.log ((4655733599463999 / 5000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (4655733599463999 / 5000000000000000 : ℚ) (-344266400536001 / 9655733599463999 : ℚ) 24 rna_5_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_5_hi : Box := ⟨(-2853536809988573 / 40000000000000000 : ℚ), (-17834605062428571 / 250000000000000000 : ℚ)⟩
theorem rna_5_hi_sound : rna_5_hi.Holds (Real.log ((4655733599473999 / 5000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (4655733599473999 / 5000000000000000 : ℚ) (-344266400526001 / 9655733599473999 : ℚ) 24 rna_5_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_5_enclosed :
    (rnaEndpoints 5).Holds (factor rnaMasks 5) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 5 (by decide))
    rna_5_lo_sound rna_5_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def rna_6_lo : Box := ⟨(-25188840772118939 / 1000000000000000000 : ℚ), (-12594420386059449 / 500000000000000000 : ℚ)⟩
theorem rna_6_lo_sound : rna_6_lo.Holds (Real.log ((4875628755702897 / 5000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (4875628755702897 / 5000000000000000 : ℚ) (-124371244297103 / 9875628755702897 : ℚ) 24 rna_6_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def rna_6_hi : Box := ⟨(-12594420385033961 / 500000000000000000 : ℚ), (-25188840770067881 / 1000000000000000000 : ℚ)⟩
theorem rna_6_hi_sound : rna_6_hi.Holds (Real.log ((4875628755712897 / 5000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (4875628755712897 / 5000000000000000 : ℚ) (-124371244287103 / 9875628755712897 : ℚ) 24 rna_6_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rna_6_enclosed :
    (rnaEndpoints 6).Holds (factor rnaMasks 6) := by
  exact exp_enclosure (center_summary_sound rnaMasks rnaSummary rna_summary_sound 6 (by decide))
    rna_6_lo_sound rna_6_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem rna_enclosed (i : ℕ) (hi : i ∈ List.range 7) :
    (rnaEndpoints i).Holds (factor rnaMasks i) := by
  simp only [List.mem_range] at hi
  interval_cases i
  · exact rna_0_enclosed
  · exact rna_1_enclosed
  · exact rna_2_enclosed
  · exact rna_3_enclosed
  · exact rna_4_enclosed
  · exact rna_5_enclosed
  · exact rna_6_enclosed
end TMM
