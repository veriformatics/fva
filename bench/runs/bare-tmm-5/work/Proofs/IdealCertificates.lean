-- Generated numerical witnesses; interval inclusions and logarithms checked in Lean.
import Proofs.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TMM
def idealSummary (i : ℕ) : Box :=
  match i with
  | 0 => ⟨(19789905033899 / 1000000000000000 : ℚ), (197899050339 / 10000000000000 : ℚ)⟩
  | 1 => ⟨(29227292025373 / 100000000000000 : ℚ), (292272920253731 / 1000000000000000 : ℚ)⟩
  | 2 => ⟨(91187234549491 / 500000000000000 : ℚ), (182374469098983 / 1000000000000000 : ℚ)⟩
  | 3 => ⟨(-1 / 1000000000000000 : ℚ), (1 / 1000000000000000 : ℚ)⟩
  | 4 => ⟨(-159036908025723 / 1000000000000000 : ℚ), (-79518454012861 / 500000000000000 : ℚ)⟩
  | 5 => ⟨(-25386130001683 / 1000000000000000 : ℚ), (-12693065000841 / 500000000000000 : ℚ)⟩
  | 6 => ⟨(488043810059 / 250000000000000 : ℚ), (1952175240237 / 1000000000000000 : ℚ)⟩
  | _ => ⟨0,0⟩
theorem ideal_valid : ∀ i ∈ List.range 7, validPairs (pairsOfMask idealMasks i) i := by
  decide +kernel
theorem ideal_summary_contains : ∀ i ∈ List.range 7,
    (idealSummary i).lo ≤ (rawBox (pairsOfMask idealMasks i) i).lo ∧
    (rawBox (pairsOfMask idealMasks i) i).hi ≤ (idealSummary i).hi := by
  decide +kernel
theorem ideal_summary_sound (i : ℕ) (hi : i ∈ List.range 7) :
    (idealSummary i).Holds (raw (pairsOfMask idealMasks i) i) := by
  exact widen_sound (rawBox_sound _ _ (ideal_valid i hi))
    (ideal_summary_contains i hi).1 (ideal_summary_contains i hi).2
def idealEndpoints (i : ℕ) : Box :=
  match i with
  | 0 => ⟨(975527 / 1000000 : ℚ), (121941 / 125000 : ℚ)⟩
  | 1 => ⟨(1281083 / 1000000 : ℚ), (320271 / 250000 : ℚ)⟩
  | 2 => ⟨(573877 / 500000 : ℚ), (229551 / 200000 : ℚ)⟩
  | 3 => ⟨(956411 / 1000000 : ℚ), (239103 / 250000 : ℚ)⟩
  | 4 => ⟨(163157 / 200000 : ℚ), (407893 / 500000 : ℚ)⟩
  | 5 => ⟨(932437 / 1000000 : ℚ), (466219 / 500000 : ℚ)⟩
  | 6 => ⟨(23957 / 25000 : ℚ), (958281 / 1000000 : ℚ)⟩
  | _ => ⟨1,1⟩
def ideal_0_lo : Box := ⟨(-12388720594107647 / 500000000000000000 : ℚ), (-24777441188215253 / 1000000000000000000 : ℚ)⟩
theorem ideal_0_lo_sound : ideal_0_lo.Holds (Real.log ((975527 / 1000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (975527 / 1000000 : ℚ) (-24473 / 1975527 : ℚ) 24 ideal_0_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_0_hi : Box := ⟨(-12388208050893847 / 500000000000000000 : ℚ), (-24776416101787653 / 1000000000000000000 : ℚ)⟩
theorem ideal_0_hi_sound : ideal_0_hi.Holds (Real.log ((121941 / 125000 : ℚ) : ℝ)) := by
  exact log_signed_bound (121941 / 125000 : ℚ) (-3059 / 246941 : ℚ) 24 ideal_0_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_0_enclosed :
    (idealEndpoints 0).Holds (factor idealMasks 0) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 0 (by decide))
    ideal_0_lo_sound ideal_0_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def ideal_1_lo : Box := ⟨(61926453486494967 / 250000000000000000 : ℚ), (247705813945979909 / 1000000000000000000 : ℚ)⟩
theorem ideal_1_lo_sound : ideal_1_lo.Holds (Real.log ((1281083 / 1000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (1281083 / 1000000 : ℚ) (281083 / 2281083 : ℚ) 24 ideal_1_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_1_hi : Box := ⟨(24770659453522327 / 100000000000000000 : ℚ), (247706594535223311 / 1000000000000000000 : ℚ)⟩
theorem ideal_1_hi_sound : ideal_1_hi.Holds (Real.log ((320271 / 250000 : ℚ) : ℝ)) := by
  exact log_signed_bound (320271 / 250000 : ℚ) (70271 / 570271 : ℚ) 24 ideal_1_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_1_enclosed :
    (idealEndpoints 1).Holds (factor idealMasks 1) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 1 (by decide))
    ideal_1_lo_sound ideal_1_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def ideal_2_lo : Box := ⟨(137806989220624857 / 1000000000000000000 : ℚ), (68903494610312449 / 500000000000000000 : ℚ)⟩
theorem ideal_2_lo_sound : ideal_2_lo.Holds (Real.log ((573877 / 500000 : ℚ) : ℝ)) := by
  exact log_signed_bound (573877 / 500000 : ℚ) (73877 / 1073877 : ℚ) 24 ideal_2_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_2_hi : Box := ⟨(68903930243542357 / 500000000000000000 : ℚ), (27561572097416951 / 200000000000000000 : ℚ)⟩
theorem ideal_2_hi_sound : ideal_2_hi.Holds (Real.log ((229551 / 200000 : ℚ) : ℝ)) := by
  exact log_signed_bound (229551 / 200000 : ℚ) (29551 / 429551 : ℚ) 24 ideal_2_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_2_enclosed :
    (idealEndpoints 2).Holds (factor idealMasks 2) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 2 (by decide))
    ideal_2_lo_sound ideal_2_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def ideal_3_lo : Box := ⟨(-44567542000286067 / 1000000000000000000 : ℚ), (-22283771000143013 / 500000000000000000 : ℚ)⟩
theorem ideal_3_lo_sound : ideal_3_lo.Holds (Real.log ((956411 / 1000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (956411 / 1000000 : ℚ) (-43589 / 1956411 : ℚ) 24 ideal_3_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_3_hi : Box := ⟨(-5570812053154761 / 125000000000000000 : ℚ), (-44566496425238047 / 1000000000000000000 : ℚ)⟩
theorem ideal_3_hi_sound : ideal_3_hi.Holds (Real.log ((239103 / 250000 : ℚ) : ℝ)) := by
  exact log_signed_bound (239103 / 250000 : ℚ) (-10897 / 489103 : ℚ) 24 ideal_3_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_3_enclosed :
    (idealEndpoints 3).Holds (factor idealMasks 3) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 3 (by decide))
    ideal_3_lo_sound ideal_3_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def ideal_4_lo : Box := ⟨(-203604439127243761 / 1000000000000000000 : ℚ), (-5090110978181093 / 25000000000000000 : ℚ)⟩
theorem ideal_4_lo_sound : ideal_4_lo.Holds (Real.log ((163157 / 200000 : ℚ) : ℝ)) := by
  exact log_signed_bound (163157 / 200000 : ℚ) (-36843 / 363157 : ℚ) 24 ideal_4_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_4_hi : Box := ⟨(-40720642662964251 / 200000000000000000 : ℚ), (-101801606657410607 / 500000000000000000 : ℚ)⟩
theorem ideal_4_hi_sound : ideal_4_hi.Holds (Real.log ((407893 / 500000 : ℚ) : ℝ)) := by
  exact log_signed_bound (407893 / 500000 : ℚ) (-92107 / 907893 : ℚ) 24 ideal_4_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_4_enclosed :
    (idealEndpoints 4).Holds (factor idealMasks 4) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 4 (by decide))
    ideal_4_lo_sound ideal_4_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def ideal_5_lo : Box := ⟨(-13990738013636723 / 200000000000000000 : ℚ), (-34976845034091787 / 500000000000000000 : ℚ)⟩
theorem ideal_5_lo_sound : ideal_5_lo.Holds (Real.log ((932437 / 1000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (932437 / 1000000 : ℚ) (-67563 / 1932437 : ℚ) 24 ideal_5_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_5_hi : Box := ⟨(-2798104704409763 / 40000000000000000 : ℚ), (-34976308805122017 / 500000000000000000 : ℚ)⟩
theorem ideal_5_hi_sound : ideal_5_hi.Holds (Real.log ((466219 / 500000 : ℚ) : ℝ)) := by
  exact log_signed_bound (466219 / 500000 : ℚ) (-33781 / 966219 : ℚ) 24 ideal_5_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_5_enclosed :
    (idealEndpoints 5).Holds (factor idealMasks 5) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 5 (by decide))
    ideal_5_lo_sound ideal_5_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def ideal_6_lo : Box := ⟨(-1065381703533717 / 25000000000000000 : ℚ), (-42615268141348639 / 1000000000000000000 : ℚ)⟩
theorem ideal_6_lo_sound : ideal_6_lo.Holds (Real.log ((23957 / 25000 : ℚ) : ℝ)) := by
  exact log_signed_bound (23957 / 25000 : ℚ) (-1043 / 48957 : ℚ) 24 ideal_6_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def ideal_6_hi : Box := ⟨(-42614224605557229 / 1000000000000000000 : ℚ), (-10653556151389297 / 250000000000000000 : ℚ)⟩
theorem ideal_6_hi_sound : ideal_6_hi.Holds (Real.log ((958281 / 1000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (958281 / 1000000 : ℚ) (-41719 / 1958281 : ℚ) 24 ideal_6_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem ideal_6_enclosed :
    (idealEndpoints 6).Holds (factor idealMasks 6) := by
  exact exp_enclosure (center_summary_sound idealMasks idealSummary ideal_summary_sound 6 (by decide))
    ideal_6_lo_sound ideal_6_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem ideal_enclosed (i : ℕ) (hi : i ∈ List.range 7) :
    (idealEndpoints i).Holds (factor idealMasks i) := by
  simp only [List.mem_range] at hi
  interval_cases i
  · exact ideal_0_enclosed
  · exact ideal_1_enclosed
  · exact ideal_2_enclosed
  · exact ideal_3_enclosed
  · exact ideal_4_enclosed
  · exact ideal_5_enclosed
  · exact ideal_6_enclosed
end TMM
