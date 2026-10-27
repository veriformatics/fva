-- Generated numerical witnesses; interval inclusions and logarithms checked in Lean.
import Proofs.Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TMM
def edgeSummary (i : ℕ) : Box :=
  match i with
  | 0 => ⟨(38484367159369 / 1000000000000000 : ℚ), (3848436715937 / 100000000000000 : ℚ)⟩
  | 1 => ⟨(29227292025373 / 100000000000000 : ℚ), (292272920253731 / 1000000000000000 : ℚ)⟩
  | 2 => ⟨(165582148247453 / 1000000000000000 : ℚ), (82791074123727 / 500000000000000 : ℚ)⟩
  | 3 => ⟨(-1 / 1000000000000000 : ℚ), (1 / 1000000000000000 : ℚ)⟩
  | 4 => ⟨(-159036908025723 / 1000000000000000 : ℚ), (-79518454012861 / 500000000000000 : ℚ)⟩
  | 5 => ⟨(-25386130001683 / 1000000000000000 : ℚ), (-12693065000841 / 500000000000000 : ℚ)⟩
  | 6 => ⟨(5190862369503 / 250000000000000 : ℚ), (20763449478013 / 1000000000000000 : ℚ)⟩
  | _ => ⟨0,0⟩
theorem edge_valid : ∀ i ∈ List.range 7, validPairs (pairsOfMask edgeMasks i) i := by
  decide +kernel
theorem edge_summary_contains : ∀ i ∈ List.range 7,
    (edgeSummary i).lo ≤ (rawBox (pairsOfMask edgeMasks i) i).lo ∧
    (rawBox (pairsOfMask edgeMasks i) i).hi ≤ (edgeSummary i).hi := by
  decide +kernel
theorem edge_summary_sound (i : ℕ) (hi : i ∈ List.range 7) :
    (edgeSummary i).Holds (raw (pairsOfMask edgeMasks i) i) := by
  exact widen_sound (rawBox_sound _ _ (edge_valid i hi))
    (edge_summary_contains i hi).1 (edge_summary_contains i hi).2
def edgeEndpoints (i : ℕ) : Box :=
  match i with
  | 0 => ⟨(99099942459193067 / 100000000000000000 : ℚ), (99099942459393067 / 100000000000000000 : ℚ)⟩
  | 1 => ⟨(1596623008597781 / 1250000000000000 : ℚ), (1596623008600281 / 1250000000000000 : ℚ)⟩
  | 2 => ⟨(450123055887791 / 400000000000000 : ℚ), (450123055888591 / 400000000000000 : ℚ)⟩
  | 3 => ⟨(95358597286225431 / 100000000000000000 : ℚ), (95358597286425431 / 100000000000000000 : ℚ)⟩
  | 4 => ⟨(40668767109167191 / 50000000000000000 : ℚ), (40668767109267191 / 50000000000000000 : ℚ)⟩
  | 5 => ⟨(92968280356611641 / 100000000000000000 : ℚ), (92968280356811641 / 100000000000000000 : ℚ)⟩
  | 6 => ⟨(97359269251816547 / 100000000000000000 : ℚ), (97359269252016547 / 100000000000000000 : ℚ)⟩
  | _ => ⟨1,1⟩
def edge_0_lo : Box := ⟨(-452066264304547 / 50000000000000000 : ℚ), (-9041325286090899 / 1000000000000000000 : ℚ)⟩
theorem edge_0_lo_sound : edge_0_lo.Holds (Real.log ((99099942459193067 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (99099942459193067 / 100000000000000000 : ℚ) (-900057540806933 / 199099942459193067 : ℚ) 24 edge_0_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_0_hi : Box := ⟨(-1130165660509097 / 125000000000000000 : ℚ), (-1808265056814547 / 200000000000000000 : ℚ)⟩
theorem edge_0_hi_sound : edge_0_hi.Holds (Real.log ((99099942459393067 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (99099942459393067 / 100000000000000000 : ℚ) (-900057540606933 / 199099942459393067 : ℚ) 24 edge_0_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_0_enclosed :
    (edgeEndpoints 0).Holds (factor edgeMasks 0) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 0 (by decide))
    edge_0_lo_sound edge_0_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def edge_1_lo : Box := ⟨(122373613904247981 / 500000000000000000 : ℚ), (244747227808496003 / 1000000000000000000 : ℚ)⟩
theorem edge_1_lo_sound : edge_1_lo.Holds (Real.log ((1596623008597781 / 1250000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (1596623008597781 / 1250000000000000 : ℚ) (346623008597781 / 2846623008597781 : ℚ) 24 edge_1_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_1_hi : Box := ⟨(244747227810061767 / 1000000000000000000 : ℚ), (15296701738128863 / 62500000000000000 : ℚ)⟩
theorem edge_1_hi_sound : edge_1_hi.Holds (Real.log ((1596623008600281 / 1250000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (1596623008600281 / 1250000000000000 : ℚ) (346623008600281 / 2846623008600281 : ℚ) 24 edge_1_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_1_enclosed :
    (edgeEndpoints 1).Holds (factor edgeMasks 1) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 1 (by decide))
    edge_1_lo_sound edge_1_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def edge_2_lo : Box := ⟨(2361129116042257 / 20000000000000000 : ℚ), (118056455802112891 / 1000000000000000000 : ℚ)⟩
theorem edge_2_lo_sound : edge_2_lo.Holds (Real.log ((450123055887791 / 400000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (450123055887791 / 400000000000000 : ℚ) (50123055887791 / 850123055887791 : ℚ) 24 edge_2_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_2_hi : Box := ⟨(59028227901945071 / 500000000000000000 : ℚ), (118056455803890183 / 1000000000000000000 : ℚ)⟩
theorem edge_2_hi_sound : edge_2_hi.Holds (Real.log ((450123055888591 / 400000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (450123055888591 / 400000000000000 : ℚ) (50123055888591 / 850123055888591 : ℚ) 24 edge_2_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_2_enclosed :
    (edgeEndpoints 2).Holds (factor edgeMasks 2) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 2 (by decide))
    edge_2_lo_sound edge_2_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def edge_3_lo : Box := ⟨(-23762846222750061 / 500000000000000000 : ℚ), (-47525692445500081 / 1000000000000000000 : ℚ)⟩
theorem edge_3_lo_sound : edge_3_lo.Holds (Real.log ((95358597286225431 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (95358597286225431 / 100000000000000000 : ℚ) (-4641402713774569 / 195358597286225431 : ℚ) 24 edge_3_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_3_hi : Box := ⟨(-5940711555425347 / 125000000000000000 : ℚ), (-9505138488680547 / 200000000000000000 : ℚ)⟩
theorem edge_3_hi_sound : edge_3_hi.Holds (Real.log ((95358597286425431 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (95358597286425431 / 100000000000000000 : ℚ) (-4641402713574569 / 195358597286425431 : ℚ) 24 edge_3_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_3_enclosed :
    (edgeEndpoints 3).Holds (factor edgeMasks 3) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 3 (by decide))
    edge_3_lo_sound edge_3_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def edge_4_lo : Box := ⟨(-25820325058925431 / 125000000000000000 : ℚ), (-206562600471403407 / 1000000000000000000 : ℚ)⟩
theorem edge_4_lo_sound : edge_4_lo.Holds (Real.log ((40668767109167191 / 50000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (40668767109167191 / 50000000000000000 : ℚ) (-9331232890832809 / 90668767109167191 : ℚ) 24 edge_4_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_4_hi : Box := ⟨(-103281300234472279 / 500000000000000000 : ℚ), (-206562600468944517 / 1000000000000000000 : ℚ)⟩
theorem edge_4_hi_sound : edge_4_hi.Holds (Real.log ((40668767109267191 / 50000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (40668767109267191 / 50000000000000000 : ℚ) (-9331232890732809 / 90668767109267191 : ℚ) 24 edge_4_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_4_enclosed :
    (edgeEndpoints 4).Holds (factor edgeMasks 4) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 4 (by decide))
    edge_4_lo_sound edge_4_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def edge_5_lo : Box := ⟨(-72911822447209489 / 1000000000000000000 : ℚ), (-9113977805901181 / 125000000000000000 : ℚ)⟩
theorem edge_5_lo_sound : edge_5_lo.Holds (Real.log ((92968280356611641 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (92968280356611641 / 100000000000000000 : ℚ) (-7031719643388359 / 192968280356611641 : ℚ) 24 edge_5_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_5_hi : Box := ⟨(-36455911222529109 / 500000000000000000 : ℚ), (-72911822445058177 / 1000000000000000000 : ℚ)⟩
theorem edge_5_hi_sound : edge_5_hi.Holds (Real.log ((92968280356811641 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (92968280356811641 / 100000000000000000 : ℚ) (-7031719643188359 / 192968280356811641 : ℚ) 24 edge_5_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_5_enclosed :
    (edgeEndpoints 5).Holds (factor edgeMasks 5) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 5 (by decide))
    edge_5_lo_sound edge_5_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def edge_6_lo : Box := ⟨(-26762242967466221 / 1000000000000000000 : ℚ), (-1338112148373309 / 50000000000000000 : ℚ)⟩
theorem edge_6_lo_sound : edge_6_lo.Holds (Real.log ((97359269251816547 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (97359269251816547 / 100000000000000000 : ℚ) (-2640730748183453 / 197359269251816547 : ℚ) 24 edge_6_lo
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def edge_6_hi : Box := ⟨(-13381121482705987 / 500000000000000000 : ℚ), (-26762242965411933 / 1000000000000000000 : ℚ)⟩
theorem edge_6_hi_sound : edge_6_hi.Holds (Real.log ((97359269252016547 / 100000000000000000 : ℚ) : ℝ)) := by
  exact log_signed_bound (97359269252016547 / 100000000000000000 : ℚ) (-2640730747983453 / 197359269252016547 : ℚ) 24 edge_6_hi
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem edge_6_enclosed :
    (edgeEndpoints 6).Holds (factor edgeMasks 6) := by
  exact exp_enclosure (center_summary_sound edgeMasks edgeSummary edge_summary_sound 6 (by decide))
    edge_6_lo_sound edge_6_hi_sound (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem edge_enclosed (i : ℕ) (hi : i ∈ List.range 7) :
    (edgeEndpoints i).Holds (factor edgeMasks i) := by
  simp only [List.mem_range] at hi
  interval_cases i
  · exact edge_0_enclosed
  · exact edge_1_enclosed
  · exact edge_2_enclosed
  · exact edge_3_enclosed
  · exact edge_4_enclosed
  · exact edge_5_enclosed
  · exact edge_6_enclosed
end TMM
