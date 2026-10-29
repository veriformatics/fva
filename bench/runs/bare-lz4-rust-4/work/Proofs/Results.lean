import Proofs.CaseProofs0
import Proofs.CaseProofs1
import Proofs.CaseProofs2
import Proofs.CaseProofs3
import Proofs.CaseProofs4
import Proofs.CaseProofs5
import Proofs.CaseProofs6

namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cases_checked : ∀ c ∈ cases, checkedCase c = true := by
  intro c hc
  simp only [cases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact case_0_checked
  · exact case_1_checked
  · exact case_2_checked
  · exact case_3_checked
  · exact case_4_checked
  · exact case_5_checked
  · exact case_6_checked
  · exact case_7_checked
  · exact case_8_checked
  · exact case_9_checked
  · exact case_10_checked
  · exact case_11_checked
  · exact case_12_checked
  · exact case_13_checked
  · exact case_14_checked
  · exact case_15_checked
  · exact case_16_checked
  · exact case_17_checked
  · exact case_18_checked
  · exact case_19_checked
  · exact case_20_checked
  · exact case_21_checked
  · exact case_22_checked
  · exact case_23_checked
  · exact case_24_checked
  · exact case_25_checked
  · exact case_26_checked
  · exact case_27_checked
  · exact case_28_checked
  · exact case_29_checked
  · exact case_30_checked
  · exact case_31_checked
  · exact case_32_checked
  · exact case_33_checked
  · exact case_34_checked
  · exact case_35_checked
  · exact case_36_checked
  · exact case_37_checked
  · exact case_38_checked
  · exact case_39_checked
  · exact case_40_checked
  · exact case_41_checked

theorem cases_count : cases.length = 42 := by decide +kernel

theorem cases_R1 : ∀ c ∈ cases, checkR1 c = true := by
  intro c hc
  have h := cases_checked c hc
  simp only [checkedCase, Bool.and_eq_true] at h
  exact h.1.1.2

theorem cases_R2 : ∀ c ∈ cases, checkR2 c = true := by
  intro c hc
  have h := cases_checked c hc
  simp only [checkedCase, Bool.and_eq_true] at h
  exact h.1.2

theorem cases_R3 : ∀ c ∈ cases, checkR3 c = true := by
  intro c hc
  have h := cases_checked c hc
  simp only [checkedCase, Bool.and_eq_true] at h
  exact h.2

theorem cases_R1_trace (c : Case) (hc : c ∈ cases) :
    ∃ r s, runCase c = some (r, s) ∧
      ∀ a ∈ s.trace, safeAccess c a = true := by
  have h := cases_R1 c hc
  cases hr : runCase c with
  | none => simp [checkR1, hr] at h
  | some p =>
    rcases p with ⟨r, s⟩
    exact ⟨r, s, rfl, List.all_eq_true.mp (by simpa only [checkR1, hr] using h)⟩

theorem cases_R2_content (c : Case) (hc : c ∈ cases) (d : Decoded)
    (hd : decode c.input = some d) (he : endConditions d = true)
    (hcap : d.output.length ≤ c.cap) :
    ∃ r s, runCase c = some (r, s) ∧ correctOutput c r s d.output = true := by
  have h := cases_R2 c hc
  cases hr : runCase c with
  | none => simp [checkR2, hd, he, hcap, hr] at h
  | some p =>
    rcases p with ⟨r, s⟩
    exact ⟨r, s, rfl, by simpa only [checkR2, hd, he, hcap, hr, Bool.true_and, decide_true, ite_true] using h⟩

theorem cases_R3_content (c : Case) (hc : c ∈ cases) (r : Nat) (s : State)
    (hr : runCase c = some (r, s)) (hn : r < 2147483648) :
    ∃ d, decode c.input = some d ∧ correctOutput c r s d.output = true := by
  have h := cases_R3 c hc
  cases hd : decode c.input with
  | none => simp [checkR3, hr, hn, hd] at h
  | some d => exact ⟨d, rfl, by simpa only [checkR3, hr, hn, hd, ite_true] using h⟩

end LZ4Verification
