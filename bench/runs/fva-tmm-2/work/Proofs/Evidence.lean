import Proofs.LogChecks
import Proofs.Calc.Selection

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem raw_self (m : Matrix) (r : Nat) : rawLog m r r = 0 := by
  have heq : ∀ p ∈ kept m r r, p.1 = p.2 := by
    intro p hp
    have hp1 : p ∈ pairs m r r := (List.mem_filter.mp hp).1
    have hp2 := (List.mem_filter.mp hp1).1
    obtain ⟨row, _, hrow⟩ := List.mem_map.mp hp2
    cases hrow
    rfl
  unfold rawLog
  dsimp only
  have hz : ((kept m r r).map (fun p => (weight (lib m r) (lib m r) p : ℝ) *
      logRatio (lib m r) (lib m r) p)).sum = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    simp [logRatio, heq p hp]
  rw [hz]
  simp

def rb (j : Nat) : I := Data.rawBounds[j]?.getD I.zero

theorem raw_0 : (rb 0).Holds (rawLog Data.counts 0 3) := by
  have hn : ∀ p ∈ Data.kept0, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel
  have hp : ∀ p ∈ Data.kept0, (Data.logI p.1).Holds (Real.log p.1) ∧
      (Data.logI p.2).Holds (Real.log p.2) := by
    intro p h
    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩
  have hw : ∀ p ∈ Data.kept0, 0 ≤ weight 1261 1097 p := by decide +kernel
  have h := raw_sound Data.logI 1261 1097 Data.kept0 log_1261 log_1097 hp hw
  unfold rawLog
  rw [kept_0, lib_0, lib_3]
  exact holds_weaken h (by decide +kernel) (by decide +kernel)

theorem raw_1 : (rb 1).Holds (rawLog Data.counts 1 3) := by
  have hn : ∀ p ∈ Data.kept1, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel
  have hp : ∀ p ∈ Data.kept1, (Data.logI p.1).Holds (Real.log p.1) ∧
      (Data.logI p.2).Holds (Real.log p.2) := by
    intro p h
    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩
  have hw : ∀ p ∈ Data.kept1, 0 ≤ weight 621 1097 p := by decide +kernel
  have h := raw_sound Data.logI 621 1097 Data.kept1 log_621 log_1097 hp hw
  unfold rawLog
  rw [kept_1, lib_1, lib_3]
  exact holds_weaken h (by decide +kernel) (by decide +kernel)

theorem raw_2 : (rb 2).Holds (rawLog Data.counts 2 3) := by
  have hn : ∀ p ∈ Data.kept2, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel
  have hp : ∀ p ∈ Data.kept2, (Data.logI p.1).Holds (Real.log p.1) ∧
      (Data.logI p.2).Holds (Real.log p.2) := by
    intro p h
    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩
  have hw : ∀ p ∈ Data.kept2, 0 ≤ weight 755 1097 p := by decide +kernel
  have h := raw_sound Data.logI 755 1097 Data.kept2 log_755 log_1097 hp hw
  unfold rawLog
  rw [kept_2, lib_2, lib_3]
  exact holds_weaken h (by decide +kernel) (by decide +kernel)

theorem raw_3 : (rb 3).Holds (rawLog Data.counts 3 3) := by
  rw [raw_self]
  norm_num [rb, Data.rawBounds, I.Holds]

theorem raw_4 : (rb 4).Holds (rawLog Data.counts 4 3) := by
  have hn : ∀ p ∈ Data.kept4, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel
  have hp : ∀ p ∈ Data.kept4, (Data.logI p.1).Holds (Real.log p.1) ∧
      (Data.logI p.2).Holds (Real.log p.2) := by
    intro p h
    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩
  have hw : ∀ p ∈ Data.kept4, 0 ≤ weight 1916 1097 p := by decide +kernel
  have h := raw_sound Data.logI 1916 1097 Data.kept4 log_1916 log_1097 hp hw
  unfold rawLog
  rw [kept_4, lib_4, lib_3]
  exact holds_weaken h (by decide +kernel) (by decide +kernel)

theorem raw_5 : (rb 5).Holds (rawLog Data.counts 5 3) := by
  have hn : ∀ p ∈ Data.kept5, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel
  have hp : ∀ p ∈ Data.kept5, (Data.logI p.1).Holds (Real.log p.1) ∧
      (Data.logI p.2).Holds (Real.log p.2) := by
    intro p h
    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩
  have hw : ∀ p ∈ Data.kept5, 0 ≤ weight 1136 1097 p := by decide +kernel
  have h := raw_sound Data.logI 1136 1097 Data.kept5 log_1136 log_1097 hp hw
  unfold rawLog
  rw [kept_5, lib_5, lib_3]
  exact holds_weaken h (by decide +kernel) (by decide +kernel)

theorem raw_6 : (rb 6).Holds (rawLog Data.counts 6 3) := by
  have hn : ∀ p ∈ Data.kept6, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel
  have hp : ∀ p ∈ Data.kept6, (Data.logI p.1).Holds (Real.log p.1) ∧
      (Data.logI p.2).Holds (Real.log p.2) := by
    intro p h
    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩
  have hw : ∀ p ∈ Data.kept6, 0 ≤ weight 1219 1097 p := by decide +kernel
  have h := raw_sound Data.logI 1219 1097 Data.kept6 log_1219 log_1097 hp hw
  unfold rawLog
  rw [kept_6, lib_6, lib_3]
  exact holds_weaken h (by decide +kernel) (by decide +kernel)

theorem raw_valid (j : Nat) (hj : j ∈ List.range 7) :
    (rb j).Holds (rawLog Data.counts j 3) := by
  have hj7 : j < 7 := List.mem_range.mp hj
  interval_cases j
  · exact raw_0
  · exact raw_1
  · exact raw_2
  · exact raw_3
  · exact raw_4
  · exact raw_5
  · exact raw_6

def centerI (j : Nat) : I :=
  (rb j).sub ((isum ((List.range 7).map rb)).div 7)

theorem center_sound (j : Nat) (hj : j ∈ List.range 7) :
    (centerI j).Holds (rawLog Data.counts j 3 -
      ((List.range 7).map (fun k => rawLog Data.counts k 3)).sum / 7) := by
  exact holds_sub (raw_valid j hj)
    (holds_div (by norm_num) (holds_sum (List.range 7) rb
      (fun k => rawLog Data.counts k 3) raw_valid))

theorem factor_0 : (975526 / 1000000 : ℚ) ≤ factor Data.counts 0 ∧
    factor Data.counts 0 ≤ (975529 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 975526 1000000 (by decide) (by decide) log_975526 log_1000000
  have hh := log_quotient 975529 1000000 (by decide) (by decide) log_975529 log_1000000
  exact exp_enclose (center_sound 0 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem factor_1 : (1281082 / 1000000 : ℚ) ≤ factor Data.counts 1 ∧
    factor Data.counts 1 ≤ (1281085 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 1281082 1000000 (by decide) (by decide) log_1281082 log_1000000
  have hh := log_quotient 1281085 1000000 (by decide) (by decide) log_1281085 log_1000000
  exact exp_enclose (center_sound 1 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem factor_2 : (1147753 / 1000000 : ℚ) ≤ factor Data.counts 2 ∧
    factor Data.counts 2 ≤ (1147756 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 1147753 1000000 (by decide) (by decide) log_1147753 log_1000000
  have hh := log_quotient 1147756 1000000 (by decide) (by decide) log_1147756 log_1000000
  exact exp_enclose (center_sound 2 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem factor_3 : (956410 / 1000000 : ℚ) ≤ factor Data.counts 3 ∧
    factor Data.counts 3 ≤ (956413 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 956410 1000000 (by decide) (by decide) log_956410 log_1000000
  have hh := log_quotient 956413 1000000 (by decide) (by decide) log_956413 log_1000000
  exact exp_enclose (center_sound 3 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem factor_4 : (815784 / 1000000 : ℚ) ≤ factor Data.counts 4 ∧
    factor Data.counts 4 ≤ (815787 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 815784 1000000 (by decide) (by decide) log_815784 log_1000000
  have hh := log_quotient 815787 1000000 (by decide) (by decide) log_815787 log_1000000
  exact exp_enclose (center_sound 4 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem factor_5 : (932436 / 1000000 : ℚ) ≤ factor Data.counts 5 ∧
    factor Data.counts 5 ≤ (932439 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 932436 1000000 (by decide) (by decide) log_932436 log_1000000
  have hh := log_quotient 932439 1000000 (by decide) (by decide) log_932439 log_1000000
  exact exp_enclose (center_sound 5 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem factor_6 : (958279 / 1000000 : ℚ) ≤ factor Data.counts 6 ∧
    factor Data.counts 6 ≤ (958282 / 1000000 : ℚ) := by
  unfold factor
  rw [reference_eq]
  have hl := log_quotient 958279 1000000 (by decide) (by decide) log_958279 log_1000000
  have hh := log_quotient 958282 1000000 (by decide) (by decide) log_958282 log_1000000
  exact exp_enclose (center_sound 6 (by decide)) hl hh
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem edge_errors (j : Fin 7) :
    |((Data.edge[j.val]?.getD ⟨0, []⟩).value : ℝ) - factor Data.counts j| ≤
      (23 / 1000 : ℚ) := by
  fin_cases j
  · exact abs_error factor_0 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_1 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_2 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_3 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_4 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_5 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_6 (by decide +kernel) (by decide +kernel)

theorem rna_errors (j : Fin 7) :
    |((Data.rna[j.val]?.getD ⟨0, []⟩).value : ℝ) - factor Data.counts j| ≤
      (21 / 1000 : ℚ) := by
  fin_cases j
  · exact abs_error factor_0 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_1 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_2 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_3 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_4 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_5 (by decide +kernel) (by decide +kernel)
  · exact abs_error factor_6 (by decide +kernel) (by decide +kernel)

end Proofs
