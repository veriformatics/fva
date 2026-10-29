import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem badInput_decoded : ofBits f64fmt badInput = .normal false 4503599627370495 (-2) := by
  decide +kernel

theorem badValue_exact : badValue = (9007199254740991 : ℝ) / 18014398509481984 := by
  unfold badValue
  rw [badInput_decoded]
  norm_num [FVal.toReal, f64fmt, zpow_neg]

theorem badInput_returns : Returns Lifted.module "iround" [.f64 badInput] [.i32 1] := by
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
  refine ⟨0, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · change List.Forall₂ _ [Val.f64 badInput] [ValType.num .f64]
    exact .cons trivial .nil
  refine must_returned_of_runDet (n := 20)
    (s' := (allocModule {} Lifted.module [] [] []).1)
    (f' := ⟨[], {}⟩) (vs := [.i32 1]) ?_ rfl
  rfl

theorem r1_counterexample_holds : r1_counterexample := by
  refine ⟨?_, badValue_exact, ?_, ?_, badInput_returns⟩
  · rw [badInput_decoded]; trivial
  · rw [badValue_exact]; norm_num
  · intro n hn
    rw [badValue_exact]
    have hn' : n ≤ -1 ∨ 1 ≤ n := by omega
    rcases hn' with h | h
    · have hc : (n : ℝ) ≤ -1 := by exact_mod_cast h
      rw [abs_of_pos (by norm_num), abs_of_pos (by linarith)]
      linarith
    · have hc : (1 : ℝ) ≤ n := by exact_mod_cast h
      rw [abs_of_pos (by norm_num), abs_of_neg (by linarith)]
      linarith

end Proofs
