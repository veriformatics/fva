import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem call_of_run (c L : BitVec 64) (out : Nat)
    (hrun : (runDet 1000 (invokeConfig (inputStore c L) 160
      [.i32 32768, .i32 32800, .i32 32840, .i32 1])).map
      (fun c => (c.instrs.isEmpty, c.store.mems[0]?.map (fun m => m.read 32840 8))) =
      some (true, some out)) :
    CallReturns (fun _ _ _ _ => False) (inputStore c L) linked.2 "calc_cpm_raw"
      [.i32 32768, .i32 32800, .i32 32840, .i32 1]
      (fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧ mem.read 32840 8 = out) := by
  refine ⟨160, ?_, ?_, ?_⟩
  · kernel_rfl
  · refine ⟨.wasm (Lifted.module.types[17]?.getD ⟨[], []⟩) linked.2 Lifted.func86, ?_, ?_⟩
    · rfl
    · simp [Val.HasType, FuncInst.type, Lifted.module]
  · generalize hr : runDet 1000 (invokeConfig (inputStore c L) 160
      [.i32 32768, .i32 32800, .i32 32840, .i32 1]) = result at hrun
    cases result with
    | none => simp at hrun
    | some final =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrun
      have he : final.instrs = [] := List.isEmpty_iff.mp hrun.1
      apply must_returned_of_runDet (n := 1000) (s' := final.store) (f' := final.frame) (vs := [])
      · convert hr using 1
        cases final
        simp_all
      · refine ⟨rfl, ?_⟩
        cases hm : final.store.mems[0]? with
        | none => simp [hm] at hrun
        | some mem => exact ⟨mem, rfl, Option.some.inj (by simpa [hm] using hrun.2)⟩

theorem r1_counterexample_holds : r1_counterexample := by
  refine ⟨call_of_run huge huge 0x7ff0000000000000 (by decide +kernel), ?_⟩
  have hb : ofBits f64fmt huge = .normal false 0 1023 := by decide +kernel
  have hp : 0 < (ofBits f64fmt huge).toReal f64fmt := by
    rw [hb]
    simp only [FVal.toReal]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero, one_mul]
    exact zpow_pos (by norm_num) _
  refine ⟨by rw [hb]; trivial, hp, ?_⟩
  rw [div_self (ne_of_gt hp), one_mul]

theorem r2_total_witness_holds : r2_total_witness := by
  refine ⟨call_of_run _ _ _ (by decide +kernel), ?_⟩
  decide +kernel

theorem r2_rounding_witness_holds : r2_rounding_witness := by
  refine ⟨call_of_run _ _ _ (by decide +kernel), ?_, by decide +kernel⟩
  apply must_returned_of_runDet (n := 20) (s' := {}) (f' := ⟨[], {}⟩) (vs := [.i32 0])
  · kernel_rfl
  · rfl

end Proofs
