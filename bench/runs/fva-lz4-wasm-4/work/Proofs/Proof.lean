import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Turn an observed deterministic reference execution into semantic total correctness. -/
theorem checked_return {H : HostSem} {s : Store} {a : Nat} {args : List Val}
    {P : Store → List Val → Prop} {n : Nat}
    (h : (match runDet n (invokeConfig s a args) with
      | none => False
      | some c => ∃ vs, c.instrs = vals vs ∧ P c.store vs)) :
    Must H (fun | .returned s vs => P s vs | .trapped _ => False)
      (invokeConfig s a args) := by
  cases hr : runDet n (invokeConfig s a args) with
  | none => simp [hr] at h
  | some c =>
    rw [hr] at h
    obtain ⟨vs, hv, hp⟩ := h
    apply must_returned_of_runDet (s' := c.store) (f' := c.frame) (vs := vs) (n := n) ?_ hp
    exact hr.trans (congrArg some (by cases c; simp_all))

def valuesAre : List AInstr → List Val → Bool
  | [], [] => true
  | e :: es, v :: vs => toVal e == some v && valuesAre es vs
  | _, _ => false

theorem valuesAre_sound {es : List AInstr} {vs : List Val}
    (h : valuesAre es vs = true) : es = vals vs := by
  induction es generalizing vs with
  | nil => cases vs <;> simp_all [valuesAre, vals]
  | cons e es ih =>
    cases vs with
    | nil => simp [valuesAre] at h
    | cons v vs =>
      simp only [valuesAre, Bool.and_eq_true, beq_iff_eq] at h
      rw [eq_instr_of_toVal h.1, ih h.2]
      rfl

-- Compare only the observable result and bytes, never function-valued memory equality.
def observation (r : Option Config) (vs : List Val) (p : Nat) (bs : List UInt8) : Bool :=
  match r with
  | none => false
  | some c => valuesAre c.instrs vs && bytesAt c.store p bs.length == bs

theorem observed_return {H : HostSem} {s : Store} {a n p : Nat} {args vs : List Val}
    {bs : List UInt8}
    (h : observation (runDet n (invokeConfig s a args)) vs p bs = true) :
    Must H (fun | .returned s ws => ws = vs ∧ bytesAt s p bs.length = bs
                | .trapped _ => False) (invokeConfig s a args) := by
  apply checked_return (n := n)
  cases hr : runDet n (invokeConfig s a args) with
  | none => simp [hr, observation] at h
  | some c =>
    simp only [hr, observation, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨vs, valuesAre_sound h.1, rfl, h.2⟩

private theorem encoder_observed :
    observation (runDet 2000 (invokeConfig encoderStore 2
      [.i32 262144, .i32 13, .i32 262208])) [.i32 13] 262208 badBlock = true := by
  kernel_rfl

private theorem decoder_observed :
    observation (runDet 500 (invokeConfig (allocation.1.withBytes 100 validBlock) 3
      [.i32 100, .i32 10, .i32 0])) [.i32 1] 0 (97 :: List.replicate 16 0) = true := by
  kernel_rfl

private theorem empty_zero_observed :
    observation (runDet 500 (invokeConfig (allocation.1.withBytes 0 [0,0,0]) 3
      [.i32 0, .i32 1, .i32 1024])) [.i32 0] 0 [] = true := by
  kernel_rfl

private theorem empty_one_observed :
    observation (runDet 500 (invokeConfig (allocation.1.withBytes 0 [0,1,0]) 3
      [.i32 0, .i32 1, .i32 1024])) [.i32 4] 0 [] = true := by
  kernel_rfl

-- Export address and argument types are checked separately from the execution.
theorem r1_counterexample_holds : r1_counterexample := by
  intro H
  refine ⟨2, rfl, ?_, ?_⟩
  · exact ⟨_, rfl, by change List.Forall₂ _ _ [ValType.num .i32, ValType.num .i32, ValType.num .i32]; exact .cons trivial (.cons trivial (.cons trivial .nil))⟩
  · exact observed_return encoder_observed

theorem r2_counterexample_holds : r2_counterexample := by
  intro H
  refine ⟨3, rfl, ?_, ?_⟩
  · exact ⟨_, rfl, by change List.Forall₂ _ _ [ValType.num .i32, ValType.num .i32, ValType.num .i32]; exact .cons trivial (.cons trivial (.cons trivial .nil))⟩
  · exact observed_return decoder_observed

theorem r3_counterexample_holds : r3_counterexample := by
  intro H
  constructor
  · refine ⟨3, rfl, ⟨_, rfl, by change List.Forall₂ _ _ [ValType.num .i32, ValType.num .i32, ValType.num .i32]; exact .cons trivial (.cons trivial (.cons trivial .nil))⟩, ?_⟩
    exact (observed_return empty_zero_observed).mono (by intro o h; cases o <;> simp_all)
  · refine ⟨3, rfl, ⟨_, rfl, by change List.Forall₂ _ _ [ValType.num .i32, ValType.num .i32, ValType.num .i32]; exact .cons trivial (.cons trivial (.cons trivial .nil))⟩, ?_⟩
    exact (observed_return empty_one_observed).mono (by intro o h; cases o <;> simp_all)

theorem empty_boundary_traps_holds : empty_boundary_traps := by
  intro H
  refine ⟨3, rfl, ⟨_, rfl, by change List.Forall₂ _ _ [ValType.num .i32, ValType.num .i32, ValType.num .i32]; exact .cons trivial (.cons trivial (.cons trivial .nil))⟩, ?_⟩
  have h : (runDet 500 (invokeConfig (allocation.1.withBytes 65535 [0]) 3
    [.i32 65535, .i32 1, .i32 0])).map (fun c => c.instrs) = some [.trap] := by
    kernel_rfl
  cases hr : runDet 500 (invokeConfig (allocation.1.withBytes 65535 [0]) 3
    [.i32 65535, .i32 1, .i32 0]) with
  | none => rw [hr] at h; cases h
  | some c =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    apply runDet_must hr
    intro o hf
    cases o with
    | returned s vs => exact False.elim (vals_ne_trap vs (hf.2.symm.trans h))
    | trapped s => trivial

theorem initialization_holds : initialization := by
  refine ⟨?_, ?_, ?_⟩
  · intro H
    obtain ⟨s, inst, hi⟩ := instantiable_alloc (m := Lifted.module) rfl rfl rfl rfl rfl H
    have he := instance_alloc rfl rfl rfl rfl hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact hi
  · rfl
  · rfl
end Proofs
