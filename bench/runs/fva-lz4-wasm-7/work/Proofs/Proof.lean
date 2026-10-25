import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem r1_run :
    ((runDet 3000 (invokeConfig encoderStore 2 [.i32 262144, .i32 13, .i32 300000])).map
      (fun c => (c.instrs, memoryBytes c.store 300000 13))) =
      some (vals [.i32 13], encoded) := by
  kernel_rfl

private theorem r2_run :
    ((runDet 1000 (invokeConfig decoderStore 3 [.i32 100, .i32 10, .i32 32])).map
      (fun c => (c.instrs, memoryBytes c.store 32 13))) =
      some (vals [.i32 1], [65,0,0,0,0,0,0,0,0,0,0,0,0]) := by
  kernel_rfl

private theorem r3_run :
    ((runDet 100 (invokeConfig allocation.1 3 [.i32 65535, .i32 1, .i32 32])).map
      (fun c => c.instrs)) = some [.trap] := by
  kernel_rfl

private theorem returns_of_check {H : HostSem} {n p len : Nat} {c : Config}
    {vs : List Val} {bs : List UInt8}
    (h : (runDet n c).map (fun c => (c.instrs, memoryBytes c.store p len)) =
      some (vals vs, bs)) :
    Must H (fun | .returned s ws => ws = vs ∧ memoryBytes s p len = bs
                | .trapped _ => False) c := by
  cases hr : runDet n c with
  | none => simp [hr] at h
  | some c' =>
    simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    apply runDet_must hr
    intro o ho
    cases o with
    | returned s ws =>
      have hv : ws = vs := vals_inj.mp (ho.2.symm.trans h.1)
      exact ⟨hv, ho.1 ▸ h.2⟩
    | trapped s => exact (vals_ne_trap vs) (h.1.symm.trans ho.2)

theorem r1_counterexample_holds : r1_counterexample := by
  intro H
  refine ⟨2, rfl, ⟨_, rfl, ?_⟩, returns_of_check r1_run⟩
  repeat' constructor

theorem r2_counterexample_holds : r2_counterexample := by
  intro H
  refine ⟨3, rfl, ⟨_, rfl, ?_⟩, returns_of_check r2_run⟩
  repeat' constructor

theorem r3_counterexample_holds : r3_counterexample := by
  intro H
  refine ⟨3, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · repeat' constructor
  · cases hr : runDet 100 (invokeConfig allocation.1 3 [.i32 65535, .i32 1, .i32 32]) with
    | none => have h := r3_run; simp only [hr, Option.map_none, reduceCtorEq] at h
    | some c =>
      have hi : c.instrs = [.trap] := by
        simpa only [hr, Option.map_some, Option.some.injEq] using r3_run
      apply runDet_must hr
      intro o ho
      cases o with
      | returned s vs => exact False.elim ((vals_ne_trap vs) (ho.2.symm.trans hi))
      | trapped s => trivial

end Proofs
