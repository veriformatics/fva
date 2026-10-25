import Proofs.Spec
import FVA.Proof.Lib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

private def codecType : FuncType :=
  ⟨[.num .i32, .num .i32, .num .i32], [.num .i32]⟩

noncomputable def encodeStart : Config :=
  invokeConfig encoderStore 2 [.i32 262144, .i32 13, .i32 262200]
noncomputable def decodeStart : Config :=
  invokeConfig (fresh.1.withBytes 100 validBlock) 3 [.i32 100, .i32 10, .i32 0]
noncomputable def outsideStart (x : UInt8) : Config :=
  invokeConfig (fresh.1.withBytes 0 [0, x, 0]) 3 [.i32 0, .i32 1, .i32 1024]
noncomputable def trapStart : Config :=
  invokeConfig (fresh.1.withBytes 65535 [0]) 3 [.i32 65535, .i32 1, .i32 0]

private theorem encode_observed :
    (runDet 1200 encodeStart).map (fun c => (c.instrs, bytesAt c.store 262200 13)) =
      some (vals [.i32 13], some encoderOutput) := by kernel_rfl
private theorem decode_observed :
    (runDet 300 decodeStart).map (fun c => (c.instrs, bytesAt c.store 0 13)) =
      some (vals [.i32 1], some (65 :: List.replicate 12 0)) := by kernel_rfl
private theorem outside_zero_observed :
    (runDet 300 (outsideStart 0)).map Config.instrs = some (vals [.i32 0]) := by kernel_rfl
private theorem outside_one_observed :
    (runDet 300 (outsideStart 1)).map Config.instrs = some (vals [.i32 4]) := by kernel_rfl
private theorem trap_observed :
    (runDet 100 trapStart).map Config.instrs = some [.trap] := by kernel_rfl

private theorem returns_bytes_of_observed {H : HostSem} {n : Nat} {c : Config}
    {vs : List Val} {p len : Nat} {bs : List UInt8}
    (h : (runDet n c).map (fun c => (c.instrs, bytesAt c.store p len)) =
      some (vals vs, some bs)) :
    Must H (fun | .returned s ws => ws = vs ∧ bytesAt s p len = some bs
                | .trapped _ => False) c := by
  obtain ⟨c', hr, ho⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hi, hm⟩ := Prod.mk.inj ho
  refine runDet_must hr ?_
  rintro (⟨s, ws⟩ | s) ⟨hs, hv⟩
  · have hvs := vals_inj.mp (hv.symm.trans hi)
    subst s; subst ws
    exact ⟨rfl, hm⟩
  · exact False.elim (vals_ne_trap vs (hi.symm.trans hv))

private theorem returns_of_observed {H : HostSem} {n : Nat} {c : Config} {vs : List Val}
    (h : (runDet n c).map Config.instrs = some (vals vs)) :
    Must H (fun | .returned _ ws => ws = vs | .trapped _ => False) c := by
  obtain ⟨c', hr, hi⟩ := Option.map_eq_some_iff.mp h
  refine runDet_must hr ?_
  rintro (⟨s, ws⟩ | s) ⟨_, hv⟩
  · exact vals_inj.mp (hv.symm.trans hi)
  · exact False.elim (vals_ne_trap vs (hi.symm.trans hv))

theorem r1_holds : r1 := by
  constructor
  · intro H
    obtain ⟨s, inst, h⟩ := instantiable_alloc (m := Lifted.module) rfl rfl rfl rfl rfl H
    have ha := instance_alloc rfl rfl rfl rfl h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
    exact h
  · intro H
    refine ⟨2, rfl, ⟨.wasm codecType fresh.2 Lifted.func2, rfl, ?_⟩, ?_⟩
    · simp [Val.HasType, FuncInst.type, codecType]
    · exact returns_bytes_of_observed encode_observed

theorem r2_holds : r2 := by
  intro H
  refine ⟨3, rfl, ⟨.wasm codecType fresh.2 Lifted.func3, rfl, ?_⟩, ?_⟩
  · simp [Val.HasType, FuncInst.type, codecType]
  · exact returns_bytes_of_observed decode_observed

theorem r3_holds : r3 := by
  constructor <;> intro H
  · refine ⟨3, rfl, ⟨.wasm codecType fresh.2 Lifted.func3, rfl, ?_⟩, ?_⟩
    · simp [Val.HasType, FuncInst.type, codecType]
    · exact returns_of_observed outside_zero_observed
  · refine ⟨3, rfl, ⟨.wasm codecType fresh.2 Lifted.func3, rfl, ?_⟩, ?_⟩
    · simp [Val.HasType, FuncInst.type, codecType]
    · exact returns_of_observed outside_one_observed

theorem emptyBlockTrap_holds : emptyBlockTrap := by
  intro H
  refine ⟨3, rfl, ⟨.wasm codecType fresh.2 Lifted.func3, rfl, ?_⟩, ?_⟩
  · simp [Val.HasType, FuncInst.type, codecType]
  · obtain ⟨c, hr, hi⟩ := Option.map_eq_some_iff.mp trap_observed
    refine runDet_must hr ?_
    rintro (⟨s, vs⟩ | s) ⟨_, hv⟩
    · exact False.elim (vals_ne_trap vs (hv.symm.trans hi))
    · trivial

end Proofs
