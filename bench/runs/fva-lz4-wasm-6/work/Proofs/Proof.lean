import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem fresh_instance (H : HostSem) : Instance Lifted.module H fresh.1 fresh.2 := by
  obtain ⟨s, inst, h⟩ := instantiable_alloc (m := Lifted.module) rfl rfl rfl rfl rfl H
  have ha := instance_alloc rfl rfl rfl rfl h
  change (s, inst) = fresh at ha
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
  exact h

private def checkBytes (s : Store) (p : Nat) (bs : List UInt8) : Bool :=
  match s.mems[0]? with
  | none => false
  | some m => (List.range bs.length).all fun i => m.byte (p+i) == bs[i]!

private theorem checkBytes_sound {s p bs} (h : checkBytes s p bs = true) : bytesAt s p bs := by
  unfold checkBytes at h
  cases hm : s.mems[0]? with
  | none => simp [hm] at h
  | some m =>
    refine ⟨m, hm, ?_⟩
    simp only [hm, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact h

private def isReturn32 (es : List AInstr) (n : Nat) : Bool :=
  match es with
  | [.plain (.iconst .w32 k)] => k == n
  | _ => false

private theorem isReturn32_sound {es n} (hn : n < 2^32)
    (h : isReturn32 es n = true) : es = vals [.i32 (BitVec.ofNat 32 n)] := by
  unfold isReturn32 at h
  split at h
  next k =>
    simp only [beq_iff_eq] at h
    subst k
    simp only [vals, List.map_cons, List.map_nil, Val.instr, BitVec.toNat_ofNat]
    have hn' : n < 4294967296 := hn
    rw [Nat.mod_eq_of_lt hn']
  all_goals contradiction

private theorem computed_return {H : HostSem} {c : Config} {fuel p n : Nat}
    {bs : List UInt8} (hn : n < 2^32)
    (h : (runDet fuel c).any (fun c' => isReturn32 c'.instrs n && checkBytes c'.store p bs) = true) :
    Must H (fun | .returned s v => v = [.i32 (BitVec.ofNat 32 n)] ∧ bytesAt s p bs
                | .trapped _ => False) c := by
  cases hr : runDet fuel c with
  | none => simp [hr] at h
  | some c' =>
    simp only [hr, Option.any_some, Bool.and_eq_true] at h
    have he : runDet fuel c = some ⟨c'.store, c'.frame, vals [.i32 (BitVec.ofNat 32 n)]⟩ := by
      rw [hr]; congr 1; exact congrArg (fun es => Config.mk c'.store c'.frame es) (isReturn32_sound hn h.1)
    exact must_returned_of_runDet he ⟨rfl, checkBytes_sound h.2⟩

private def isTrap : List AInstr → Bool
  | [.trap] => true
  | _ => false

private theorem isTrap_sound {es} (h : isTrap es = true) : es = [.trap] := by
  unfold isTrap at h
  split at h
  · rfl
  · contradiction

theorem r2_holds : r2 := by
  refine ⟨?_, rfl, ?_⟩
  · refine ⟨[65], [66,67,68,69,70,71,72,73], 1, 4, ?_⟩
    dsimp [validBlock, decodedContent, endConditions]
    decide +kernel
  · intro H
    refine ⟨3, rfl, ⟨_, rfl, by simp [Val.HasType, FuncInst.type, Lifted.module, Lifted.func3, Lifted.func2]⟩, ?_⟩
    apply computed_return (fuel := 300) (by decide)
    decide +kernel

private theorem computed_trap {H : HostSem} {c : Config} {fuel : Nat}
    (h : (runDet fuel c).any (fun c' => isTrap c'.instrs) = true) :
    Must H (fun | .returned _ _ => False | .trapped _ => True) c := by
  cases he : runDet fuel c with
  | none => simp [he] at h
  | some c' =>
    simp only [he, Option.any_some] at h
    have ht := isTrap_sound h
    apply runDet_must he
    rintro (⟨s, vs⟩ | s) ⟨hs, hv⟩
    · exact False.elim (vals_ne_trap vs (hv.symm.trans ht))
    · trivial

theorem r3_holds : r3 := by
  intro H
  refine ⟨3, rfl, ⟨_, rfl, by simp [Val.HasType, FuncInst.type,
    Lifted.module, Lifted.func3]⟩, ?_⟩
  apply computed_trap (fuel := 100)
  decide +kernel

theorem r1_holds : r1 := by
  refine ⟨?_, by simp [endConditions]⟩
  intro H
  refine ⟨2, rfl, ⟨_, rfl, by simp [Val.HasType, FuncInst.type, Lifted.module, Lifted.func3, Lifted.func2]⟩, ?_⟩
  apply computed_return (fuel := 1000) (by decide)
  decide +kernel

theorem preparation_holds : preparation := by
  refine ⟨fresh_instance, ?_, ?_, ?_⟩
  · refine ⟨_, _, rfl, rfl, rfl⟩
  · intro i hi
    refine ⟨_, rfl, ?_⟩
    have h0 : 4*i < 262144 := by omega
    have h1 : 4*i+1 < 262144 := by omega
    have h2 : 4*i+1+1 < 262144 := by omega
    have h3 : 4*i+1+1+1 < 262144 := by omega
    simp [encoderStore, MemInst.read, h0, h1, h2, h3, Nat.add_mod, Nat.mul_mod]
  · refine ⟨_, rfl, ?_⟩
    intro i hi
    have hlen : encoderInput.length = 13 := rfl
    have hlow : ¬ 262144 + i < 262144 := by omega
    have hhigh : 262144 + i < 262157 := by omega
    simp [encoderStore, hlow, hhigh]

theorem r3_dependence_holds : r3_dependence := by
  constructor <;> intro H
  · refine ⟨3, rfl, ⟨_, rfl, by simp [Val.HasType, FuncInst.type,
      Lifted.module, Lifted.func3]⟩, ?_⟩
    apply computed_return (fuel := 300) (by decide)
    decide +kernel
  · refine ⟨3, rfl, ⟨_, rfl, by simp [Val.HasType, FuncInst.type,
      Lifted.module, Lifted.func3]⟩, ?_⟩
    apply computed_return (fuel := 300) (by decide)
    decide +kernel

end Proofs
