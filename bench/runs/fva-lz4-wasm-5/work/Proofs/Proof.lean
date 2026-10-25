import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def returnValue (c : Config) : Option Nat :=
  match c.instrs with
  | [.plain (.iconst .w32 n)] => some n
  | _ => none

private theorem returnValue_sound {c : Config} {n : Nat}
    (h : returnValue c = some n) (hn : n < 2^32) :
    c.instrs = vals [.i32 (BitVec.ofNat 32 n)] := by
  unfold returnValue at h
  split at h
  · rename_i n' he
    have : n' = n := Option.some.inj h
    subst n'
    change c.instrs = [.plain (.iconst .w32 (n % 2^32))]
    rw [Nat.mod_eq_of_lt hn]
    exact he
  · contradiction

private theorem run_return {c : Config} {fuel n : Nat} {H : HostSem}
    (hn : n < 2^32)
    (h : (runDet fuel c).any (fun d => returnValue d == some n) = true) :
    Must H (fun | .returned _ vs => vs = [.i32 (BitVec.ofNat 32 n)]
                | .trapped _ => False) c := by
  obtain ⟨d, hd, hp⟩ := (Option.any_eq_true _ _).mp h
  have hv := returnValue_sound (eq_of_beq hp) hn
  apply runDet_must hd
  rintro (⟨s, vs⟩ | s) ⟨hs, hf⟩
  · exact vals_inj.mp (hf.symm.trans hv)
  · exact False.elim (vals_ne_trap _ (hv.symm.trans hf))

private theorem run_return_bytes {c : Config} {fuel n p len : Nat} {bs : List UInt8}
    {H : HostSem} (hn : n < 2^32)
    (h : (runDet fuel c).any (fun d =>
      (returnValue d == some n) && (bytesAt d.store p len == some bs)) = true) :
    Must H (fun | .returned s vs => vs = [.i32 (BitVec.ofNat 32 n)] ∧ bytesAt s p len = some bs
                | .trapped _ => False) c := by
  obtain ⟨d, hd, hp⟩ := (Option.any_eq_true _ _).mp h
  obtain ⟨hv, hb⟩ := Bool.and_eq_true_iff.mp hp
  have hv := returnValue_sound (eq_of_beq hv) hn
  have hb : bytesAt d.store p len = some bs := eq_of_beq hb
  apply runDet_must hd
  rintro (⟨s, vs⟩ | s) ⟨hs, hf⟩
  · exact ⟨vals_inj.mp (hf.symm.trans hv), hs ▸ hb⟩
  · exact False.elim (vals_ne_trap _ (hv.symm.trans hf))

theorem fresh_instance_holds : fresh_instance := by
  have hi : Instantiable Lifted.module := instantiable_alloc rfl rfl rfl rfl rfl
  refine ⟨hi, ?_⟩
  intro H
  obtain ⟨s, inst, h⟩ := hi H
  have ha := instance_alloc rfl rfl rfl rfl h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
  exact h

theorem r1_counterexample_holds : r1_counterexample := by
  refine ⟨?_, ?_⟩
  · intro H
    refine ⟨2, rfl, ⟨_, rfl, ?_⟩, ?_⟩
    · change List.Forall₂ (Val.HasType encoderStore) _ [.num .i32,.num .i32,.num .i32]
      exact .cons trivial (.cons trivial (.cons trivial .nil))
    · apply run_return_bytes (n := 13) (p := 300000) (len := 13) (bs := encoderOutput) (fuel := 2000) (by decide)
      decide +kernel
  · decide +kernel

theorem r2_counterexample_holds : r2_counterexample := by
  refine ⟨?_, rfl, ?_⟩
  · decide +kernel
  · intro H
    refine ⟨3, rfl, ⟨_, rfl, ?_⟩, ?_⟩
    · change List.Forall₂ (Val.HasType decoderStore) _ [.num .i32,.num .i32,.num .i32]
      exact .cons trivial (.cons trivial (.cons trivial .nil))
    · apply run_return_bytes (n := 1) (p := 0) (len := 13)
        (bs := 65 :: List.replicate 12 0) (fuel := 1000) (by decide)
      decide +kernel

theorem r3_counterexample_holds : r3_counterexample := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro H
    have hc : (walk 35 (invokeConfig (emptyStore 1) 3 [.i32 200,.i32 1,.i32 300])).any
        (fun c => (nextByteRead 20 c.instrs == some 201) && (step c).isSome) = true := by
      decide +kernel
    obtain ⟨c, hc, hp⟩ := (Option.any_eq_true _ _).mp hc
    obtain ⟨hr, hs⟩ := Bool.and_eq_true_iff.mp hp
    obtain ⟨c', hs⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨c, c', steps_of_walk hc, eq_of_beq hr, step_sound hs⟩
  · intro H
    refine ⟨3, rfl, ⟨_, rfl, ?_⟩, ?_⟩
    · change List.Forall₂ (Val.HasType (emptyStore 0)) _ [.num .i32,.num .i32,.num .i32]
      exact .cons trivial (.cons trivial (.cons trivial .nil))
    · apply run_return (n := 0) (fuel := 1000) (by decide)
      decide +kernel
  · intro H
    refine ⟨3, rfl, ⟨_, rfl, ?_⟩, ?_⟩
    · change List.Forall₂ (Val.HasType (emptyStore 1)) _ [.num .i32,.num .i32,.num .i32]
      exact .cons trivial (.cons trivial (.cons trivial .nil))
    · apply run_return (n := 4) (fuel := 1000) (by decide)
      decide +kernel

end Proofs
