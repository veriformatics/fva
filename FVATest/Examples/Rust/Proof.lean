import FVATest.Examples.Rust.Spec
import FVA.Proof.Lib.Instance
import FVA.Proof.Lib.Arith

/-! Proofs of the Rust example's claims. -/

namespace Examples.Rust

open FVA.Wasm FVA.Wasm.Num FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem clamp_holds : clamp := by
  intro x lo hi
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[0]? = some (.wasm ⟨[.num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst
      Lifted.func0) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "clamp" = some 0 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨0, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  -- the select chain as compiled: `x <s lo ? lo : (x <s hi ? x : hi)`
  let r := if iltS x lo = 0#32 then (if iltS x hi = 0#32 then hi else x) else lo
  have hr : runDet 40 (invokeConfig s 0 [.i32 x, .i32 lo, .i32 hi]) =
      some ⟨s, ⟨[], {}⟩, vals [.i32 r]⟩ := by
    simp [runDet, wasm_step, invokeConfig, hf, Lifted.func0, irelop, r]
    split_ifs <;> rfl
  refine must_returned_of_runDet hr ?_
  show [Val.i32 r] = _
  simp only [r, iltS_eq_zero, List.cons.injEq, Val.i32.injEq, and_true]
  by_cases h₁ : x.slt lo <;> by_cases h₂ : x.slt hi <;> by_cases h₃ : hi.slt x <;>
    simp only [h₁, h₂, h₃, ite_true, ite_false, Bool.false_eq_true, not_false_eq_true,
      not_true_eq_false]
  -- left: `¬ x <s hi` and `¬ hi <s x`, the same value
  all_goals
    simp only [BitVec.slt_iff_toInt_lt, not_lt] at h₂ h₃
    exact BitVec.toInt_inj.mp (by omega)

/-- The compiled loop body of `gcd` (`t := a mod b; a, b := b, t` while `t ≠ 0`). -/
def gcdBody : List Instr :=
  [.localGet 0, .localGet 1, .ibinop .w32 (.rem .u), .localSet 2, .localGet 1, .localSet 0,
    .localGet 2, .localSet 1, .localGet 2, .brIf 0]

/-- The configuration at the head of `gcd`'s loop with locals `a b t`. -/
def gcdHead (s : Store) (inst : ModuleInst) (a b t : BitVec 32) : Config :=
  ⟨s, ⟨[], {}⟩, [.frame 1 ⟨[.i32 a, .i32 b, .i32 t], inst⟩
    [.label 1 [] [.label 0 [] [.label 0 [.loop .empty gcdBody] (gcdBody.map .plain)],
      .plain (.localGet 0)]]]⟩

theorem gcd_loop (H : HostSem) (s : Store) (inst : ModuleInst) :
    ∀ (k : Nat) (a b t : BitVec 32), b.toNat = k → b ≠ 0 →
      Must H (fun | .returned _ vs => vs = [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]
                  | .trapped _ => False) (gcdHead s inst a b t) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a b t hk hb
    have hbn : ¬ b.toNat = 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlt : a.toNat % b.toNat < b.toNat := Nat.mod_lt _ (Nat.pos_of_ne_zero hbn)
    by_cases hr : BitVec.ofNat 32 (a.toNat % b.toNat) = 0
    · -- the remainder is zero: the loop exits and returns `b`
      unfold gcdHead
      wasm_run [gcdBody, iremU, hbn, hr]
      refine Must.done (o := .returned s [.i32 b]) ⟨rfl, rfl⟩ ?_
      show [Val.i32 b] = _
      have h0 : a.toNat % b.toNat = 0 := by
        have := congrArg BitVec.toNat hr
        simpa [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.le_of_lt b.isLt))] using this
      rw [Nat.gcd_comm, Nat.gcd_rec, h0, Nat.gcd_zero_left]
      simp
    · -- another round with `b, a mod b`: the 12 steps of one iteration, back at the head
      unfold gcdHead
      iterate 12 wasm_step1 [gcdBody, iremU, hbn, hr]
      have hm : (BitVec.ofNat 32 (a.toNat % b.toNat)).toNat = a.toNat % b.toNat :=
        by simp [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.le_of_lt b.isLt))]
      have := ih (a.toNat % b.toNat) (hk ▸ hlt) b (BitVec.ofNat 32 (a.toNat % b.toNat))
        (BitVec.ofNat 32 (a.toNat % b.toNat)) hm hr
      have hg : Nat.gcd b.toNat (a.toNat % b.toNat) = Nat.gcd a.toNat b.toNat := by
        rw [Nat.gcd_comm b.toNat, ← Nat.gcd_rec, Nat.gcd_comm]
      rw [hm, hg] at this
      simpa only [gcdHead, gcdBody, List.map_cons, List.map_nil] using this

theorem gcd_holds : gcd := by
  intro a b
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[1]? = some (.wasm ⟨[.num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func1) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "gcd" = some 1 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨1, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  by_cases hb : b = 0
  · subst hb
    have hz : (ieqz (0 : BitVec 32) = 0) = False := by decide
    wasm_run [hf, Lifted.func1, hz]
    refine Must.done (o := .returned s [.i32 a]) ⟨rfl, rfl⟩ ?_
    show [Val.i32 a] = _
    simp
  · -- 6 steps: into the frame, past the zero test, at the loop head with `t = 0`
    iterate 6 wasm_step1 [hf, Lifted.func1, hb, ieqz_eq_zero]
    show Must _ _ (gcdHead s inst a b _)
    exact gcd_loop H s inst _ a b _ rfl hb

end Examples.Rust
