import FVATest.Examples.Toy.Spec
import FVA.Proof.Lib.Instance
import FVA.Proof.Lib.Arith

/-! Proofs of the toy claims. -/

namespace Examples.Toy

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

/-- Gauss: `0 + 1 + … + (k − 1) = k (k − 1) / 2`. -/
theorem sum_range_eq (k : Nat) : (List.range k).sum = k * (k - 1) / 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.sum_append, ih, List.sum_singleton]
    rcases k with _ | k
    · rfl
    · have he : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
      simp only [Nat.add_sub_cancel, he, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

/-- The compiled closed form `(k − 1) + ((k − 1)(k − 2) mod 2^64) / 2` agrees with Gauss mod
2^32. -/
theorem sumTo_value (n : BitVec 32) (hn : n ≠ 0) :
    iadd (iadd n 4294967295#32)
        (wrap (ishrU (imul (extendU (iadd n 4294967295#32)) (extendU (iadd n 4294967294#32)))
          1#64)) =
      BitVec.ofNat 32 (List.range n.toNat).sum := by
  have hk : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hn
    · exact h
  have hlt := n.isLt
  rw [sum_range_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [iadd, wrap, ishrU, imul, extendU, BitVec.toNat_ofNat]
  generalize n.toNat = k at hk hlt ⊢
  norm_num
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · simp
  -- k = j + 2: no wrap-around anywhere, then Gauss
  have hprod : (j + 1) * j < 2 ^ 64 := by
    calc (j + 1) * j ≤ (j + 1) * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 2 ^ 64 := by norm_num
  have he : (j + 1 + 1) * (j + 1) / 2 = (j + 1) + (j + 1) * j / 2 := by
    have : (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]; omega
  have h1 : (j + 1 + 1 + 4294967295) % 4294967296 = j + 1 := by omega
  have h2 : (j + 1 + 1 + 4294967294) % 4294967296 = j := by omega
  simp only [Nat.add_sub_cancel, h1, h2, he]
  have hp : (j + 1) * j < 18446744073709551616 := hprod
  rw [Nat.mod_eq_of_lt hp]
  generalize (j + 1) * j / 2 = t
  omega

theorem sumTo_holds : sumTo := by
  intro n
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[2]? = some (.wasm ⟨[.num .i32], [.num .i32]⟩ inst Lifted.func2) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "sum_to" = some 2 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨2, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  by_cases hn : n = 0
  · subst hn
    wasm_run [hf, Lifted.func2]
    exact Must.done (o := .returned s [.i32 0]) ⟨rfl, rfl⟩ rfl
  · wasm_run [hf, Lifted.func2, hn]
    refine Must.done (o := .returned s [.i32 _]) ⟨rfl, rfl⟩ ?_
    show [Val.i32 _] = _
    rw [sumTo_value n hn]

/-- The compiled loop body of `gcd` (`a, b := b, a mod b` while `b ≠ 0`; local 2 = last `b`). -/
def gcdBody : List Instr :=
  [.localGet 0, .localGet 1, .localTee 2, .ibinop .w32 (.rem .u), .localSet 1, .localGet 2,
    .localSet 0, .localGet 1, .brIf 0]

/-- The configuration at the head of `gcd`'s loop with locals `a b t`. -/
def gcdHead (s : Store) (inst : ModuleInst) (a b t : BitVec 32) : Config :=
  ⟨s, ⟨[], {}⟩, [.frame 1 ⟨[.i32 a, .i32 b, .i32 t], inst⟩
    [.label 1 [] [.label 0 [.loop .empty gcdBody] (gcdBody.map .plain), .plain (.localGet 2)]]]⟩

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
      have := ih (a.toNat % b.toNat) (hk ▸ hlt) b (BitVec.ofNat 32 (a.toNat % b.toNat)) b hm hr
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
    wasm_run [hf, Lifted.func1]
    refine Must.done (o := .returned s [.i32 a]) ⟨rfl, rfl⟩ ?_
    show [Val.i32 a] = _
    simp
  · -- 6 steps: into the frame, past the early return, at the loop head with `t = 0`
    iterate 6 wasm_step1 [hf, Lifted.func1, hb]
    show Must _ _ (gcdHead s inst a b _)
    exact gcd_loop H s inst _ a b _ rfl hb

end Examples.Toy
