import FVATest.Examples.Mem.Spec
import FVA.Proof.Lib.Instance
import FVA.Proof.Lib.Arith
import FVA.Proof.Lib.Mem
import Mathlib.Data.BitVec

/-! Proofs of the `mem.wasm` claims. -/

namespace Examples.Mem

open FVA.Wasm FVA.Wasm.Num FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem callScale_holds : callScale := by
  intro x
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf1 : s.funcs[1]? = some (.wasm ⟨[.num .i32], [.num .i32]⟩ inst Lifted.func1) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have hf2 : s.funcs[2]? = some (.wasm ⟨[.num .i32], [.num .i32]⟩ inst Lifted.func2) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have hi2 : inst.funcs[2]? = some 2 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "call_scale" = some 1 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨1, he, ⟨_, hf1, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  wasm_run [hf1, hf2, hi2, Lifted.func1, Lifted.func2]
  refine Must.done (o := .returned s [.i32 _]) ⟨rfl, rfl⟩ ?_
  show [Val.i32 _] = _
  simp only [iadd_eq, imul_eq, List.cons.injEq, Val.i32.injEq, and_true]
  bv_omega

theorem classify_holds : classify := by
  intro x y
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[3]? = some (.wasm ⟨[.num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func3) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "classify" = some 3 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨3, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  -- the `br_table` index: one case per target
  obtain hx | hx | hx | hx | hx | hx : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 ∨
      x.toNat = 4 ∨ 5 ≤ x.toNat := by omega
  all_goals
    wasm_run [hf, Lifted.func3, hx, List.getElem?_eq_none]
    refine Must.done (o := .returned s [.i32 _]) ⟨rfl, rfl⟩ ?_
    show [Val.i32 _] = _
    split <;> first
      | omega
      | (simp_all [iadd_eq, imul_eq, ixor_eq, ishl_eq]; done)
      | (simp_all [iadd_eq]; bv_omega)

/-- The compiled loop body of `array_sum` (locals: address, words left, sum so far). -/
def sumBody : List Instr :=
  [.localGet 0, .load .i32 ⟨2, 0⟩, .localGet 2, .ibinop .w32 .add, .localSet 2, .localGet 0,
    .iconst .w32 4, .ibinop .w32 .add, .localSet 0, .localGet 1, .iconst .w32 4294967295,
    .ibinop .w32 .add, .localTee 1, .brIf 0]

/-- The configuration at the head of `array_sum`'s loop with locals `a c acc`. -/
def sumHead (s : Store) (inst : ModuleInst) (a c acc : BitVec 32) : Config :=
  ⟨s, ⟨[], {}⟩, [.frame 1 ⟨[.i32 a, .i32 c, .i32 acc], inst⟩
    [.label 1 [] [.label 0 [] [.label 0 [.loop .empty sumBody] (sumBody.map .plain)],
      .plain (.localGet 2)]]]⟩

theorem sum_loop (H : HostSem) (s : Store) (inst : ModuleInst) (mem : MemInst) (p : Nat)
    (xs : List (BitVec 32)) (hm : inst.mems[0]? = some 0)
    (hw : s.mems[0]? = some (mem.withBytes p (le32s xs))) (hsize : p + 4 * xs.length ≤ 65536)
    (hmem : mem.size = 65536) :
    ∀ (k i : Nat) (a c acc : BitVec 32), i + k + 1 = xs.length → a.toNat = p + 4 * i →
      c.toNat = k + 1 → acc = (xs.take i).sum →
      Must H (fun | .returned _ vs => vs = [.i32 xs.sum] | .trapped _ => False)
        (sumHead s inst a c acc) := by
  intro k
  induction k with
  | zero =>
    intro i a c acc hi ha hc hacc
    have hb : ¬ mem.size < p + 4 * i + 4 := by omega
    have hr := read_le32s mem (p := p) (show i < xs.length by omega)
    have hx : BitVec.ofNat 32 xs[i].toNat = xs[i] := by simp
    have hc' : iadd c (BitVec.ofNat 32 4294967295) = 0 := by
      apply BitVec.eq_of_toNat_eq; simp [iadd, hc]
    unfold sumHead
    wasm_run [sumBody, hm, hw, ha, Nat.add_zero, MemInst.withBytes_size, hb, hr, hx, hc']
    refine Must.done (o := .returned s [.i32 _]) ⟨rfl, rfl⟩ ?_
    show [Val.i32 _] = _
    have hsum := List.sum_take_succ xs i (by omega)
    rw [List.take_of_length_le (by omega)] at hsum
    simp only [hsum, hacc, iadd_eq, List.cons.injEq, Val.i32.injEq, and_true]
    exact BitVec.add_comm _ _
  | succ k ih =>
    intro i a c acc hi ha hc hacc
    have hb : ¬ mem.size < p + 4 * i + 4 := by omega
    have hr := read_le32s mem (p := p) (show i < xs.length by omega)
    have hx : BitVec.ofNat 32 xs[i].toNat = xs[i] := by simp
    have hc'v : (iadd c (BitVec.ofNat 32 4294967295)).toNat = k + 1 := by
      simp only [iadd, BitVec.toNat_ofNat, hc]; omega
    have hc' : ¬ iadd c (BitVec.ofNat 32 4294967295) = 0 := by
      intro h0; have := congrArg BitVec.toNat h0; simp [hc'v] at this
    unfold sumHead
    iterate 15 wasm_step1 [sumBody, hm, hw, ha, Nat.add_zero, MemInst.withBytes_size, hb, hr, hx,
      hc']
    refine ih (i + 1) _ _ _ (by omega) ?_ hc'v ?_
    · simp only [iadd, BitVec.toNat_ofNat, ha]; omega
    · rw [iadd_eq, hacc, List.sum_take_succ _ _ (by omega)]
      exact BitVec.add_comm _ _

theorem arraySum_holds : arraySum := by
  intro p xs hp
  refine ⟨fun H => ?_, ?_⟩
  · -- the fresh instance has the array's room: one 64 KiB page
    obtain ⟨s, inst, h⟩ := instantiable_alloc (m := Lifted.module) rfl rfl rfl rfl rfl H
    refine ⟨s, inst, h, ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (instance_alloc rfl rfl rfl rfl h)
    exact ⟨_, rfl, by rw [le32s_length]; simpa [MemInst.size] using hp⟩
  intro H s inst h hfit
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[0]? = some (.wasm ⟨[.num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func0) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "array_sum" = some 0 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have hm : inst.mems[0]? = some 0 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have hs : s.mems[0]? = some ⟨1, none, fun _ => 0⟩ := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  have hw := Store.withBytes_mem0 hs p.toNat (le32s xs)
  refine ⟨0, he, ⟨_, by rw [Store.withBytes_funcs]; exact hf,
    by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  by_cases hn : xs = []
  · subst hn
    have hz : (ieqz (0#32 : BitVec 32) = 0) = False := by decide
    wasm_run [hf, Lifted.func0, Store.withBytes_funcs, hz]
    exact Must.done (o := .returned _ [.i32 0#32]) ⟨rfl, rfl⟩ rfl
  · obtain ⟨mem, hmem, hfit⟩ := hfit
    rw [hs, Option.some.injEq] at hmem
    subst hmem
    rw [le32s_length] at hfit
    have hfit' : p.toNat + 4 * xs.length ≤ 65536 := by simpa [MemInst.size] using hfit
    have hlen : BitVec.ofNat 32 xs.length ≠ 0 := by
      have : 0 < xs.length := List.length_pos_iff.mpr hn
      simp only [MemInst.size] at hfit
      intro h0
      have := congrArg BitVec.toNat h0
      simp at this
      omega
    iterate 7 wasm_step1 [hf, Lifted.func0, Store.withBytes_funcs, ieqz_eq_zero, hlen]
    have hl : 0 < xs.length := List.length_pos_iff.mpr hn
    exact sum_loop H _ inst _ p.toNat xs hm hw hfit' rfl (xs.length - 1) 0 p _ 0 (by omega)
      (by simp) (by simp; omega) (by simp)

end Examples.Mem
