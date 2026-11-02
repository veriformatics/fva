import FVATest.Subjects.Lz4C.O1.Common
import FVATest.Subjects.Lz4C.ExtRefine

/-! M4 repair, route R: the `-O1` loop simulates the same `extModel`; `model_ok` carries over
unchanged (proof support; outside the review surface). -/

namespace Subjects.Lz4C.O1.Refine

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.Lz4C.Refine

set_option maxHeartbeats 4000000

/-- The head frame of iteration `j` holds the model's state: `q = p + j + 1`, accumulator `a`,
and the previous iteration's pointer, sum and byte (entry values at `j = 0`). -/
structure Sim (ls : List Val) (inst : ModuleInst) (p : Nat) (j a : Nat) (f : Frame) : Prop where
  inst : f.inst = inst
  len : f.locals.length = ls.length
  others : ∀ i, i ≠ 3 → i ≠ 4 → i ≠ 16 → i ≠ 17 → i ≠ 18 → i ≠ 19 → i ≠ 20 →
    f.locals[i]? = ls[i]?
  l18 : f.locals[18]? = some (vI (p + j + 1))
  l19 : f.locals[19]? = some (vI a)
  l16 : f.locals[16]? = if j = 0 then ls[16]? else some (vI (p + j))
  l17 : f.locals[17]? = if j = 0 then ls[17]? else some (vI a)
  l20 : f.locals[20]? = if j = 0 then ls[20]? else some (vI 255)

/-- The `-O1` configuration of each model exit. -/
def SimExit (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (p : Nat) :
    Exit → Config → Prop
  | .normal k a byte, c => ∃ f', LocalsAt ls inst f' [(18, some (p + k + 2)), (19, some a),
      (4, some a), (3, some (p + k + 1)), (20, some byte), (16, some (p + k + 1)), (17, some a)] ∧
      c = C.fill ⟨s, f', (b11.drop 2).map .plain⟩
  | .bound k a, c => ∃ f', LocalsAt ls inst f' [(18, some (p + k + 1)), (19, some a), (4, some a),
      (3, some (p + k + 1)), (20, if k = 0 then none else some 255),
      (16, if k = 0 then none else some (p + k)), (17, if k = 0 then none else some a)] ∧
      c = (Context.label 0 [] ((b11.drop 2).map .plain) C).fill ⟨s, f', (b12.drop 19).map .plain⟩
  | .overflow k a byte, c => ∃ f', LocalsAt ls inst f' [(18, some (p + k + 1)),
      (19, some (a - byte)), (4, some a), (3, some (p + k + 1)), (20, some byte),
      (16, if k = 0 then none else some (p + k)), (17, if k = 0 then none else some (a - byte))] ∧
      c = (Context.label 0 [] ((b11.drop 2).map .plain) C).fill ⟨s, f', (b12.drop 19).map .plain⟩

/-- One `-O1` iteration simulates one model step. -/
theorem sim_one (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim j a : Nat) (f : Frame)
    (h14 : ls[14]? = some (vI lim)) (hm : inst.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some mem) (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size)
    (h20 : 20 < ls.length) (hj : p + j ≤ lim) (ha : a < 2 ^ 31) (hi : Sim ls inst p j a f)
    (hk : p + j + 1 ≤ lim → a + (mem.byte (p + j)).toNat < 2 ^ 31 → ∀ f',
      Sim ls inst p (j + 1) (a + (mem.byte (p + j)).toNat) f' →
      Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
        (SimExit C s inst ls p (extModel (fun i => mem.byte (p + i)) p lim (j + 1)
          (a + (mem.byte (p + j)).toNat))) (head C s f')) :
    Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
      (SimExit C s inst ls p (extModel (fun i => mem.byte (p + i)) p lim j a)) (head C s f) := by
  have hf14 : f.locals[14]? = some (vI lim) := by
    rw [hi.others 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h14]
  have hlenf : f.locals.length = ls.length := hi.len
  have hgt := igtU_ofNat (a := p + j + 1) (b := lim) (by omega) (by omega)
  have h3 : 3 < ls.length := by omega
  have h4 : 4 < ls.length := by omega
  have h16 : 16 < ls.length := by omega
  have h17 : 17 < ls.length := by omega
  have h18 : 18 < ls.length := by omega
  have h19 : 19 < ls.length := by omega
  rw [extModel]
  unfold head
  simp only [ctx, Context.fill]
  iterate 7 (wasm_cstepu [extBody, hi.l18, hi.l19, hf14, List.getElem?_set, List.length_set,
               hlenf, h3, h4, h20, hgt]
             · wasm_within [extBody])
  by_cases hb : lim < p + j + 1
  · have hc : Num.bool (decide (lim < p + j + 1)) = 1 := by simp [hb, bool_true]
    wasm_cstepu [extBody, hc, one_ne]
    · wasm_within [extBody]
    wasm_cstepu [extBody]
    · wasm_within [extBody]
    simp only [hb, ite_true]
    refine Until.done ⟨⟨(f.locals.set 4 (vI a)).set 3 (vI (p + j + 1)), f.inst⟩,
      ⟨hi.inst, by simp [hlenf], ?_⟩, by simp only [Context.fill]⟩
    have hother := hi.others
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · locals_at [hi.l16, hi.l17, hi.l18, hi.l19, hi.l20, hlenf, h3, h4, hother]
    · have hj0' := Nat.pos_iff_ne_zero.mp hj0
      locals_at [hi.l16, hi.l17, hi.l18, hi.l19, hi.l20, hlenf, h3, h4, hother, hj0']
  · have hc : Num.bool (decide (lim < p + j + 1)) = 0 := by simp [hb, bool_false]
    have hle : p + j + 1 ≤ lim := by omega
    have hm' : f.inst.mems[0]? = some ma := by rw [hi.inst]; exact hm
    have hq := add32_m1 (a := p + j + 1) (by omega)
    have hpj : (BitVec.ofNat 32 (p + j + 1 - 1)).toNat = p + j := by
      rw [Nat.add_sub_cancel]; exact ofNat32_toNat (by omega)
    have hblt : decide (mem.size < p + j + 1) = false := by simp; omega
    have hbyte : (mem.byte (p + j)).toNat < 256 := (mem.byte (p + j)).toNat_lt
    have hadd2 := add32 a (mem.byte (p + j)).toNat
    have hlt := iltS_zero (a := a + (mem.byte (p + j)).toNat) (by omega)
    have hadd1 := add32 (p + j + 1) 1
    wasm_cstepu [extBody, hc, zero_eq]
    · wasm_within [extBody]
    iterate 3 (wasm_cstepu [extBody, List.getElem?_set, List.length_set, hlenf, h3, h4, hq]
               · wasm_within [extBody])
    wasm_cstepu [extBody, hm', hmem, hpj, hblt, mem_read_one, PackSize.bits, packedVal,
      Nat.add_zero]
    · wasm_within [extBody, hm', hmem, hpj, hblt, PackSize.bits, Nat.add_zero]
      exact ⟨fun x h₁ h₂ => ⟨trivial, by omega, by omega⟩, by simp⟩
    iterate 5 (wasm_cstepu [extBody, List.getElem?_set, List.length_set, hlenf, h3, h4, h20,
                 hadd2]
               · wasm_within [extBody])
    by_cases ho : 2147483648 ≤ a + (mem.byte (p + j)).toNat
    · have hlt1 : iltS (BitVec.ofNat 32 (a + (mem.byte (p + j)).toNat))
          (BitVec.ofNat 32 0) = 1 := by
        rw [hlt]; simp [ho, bool_true]
      wasm_cstepu [extBody, hlt1]
      · wasm_within [extBody]
      wasm_cstepu [extBody, one_ne]
      · wasm_within [extBody]
      wasm_cstepu [extBody]
      · wasm_within [extBody]
      simp only [hb, ite_false, ho, ite_true]
      refine Until.done ⟨⟨(((f.locals.set 4 (vI a)).set 3 (vI (p + j + 1))).set 20
        (vI (mem.byte (p + j)).toNat)).set 4 (vI (a + (mem.byte (p + j)).toNat)), f.inst⟩,
        ⟨hi.inst, by simp [hlenf], ?_⟩, by simp only [Context.fill]⟩
      have hother := hi.others
      have hsub : a + (mem.byte (p + j)).toNat - (mem.byte (p + j)).toNat = a := by omega
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · locals_at [hi.l16, hi.l17, hi.l18, hi.l19, hi.l20, hlenf, h3, h4, h20, hother, hsub]
      · have hj0' := Nat.pos_iff_ne_zero.mp hj0
        locals_at [hi.l16, hi.l17, hi.l18, hi.l19, hi.l20, hlenf, h3, h4, h20, hother, hsub, hj0']
    · have hlt0 : iltS (BitVec.ofNat 32 (a + (mem.byte (p + j)).toNat))
          (BitVec.ofNat 32 0) = 0 := by
        rw [hlt]; simp [ho, bool_false]
      wasm_cstepu [extBody, hlt0]
      · wasm_within [extBody]
      wasm_cstepu [extBody, zero_eq]
      · wasm_within [extBody]
      iterate 10 (wasm_cstepu [extBody, List.getElem?_set, List.length_set, hlenf, h3, h4, h16,
                    h17, h18, h19, h20, hadd1]
                  · wasm_within [extBody])
      have hb255 := ieq_ofNat (a := (mem.byte (p + j)).toNat) (b := 255) (by omega) (by decide)
      by_cases hff : mem.byte (p + j) = 255
      · have heq1 : ieq (BitVec.ofNat 32 (mem.byte (p + j)).toNat) (BitVec.ofNat 32 255) = 1 := by
          rw [hb255, hff]; rfl
        wasm_cstepu [extBody, heq1]
        · wasm_within [extBody]
        wasm_cstepu [extBody, one_ne]
        · wasm_within [extBody]
        wasm_cstepu [extBody]
        · wasm_within [extBody]
        wasm_cstepu [extBody]
        · wasm_within [extBody]
        simp only [hb, ite_false, ho]
        split
        rotate_left
        · contradiction
        have hother := hi.others
        have hsim : Sim ls inst p (j + 1) (a + (mem.byte (p + j)).toNat)
            ⟨(((((((f.locals.set 4 (vI a)).set 3 (vI (p + j + 1))).set 20
              (vI (mem.byte (p + j)).toNat)).set 4 (vI (a + (mem.byte (p + j)).toNat))).set 18
              (vI (p + j + 1 + 1))).set 19 (vI (a + (mem.byte (p + j)).toNat))).set 16
              (vI (p + j + 1))).set 17 (vI (a + (mem.byte (p + j)).toNat)), f.inst⟩ :=
          { inst := hi.inst
            len := by simp [hlenf]
            others := fun i h₃ h₄ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ => by
              simp [Ne.symm h₃, Ne.symm h₄, Ne.symm h₁₆, Ne.symm h₁₇,
                Ne.symm h₁₈, Ne.symm h₁₉, Ne.symm h₂₀, hother i h₃ h₄ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀]
            l18 := by
              rw [show p + (j + 1) + 1 = p + j + 1 + 1 by omega]
              simp [hlenf, h18]
            l19 := by simp [hlenf, h19]
            l16 := by
              rw [show p + (j + 1) = p + j + 1 by omega]
              simp [hlenf, h16]
            l17 := by simp [hlenf, h17]
            l20 := by simp [hlenf, h20, hff] }
        have hnext := hk hle (by omega) _ hsim
        simpa only [head, ctx, Context.fill, extBody, List.map_cons, List.map_nil] using hnext
      · have heq0 : ieq (BitVec.ofNat 32 (mem.byte (p + j)).toNat) (BitVec.ofNat 32 255) = 0 := by
          rw [hb255]
          have : ((mem.byte (p + j)).toNat == 255) = false := by
            rw [beq_eq_false_iff_ne]; intro h; exact hff (UInt8.toNat_inj.mp (by simpa using h))
          rw [this]; rfl
        wasm_cstepu [extBody, heq0]
        · wasm_within [extBody]
        wasm_cstepu [extBody, zero_eq]
        · wasm_within [extBody]
        wasm_cstepu [extBody]
        · wasm_within [extBody]
        simp only [hb, ite_false, ho]
        split
        · contradiction
        refine Until.done ⟨⟨(((((((f.locals.set 4 (vI a)).set 3 (vI (p + j + 1))).set 20
          (vI (mem.byte (p + j)).toNat)).set 4 (vI (a + (mem.byte (p + j)).toNat))).set 18
          (vI (p + j + 1 + 1))).set 19 (vI (a + (mem.byte (p + j)).toNat))).set 16
          (vI (p + j + 1))).set 17 (vI (a + (mem.byte (p + j)).toNat)), f.inst⟩,
          ⟨hi.inst, by simp [hlenf], ?_⟩, rfl⟩
        have hother := hi.others
        have h2 : p + j + 1 + 1 = p + j + 2 := by omega
        locals_at [hlenf, h3, h4, h16, h17, h18, h19, h20, hother, h2]

/-- The `-O1` loop simulates the model from every head. -/
theorem sim (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim : Nat)
    (h14 : ls[14]? = some (vI lim)) (hm : inst.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some mem) (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size)
    (h20 : 20 < ls.length) :
    ∀ n j a f, lim - (p + j) = n → p + j ≤ lim → a < 2 ^ 31 → Sim ls inst p j a f →
    Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
      (SimExit C s inst ls p (extModel (fun i => mem.byte (p + i)) p lim j a)) (head C s f) := by
  intro n
  induction n with
  | zero =>
    intro j a f hn hj ha hi
    exact sim_one H C s inst ls ma mem p lim j a f h14 hm hmem hlim hsize h20 hj ha hi
      (fun hle => absurd hle (by omega))
  | succ n ih =>
    intro j a f hn hj ha hi
    exact sim_one H C s inst ls ma mem p lim j a f h14 hm hmem hlim hsize h20 hj ha hi
      (fun hle ha' f' hi' => ih (j + 1) _ f' (by omega) hle ha' hi')

theorem psum_sub (acc : Nat) (b : Nat → UInt8) (k : Nat) :
    psum acc b k - (b k).toNat = if k = 0 then acc else psum acc b (k - 1) := by
  rcases k with _ | k
  · simp [psum_zero]
  · simp [psum_succ]

/-- `ExtL1` for the `-O1` loop, route R: the new simulation + the unchanged `model_ok`. -/
theorem ext_l1 : ExtL1O1 := by
  intro H C s inst ls ma mem p lim acc h18 h14 h19 h20 hm hmem hpl hlim hsize hacc
  have hsim0 : Sim ls inst p 0 acc ⟨ls, inst⟩ :=
    { inst := rfl, len := rfl, others := fun _ _ _ _ _ _ _ _ => rfl, l18 := by simpa using h18,
      l19 := h19, l16 := by simp, l17 := by simp, l20 := by simp }
  have hok := model_ok (fun i => mem.byte (p + i)) p lim acc _ 0 acc rfl (by simp)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (by omega))
  have hrun := sim H C s inst ls ma mem p lim h14 hm hmem hlim hsize h20 _ 0 acc
    ⟨ls, inst⟩ rfl (by omega) hacc hsim0
  rw [extLoop_eq]
  simp only [ctx, Context.fill]
  wasm_cstepu [extBody]
  · wasm_within [extBody]
  refine Until.mono (P := Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
    (by simpa only [head, ctx, Context.fill, extBody, List.map_cons, List.map_nil] using hrun)
    (fun _ h => h) ?_
  intro c hc
  revert hok hc
  generalize extModel (fun i => mem.byte (p + i)) p lim 0 acc = e
  rcases e with ⟨k, a, byte⟩ | ⟨k, a⟩ | ⟨k, a, byte⟩
  · rintro ⟨hff, h255, hle, hs, rfl, rfl⟩ ⟨f', hl, rfl⟩
    exact Or.inl ⟨k, f', hff, h255, hle, hs, hl, rfl⟩
  · rintro ⟨hff, hb, hs, rfl⟩ ⟨f', hl, rfl⟩
    refine Or.inr (Or.inl ⟨k, f', hff, hb, hs, ?_, rfl⟩)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hl
    · have hk' := Nat.pos_iff_ne_zero.mp hk
      have hb1 : (mem.byte (p + (k - 1))).toNat = 255 := by
        have h := hff (k - 1) (by omega); simp only at h; rw [h]; rfl
      simpa [hk', hb1] using hl
  · rintro ⟨hff, hle, hs, hov, rfl, rfl⟩ ⟨f', hl, rfl⟩
    refine Or.inr (Or.inr ⟨k, f', hff, hle, hs, hov, ?_, rfl⟩)
    rw [psum_sub] at hl
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hl
    · simpa [Nat.pos_iff_ne_zero.mp hk] using hl

end Subjects.Lz4C.O1.Refine
