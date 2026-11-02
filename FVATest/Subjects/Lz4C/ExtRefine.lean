import FVATest.Subjects.Lz4C.ExtCommon

/-! Checkpoint 1, route R (refinement): the loop simulates `extModel`, a Lean function of the
bytes; `ExtL1` follows from the simulation plus facts about the model alone (proof support; outside
the review surface). -/

namespace Subjects.Lz4C.Refine

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000

/-- Where the loop leaves: after the `k`-th read with the final accumulator and byte; before the
`k`-th read with the accumulator then; at the `k`-th read with the overflowing sum and byte. -/
inductive Exit where
  | normal (k a byte : Nat)
  | bound (k a : Nat)
  | overflow (k a byte : Nat)

/-- The loop as a function: from iteration `j` with accumulator `a`. -/
def extModel (b : Nat → UInt8) (p lim : Nat) (j a : Nat) : Exit :=
  if lim < p + j + 1 then .bound j a
  else if 2147483648 ≤ a + (b j).toNat then .overflow j (a + (b j).toNat) (b j).toNat
  else if b j = 255 then extModel b p lim (j + 1) (a + (b j).toNat)
  else .normal j (a + (b j).toNat) (b j).toNat
termination_by lim - (p + j)

/-- The frame at the head of iteration `j` holds the model's state `(p + j, a)`. -/
structure Sim (ls : List Val) (inst : ModuleInst) (p : Nat) (j a : Nat) (f : Frame) : Prop where
  inst : f.inst = inst
  len : f.locals.length = ls.length
  others : ∀ i, i ≠ 2 → i ≠ 4 → i ≠ 15 → i ≠ 17 → f.locals[i]? = ls[i]?
  l2 : f.locals[2]? = some (vI (p + j))
  l15 : f.locals[15]? = if j = 0 then ls[15]? else some (vI 255)
  l17 : f.locals[17]? = some (vI a)

/-- The wasm configuration of each model exit. -/
def SimExit (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (p : Nat) :
    Exit → Config → Prop
  | .normal k a byte, c => ∃ f', Locals ls inst f' (p + k + 1) (p + k + 1) (some byte) (some a) ∧
      c = (ctx8 C).fill ⟨s, f', (body8.drop 4).map .plain⟩
  | .bound k a, c => ∃ f', Locals ls inst f' (p + k) (p + k + 1)
      (if k = 0 then none else some 255) (some a) ∧
      c = C.fill ⟨s, f', (body2.drop 1).map .plain⟩
  | .overflow k a byte, c => ∃ f', Locals ls inst f' (p + k) (p + k + 1) (some byte) (some a) ∧
      c = C.fill ⟨s, f', (body2.drop 1).map .plain⟩

/-- One iteration simulates one model step. -/
theorem sim_one (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim j a : Nat) (f : Frame)
    (h14 : ls[14]? = some (vI lim)) (hm : inst.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some mem) (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size)
    (hlen17 : 17 < ls.length) (hj : p + j ≤ lim) (ha : a < 2 ^ 31) (hi : Sim ls inst p j a f)
    (hk : p + j + 1 ≤ lim → a + (mem.byte (p + j)).toNat < 2 ^ 31 → ∀ f',
      Sim ls inst p (j + 1) (a + (mem.byte (p + j)).toNat) f' →
      Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
        (SimExit C s inst ls p (extModel (fun i => mem.byte (p + i)) p lim (j + 1)
          (a + (mem.byte (p + j)).toNat))) (head C s f')) :
    Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
      (SimExit C s inst ls p (extModel (fun i => mem.byte (p + i)) p lim j a)) (head C s f) := by
  have hf14 : f.locals[14]? = some (vI lim) := by
    rw [hi.others 14 (by decide) (by decide) (by decide) (by decide), h14]
  have hlenf : f.locals.length = ls.length := hi.len
  have hadd := add32 (p + j) 1
  have hgt := igtU_ofNat (a := p + j + 1) (b := lim) (by omega) (by omega)
  rw [extModel]
  unfold head
  simp only [ctx9, Context.fill]
  wasm_cstepu [extBody, hi.l2]
  · wasm_within [extBody]
  wasm_cstepu [extBody, hi.l2, hadd]
  · wasm_within [extBody]
  wasm_cstepu [extBody, hi.l2, hadd]
  · wasm_within [extBody]
  wasm_cstepu [extBody, hi.l2, hadd, show 4 < f.locals.length by omega]
  · wasm_within [extBody]
  wasm_cstepu [extBody, getElem?_set_of_ne (show (4 : Nat) ≠ 14 by decide), hf14]
  · wasm_within [extBody]
  wasm_cstepu [extBody, hgt]
  · wasm_within [extBody]
  by_cases hb : lim < p + j + 1
  · have hc : Num.bool (decide (lim < p + j + 1)) = 1 := by simp [hb, bool_true]
    wasm_cstepu [extBody, hc, one_ne]
    · wasm_within [extBody]
    wasm_cstepu [extBody]
    · wasm_within [extBody]
    simp only [hb, ite_true]
    refine Until.done ⟨⟨f.locals.set 4 (vI (p + j + 1)), f.inst⟩,
      ⟨hi.inst, by simp [hlenf], fun i h₂ h₄ h₁₅ h₁₇ => ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · rw [getElem?_set_of_ne (Ne.symm h₄)]; exact hi.others i h₂ h₄ h₁₅ h₁₇
    · rw [getElem?_set_of_ne (by decide)]; exact hi.l2
    · rw [List.getElem?_set_self (by omega)]
    · rw [getElem?_set_of_ne (by decide), hi.l15]; split <;> rfl
    · rw [getElem?_set_of_ne (by decide), hi.l17]; rfl
  · have hc : Num.bool (decide (lim < p + j + 1)) = 0 := by simp [hb, bool_false]
    have hle : p + j + 1 ≤ lim := by omega
    have hm' : f.inst.mems[0]? = some ma := by rw [hi.inst]; exact hm
    have hpj : (BitVec.ofNat 32 (p + j)).toNat = p + j := ofNat32_toNat (by omega)
    have hblt : decide (mem.size < p + j + 1) = false := by simp; omega
    have hbyte : (mem.byte (p + j)).toNat < 256 := (mem.byte (p + j)).toNat_lt
    have hadd2 := add32 a (mem.byte (p + j)).toNat
    have hlt := iltS_zero (a := a + (mem.byte (p + j)).toNat) (by omega)
    have h15ls : 15 < ls.length := by omega
    wasm_cstepu [extBody, hc, zero_eq]
    · wasm_within [extBody]
    simp only [hb, ite_false]
    wasm_cstepu [extBody, getElem?_set_of_ne (show (4 : Nat) ≠ 17 by decide), hi.l17]
    · wasm_within [extBody]
    wasm_cstepu [extBody, getElem?_set_of_ne (show (4 : Nat) ≠ 2 by decide), hi.l2]
    · wasm_within [extBody]
    wasm_cstepu [extBody, hm', hmem, hpj, hblt, mem_read_one, PackSize.bits, packedVal,
      Nat.add_zero]
    · wasm_within [extBody, hm', hmem, hpj, hblt, PackSize.bits, Nat.add_zero]
      exact ⟨fun x h₁ h₂ => ⟨trivial, by omega, by omega⟩, by simp⟩
    iterate 5 (wasm_cstepu [extBody, List.length_set, hlenf, h15ls, hlen17, hadd2]
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
      simp only [ho, ite_true]
      refine Until.done ⟨⟨((f.locals.set 4 (vI (p + j + 1))).set 15
        (vI (mem.byte (p + j)).toNat)).set 17 (vI (a + (mem.byte (p + j)).toNat)), f.inst⟩,
        ⟨hi.inst, by simp [hlenf], fun i h₂ h₄ h₁₅ h₁₇ => ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
      · rw [getElem?_set_of_ne (Ne.symm h₁₇), getElem?_set_of_ne (Ne.symm h₁₅),
          getElem?_set_of_ne (Ne.symm h₄)]; exact hi.others i h₂ h₄ h₁₅ h₁₇
      · rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
          getElem?_set_of_ne (by decide)]; exact hi.l2
      · rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
          List.getElem?_set_self (by omega)]
      · rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp; omega)]; rfl
      · rw [List.getElem?_set_self (by simp; omega)]; rfl
    · have hlt0 : iltS (BitVec.ofNat 32 (a + (mem.byte (p + j)).toNat))
          (BitVec.ofNat 32 0) = 0 := by
        rw [hlt]; simp [ho, bool_false]
      have h2ls : 2 < ls.length := by omega
      have h4ls : 4 < ls.length := by omega
      simp only [ho, ite_false]
      wasm_cstepu [extBody, hlt0]
      · wasm_within [extBody]
      wasm_cstepu [extBody, zero_eq]
      · wasm_within [extBody]
      wasm_cstepu [extBody, getElem?_set_of_ne (show (17 : Nat) ≠ 4 by decide),
        getElem?_set_of_ne (show (15 : Nat) ≠ 4 by decide), List.getElem?_set_self,
        List.length_set, hlenf, h4ls]
      · wasm_within [extBody]
      wasm_cstepu [extBody, List.length_set, hlenf, h2ls]
      · wasm_within [extBody]
      wasm_cstepu [extBody, getElem?_set_of_ne (show (2 : Nat) ≠ 15 by decide),
        getElem?_set_of_ne (show (17 : Nat) ≠ 15 by decide), List.getElem?_set_self,
        List.length_set, hlenf, h15ls]
      · wasm_within [extBody]
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
        simp only [hff, ite_true]
        have hsim : Sim ls inst p (j + 1) (a + (mem.byte (p + j)).toNat)
            ⟨(((f.locals.set 4 (vI (p + j + 1))).set 15 (vI (mem.byte (p + j)).toNat)).set 17
              (vI (a + (mem.byte (p + j)).toNat))).set 2 (vI (p + j + 1)), f.inst⟩ :=
          { inst := hi.inst
            len := by simp [hlenf]
            others := fun i h₂ h₄ h₁₅ h₁₇ => by
              simp only
              rw [getElem?_set_of_ne (Ne.symm h₂), getElem?_set_of_ne (Ne.symm h₁₇),
                getElem?_set_of_ne (Ne.symm h₁₅), getElem?_set_of_ne (Ne.symm h₄)]
              exact hi.others i h₂ h₄ h₁₅ h₁₇
            l2 := by simp only; rw [List.getElem?_set_self (by simp; omega)]; rfl
            l15 := by
              simp only [Nat.add_one_ne_zero, ite_false]
              rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
                List.getElem?_set_self (by simp; omega), hff]; rfl
            l17 := by
              simp only
              rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp; omega)] }
        have hnext := hk hle (by omega) _ hsim
        rw [hff] at hnext
        simpa only [head, ctx9, Context.fill, extBody, List.map_cons, List.map_nil] using hnext
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
        wasm_cstepu [extBody]
        · wasm_within [extBody]
        simp only [hff, ite_false]
        refine Until.done ⟨⟨(((f.locals.set 4 (vI (p + j + 1))).set 15
          (vI (mem.byte (p + j)).toNat)).set 17 (vI (a + (mem.byte (p + j)).toNat))).set 2
          (vI (p + j + 1)), f.inst⟩, ⟨hi.inst, by simp [hlenf], fun i h₂ h₄ h₁₅ h₁₇ => ?_, ?_, ?_,
          ?_, ?_⟩, by simp only [ctx8, Context.fill]⟩
        · simp only
          rw [getElem?_set_of_ne (Ne.symm h₂), getElem?_set_of_ne (Ne.symm h₁₇),
            getElem?_set_of_ne (Ne.symm h₁₅), getElem?_set_of_ne (Ne.symm h₄)]
          exact hi.others i h₂ h₄ h₁₅ h₁₇
        · simp only; rw [List.getElem?_set_self (by simp; omega)]
        · simp only
          rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
            getElem?_set_of_ne (by decide), List.getElem?_set_self (by omega)]
        · simp only
          rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
            List.getElem?_set_self (by simp; omega)]; rfl
        · simp only
          rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp; omega)]; rfl

/-- The loop simulates the model from every head. -/
theorem sim (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim : Nat)
    (h14 : ls[14]? = some (vI lim)) (hm : inst.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some mem) (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size)
    (hlen17 : 17 < ls.length) :
    ∀ n j a f, lim - (p + j) = n → p + j ≤ lim → a < 2 ^ 31 → Sim ls inst p j a f →
    Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
      (SimExit C s inst ls p (extModel (fun i => mem.byte (p + i)) p lim j a)) (head C s f) := by
  intro n
  induction n with
  | zero =>
    intro j a f hn hj ha hi
    exact sim_one H C s inst ls ma mem p lim j a f h14 hm hmem hlim hsize hlen17 hj ha hi
      (fun hle => absurd hle (by omega))
  | succ n ih =>
    intro j a f hn hj ha hi
    exact sim_one H C s inst ls ma mem p lim j a f h14 hm hmem hlim hsize hlen17 hj ha hi
      (fun hle ha' f' hi' => ih (j + 1) _ f' (by omega) hle ha' hi')

/-- What a model exit says about the bytes (no wasm here). -/
def ModelOK (b : Nat → UInt8) (p lim acc : Nat) : Exit → Prop
  | .normal k a byte => (∀ i < k, b i = 255) ∧ b k ≠ 255 ∧ p + k + 1 ≤ lim ∧
      (∀ i ≤ k, psum acc b i < 2 ^ 31) ∧ a = psum acc b k ∧ byte = (b k).toNat
  | .bound k a => (∀ i < k, b i = 255) ∧ lim < p + k + 1 ∧
      (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
      a = (if k = 0 then acc else psum acc b (k - 1))
  | .overflow k a byte => (∀ i < k, b i = 255) ∧ p + k + 1 ≤ lim ∧
      (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧ 2 ^ 31 ≤ psum acc b k ∧ a = psum acc b k ∧
      byte = (b k).toNat

theorem psum_zero (acc : Nat) (b : Nat → UInt8) : psum acc b 0 = acc + (b 0).toNat := by
  simp [psum]

theorem psum_succ (acc : Nat) (b : Nat → UInt8) (k : Nat) :
    psum acc b (k + 1) = psum acc b k + (b (k + 1)).toNat := by
  simp [psum, List.range_succ, Nat.add_assoc]

/-- The model's exit from iteration `j`, accumulator `a` = the sum of the bytes before `j`. -/
theorem model_ok (b : Nat → UInt8) (p lim acc : Nat) :
    ∀ n j a, lim - (p + j) = n → a = (if j = 0 then acc else psum acc b (j - 1)) →
    (∀ i < j, b i = 255) → (∀ i, i + 1 ≤ j → psum acc b i < 2 ^ 31) →
    ModelOK b p lim acc (extModel b p lim j a) := by
  intro n
  induction n with
  | zero =>
    intro j a hn ha hff hs
    rw [extModel]
    have hb : lim < p + j + 1 := by omega
    simp only [hb, ite_true]
    exact ⟨hff, hb, hs, ha⟩
  | succ n ih =>
    intro j a hn ha hff hs
    have hstep : a + (b j).toNat = psum acc b j := by
      rcases j with _ | j
      · simp [ha, psum_zero]
      · simp [ha, psum_succ]
    rw [extModel]
    by_cases hb : lim < p + j + 1
    · simp only [hb, ite_true]; exact ⟨hff, hb, hs, ha⟩
    simp only [hb, ite_false]
    by_cases ho : 2147483648 ≤ a + (b j).toNat
    · simp only [ho, ite_true]
      exact ⟨hff, by omega, hs, by rw [← hstep]; exact ho, hstep, rfl⟩
    simp only [ho, ite_false]
    by_cases h255 : b j = 255
    · simp only [h255, ite_true]
      have := ih (j + 1) (a + (b j).toNat) (by omega) (by simp [hstep])
        (fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
          · exact hff i h
          · exact h255)
        (fun i hi => by
          rcases Nat.lt_or_ge i j with h | h
          · exact hs i h
          · obtain rfl : i = j := by omega
            rw [← hstep]; omega)
      rwa [h255] at this
    · simp only [h255, ite_false]
      exact ⟨hff, h255, by omega, fun i hi => by
        rcases Nat.lt_or_ge i j with h | h
        · exact hs i h
        · obtain rfl : i = j := by omega
          rw [← hstep]; omega, hstep, rfl⟩

/-- Checkpoint 1's statement, route R: simulation + the model's exits. -/
theorem ext_l1 : ExtL1 := by
  intro H C s inst ls ma mem p lim acc h2 h14 h17 hm hmem hpl hlim hsize hacc
  have hlen17 : 17 < ls.length := (List.getElem?_eq_some_iff.mp h17).1
  have hsim0 : Sim ls inst p 0 acc ⟨ls, inst⟩ :=
    { inst := rfl, len := rfl, others := fun _ _ _ _ _ => rfl, l2 := by simpa using h2,
      l15 := by simp, l17 := h17 }
  have hok := model_ok (fun i => mem.byte (p + i)) p lim acc _ 0 acc rfl (by simp)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (by omega))
  have hrun := sim H C s inst ls ma mem p lim h14 hm hmem hlim hsize hlen17 _ 0 acc
    ⟨ls, inst⟩ rfl (by omega) hacc hsim0
  rw [extLoop_eq]
  simp only [ctx9, Context.fill]
  wasm_cstepu [extBody]
  · wasm_within [extBody]
  refine Until.mono (P := Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
    (by simpa only [head, ctx9, Context.fill, extBody, List.map_cons, List.map_nil] using hrun)
    (fun _ h => h) ?_
  intro c hc
  revert hok hc
  generalize extModel (fun i => mem.byte (p + i)) p lim 0 acc = e
  rcases e with ⟨k, a, byte⟩ | ⟨k, a⟩ | ⟨k, a, byte⟩
  · rintro ⟨hff, h255, hle, hs, rfl, rfl⟩ ⟨f', hl, rfl⟩
    exact Or.inl ⟨k, f', hff, h255, hle, hs, hl, rfl⟩
  · rintro ⟨hff, hb, hs, rfl⟩ ⟨f', ⟨hi, hlen, ho, l2, l4, l15, l17⟩, rfl⟩
    refine Or.inr (Or.inl ⟨k, f', hff, hb, hs, ⟨hi, hlen, ho, l2, l4, ?_, ?_⟩, rfl⟩)
    · rw [l15]; split
      · rfl
      · rename_i hk; rw [hff (k - 1) (by omega)]; rfl
    · rw [l17]; split
      · simp [h17]
      · rfl
  · rintro ⟨hff, hle, hs, hov, rfl, rfl⟩ ⟨f', hl, rfl⟩
    exact Or.inr (Or.inr ⟨k, f', hff, hle, hs, hov, hl, rfl⟩)

end Subjects.Lz4C.Refine
