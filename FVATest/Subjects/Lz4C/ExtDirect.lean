import FVATest.Subjects.Lz4C.ExtCommon

/-! Checkpoint 1, route D (direct): `ExtL1` by stepping the loop with an invariant over the loop
head's frame, by induction on the bytes left before `lim` (proof support; outside the review
surface). -/

namespace Subjects.Lz4C.Direct

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000

/-- `acc + b 0 + … + b (j − 1)`: the accumulator at the head of iteration `j`. -/
def run (acc : Nat) (b : Nat → UInt8) (j : Nat) : Nat :=
  acc + ((List.range j).map fun i => (b i).toNat).sum

theorem psum_eq (acc : Nat) (b : Nat → UInt8) (j : Nat) : psum acc b j = run acc b (j + 1) := rfl

theorem run_succ (acc : Nat) (b : Nat → UInt8) (j : Nat) :
    run acc b (j + 1) = run acc b j + (b j).toNat := by
  simp [run, List.range_succ, Nat.add_assoc]

theorem run_zero (acc : Nat) (b : Nat → UInt8) : run acc b 0 = acc := by simp [run]

/-- The frame at the head of iteration `j`. -/
structure Inv (ls : List Val) (inst : ModuleInst) (p lim acc : Nat) (b : Nat → UInt8) (j : Nat)
    (f : Frame) : Prop where
  inst : f.inst = inst
  len : f.locals.length = ls.length
  others : ∀ i, i ≠ 2 → i ≠ 4 → i ≠ 15 → i ≠ 17 → f.locals[i]? = ls[i]?
  l2 : f.locals[2]? = some (vI (p + j))
  l15 : f.locals[15]? = if j = 0 then ls[15]? else some (vI (b (j - 1)).toNat)
  l17 : f.locals[17]? = some (vI (run acc b j))
  ff : ∀ i < j, b i = 255
  sums : ∀ i, i + 1 ≤ j → psum acc b i < 2 ^ 31
  bound : p + j ≤ lim

variable {H : HostSem} {C : Context} {s : Store} {inst : ModuleInst} {ls : List Val} {ma : Nat}
  {mem : MemInst} {p lim acc : Nat}

/-- The exit locals' unchanged part, from the head frame's. -/
theorem locals_of_inv {b : Nat → UInt8} {j : Nat} {f : Frame} (hi : Inv ls inst p lim acc b j f)
    {l2 l4 : Nat} {v15 v17 : Option Nat} {f' : Frame}
    (hinst : f'.inst = inst) (hlen : f'.locals.length = f.locals.length)
    (hother : ∀ i, i ≠ 2 → i ≠ 4 → i ≠ 15 → i ≠ 17 → f'.locals[i]? = f.locals[i]?)
    (h2 : f'.locals[2]? = some (vI l2)) (h4 : f'.locals[4]? = some (vI l4))
    (h15 : f'.locals[15]? = (v15.map vI <|> ls[15]?))
    (h17' : f'.locals[17]? = (v17.map vI <|> ls[17]?)) :
    Locals ls inst f' l2 l4 v15 v17 :=
  ⟨hinst, hlen.trans hi.len, fun i h₂ h₄ h₁₅ h₁₇ => (hother i h₂ h₄ h₁₅ h₁₇).trans
    (hi.others i h₂ h₄ h₁₅ h₁₇), h2, h4, h15, h17'⟩

/-- `Inv`'s local 15 as an exit local: unchanged at `j = 0`, the previous byte after. -/
theorem l15_exit {b : Nat → UInt8} {j : Nat} {f : Frame} (hi : Inv ls inst p lim acc b j f) :
    f.locals[15]? = ((if j = 0 then none else some (b (j - 1)).toNat).map vI <|> ls[15]?) := by
  rw [hi.l15]; split <;> rfl

/-- `Inv`'s local 17 as an exit local. -/
theorem l17_exit {b : Nat → UInt8} {j : Nat} {f : Frame} (hi : Inv ls inst p lim acc b j f)
    (h17 : ls[17]? = some (vI acc)) :
    f.locals[17]? = ((if j = 0 then none else some (psum acc b (j - 1))).map vI <|> ls[17]?) := by
  rw [hi.l17]
  split
  · subst_vars; simp [run_zero, h17]
  · rename_i hj
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [psum_eq]

/-- The accumulator at a head stays below `2^31`. -/
theorem run_lt {b : Nat → UInt8} {j : Nat} {f : Frame} (hi : Inv ls inst p lim acc b j f)
    (hacc : acc < 2 ^ 31) : run acc b j < 2 ^ 31 := by
  rcases j with _ | j
  · simpa [run_zero] using hacc
  · rw [← psum_eq]; exact hi.sums j le_rfl

/-- One iteration from the head of iteration `j`: an exit, or the head of iteration `j + 1`. -/
theorem one_iter (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim acc j : Nat) (f : Frame)
    (h14 : ls[14]? = some (vI lim)) (h17 : ls[17]? = some (vI acc))
    (hm : inst.mems[0]? = some ma) (hmem : s.mems[ma]? = some mem)
    (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size) (hacc : acc < 2 ^ 31)
    (hi : Inv ls inst p lim acc (fun i => mem.byte (p + i)) j f)
    (hk : p + j + 1 ≤ lim → ∀ f', Inv ls inst p lim acc (fun i => mem.byte (p + i)) (j + 1) f' →
      Until H (Within (fun m a => m = ma ∧ p ≤ a ∧ a < lim) (fun _ _ => False))
        (ExtExit C s inst ls p lim acc fun i => mem.byte (p + i)) (head C s f')) :
    Until H (Within (fun m a => m = ma ∧ p ≤ a ∧ a < lim) (fun _ _ => False))
      (ExtExit C s inst ls p lim acc fun i => mem.byte (p + i)) (head C s f) := by
  have hlen17 : 17 < ls.length := by
    have := List.getElem?_eq_some_iff.mp h17; exact this.1
  have hf14 : f.locals[14]? = some (vI lim) := by
    rw [hi.others 14 (by decide) (by decide) (by decide) (by decide), h14]
  have hlenf : f.locals.length = ls.length := hi.len
  have hb0 := hi.bound
  have hadd := iadd_ofNat (p + j) 1
  have hgt := igtU_ofNat (a := p + j + 1) (b := lim) (by omega) (by omega)
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
  · -- bound exit: `p + j + 1 > lim` before the `j`-th read
    have hc : bool (decide (lim < p + j + 1)) = 1 := by simp [hb, bool_true]
    wasm_cstepu [extBody, hc, one_ne]
    · wasm_within [extBody]
    wasm_cstepu [extBody]
    · wasm_within [extBody]
    refine Until.done (Or.inr (Or.inl ⟨j, _, hi.ff, hb, hi.sums, ?_, rfl⟩))
    refine locals_of_inv hi hi.inst (by simp) (fun i h₂ h₄ _ _ => getElem?_set_of_ne (Ne.symm h₄))
      (by rw [getElem?_set_of_ne (by decide)]; exact hi.l2) ?_ ?_ ?_
    · rw [List.getElem?_set_self (by omega)]
    · rw [getElem?_set_of_ne (by decide)]; exact l15_exit hi
    · rw [getElem?_set_of_ne (by decide)]; exact l17_exit hi h17
  · -- the read of byte `j`
    have hc : bool (decide (lim < p + j + 1)) = 0 := by simp [hb, bool_false]
    have hle : p + j + 1 ≤ lim := by omega
    have hm' : f.inst.mems[0]? = some ma := by rw [hi.inst]; exact hm
    have hpj : (BitVec.ofNat 32 (p + j)).toNat = p + j := ofNat_toNat (by omega)
    have hblt : decide (mem.size < p + j + 1) = false := by simp; omega
    have hrl := run_lt hi hacc
    have hbyte : (mem.byte (p + j)).toNat < 256 := (mem.byte (p + j)).toNat_lt
    have hadd2 := iadd_ofNat (run acc (fun i => mem.byte (p + i)) j) (mem.byte (p + j)).toNat
    have hlt := iltS_zero (a := run acc (fun i => mem.byte (p + i)) j + (mem.byte (p + j)).toNat)
      (by omega)
    wasm_cstepu [extBody, hc, zero_eq]
    · wasm_within [extBody]
    wasm_cstepu [extBody, getElem?_set_of_ne (show (4 : Nat) ≠ 17 by decide), hi.l17]
    · wasm_within [extBody]
    wasm_cstepu [extBody, getElem?_set_of_ne (show (4 : Nat) ≠ 2 by decide), hi.l2]
    · wasm_within [extBody]
    wasm_cstepu [extBody, hm', hmem, hpj, hblt, read_one, PackSize.bits, packedVal,
      Nat.add_zero]
    · wasm_within [extBody, hm', hmem, hpj, hblt, PackSize.bits, Nat.add_zero]
      exact ⟨fun a h₁ h₂ => ⟨trivial, by omega, by omega⟩, by simp⟩
    have h15ls : 15 < ls.length := by omega
    iterate 5 (wasm_cstepu [extBody, List.length_set, hlenf, h15ls, hlen17, hadd2]
               · wasm_within [extBody])
    by_cases ho : 2147483648 ≤ run acc (fun i => mem.byte (p + i)) j + (mem.byte (p + j)).toNat
    · -- overflow exit at the `j`-th read
      have hlt1 : iltS (BitVec.ofNat 32 (run acc (fun i => mem.byte (p + i)) j +
          (mem.byte (p + j)).toNat)) (BitVec.ofNat 32 0) = 1 := by rw [hlt]; simp [ho, bool_true]
      wasm_cstepu [extBody, hlt1]
      · wasm_within [extBody]
      wasm_cstepu [extBody, one_ne]
      · wasm_within [extBody]
      wasm_cstepu [extBody]
      · wasm_within [extBody]
      have hps : psum acc (fun i => mem.byte (p + i)) j =
          run acc (fun i => mem.byte (p + i)) j + (mem.byte (p + j)).toNat := by
        rw [psum_eq, run_succ]
      refine Until.done (Or.inr (Or.inr ⟨j, _, hi.ff, hle, hi.sums, by rw [hps]; exact ho, ?_,
        rfl⟩))
      refine locals_of_inv hi hi.inst (by simp) (fun i h₂ h₄ h₁₅ h₁₇ => ?_) ?_ ?_ ?_ ?_
      · rw [getElem?_set_of_ne (Ne.symm h₁₇), getElem?_set_of_ne (Ne.symm h₁₅),
          getElem?_set_of_ne (Ne.symm h₄)]
      · rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
          getElem?_set_of_ne (by decide)]; exact hi.l2
      · rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
          List.getElem?_set_self (by omega)]
      · rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp; omega)]; rfl
      · rw [List.getElem?_set_self (by simp; omega), hps]; rfl
    · -- no overflow: `p = p'`, then the 255 test
      have hlt0 : iltS (BitVec.ofNat 32 (run acc (fun i => mem.byte (p + i)) j +
          (mem.byte (p + j)).toNat)) (BitVec.ofNat 32 0) = 0 := by rw [hlt]; simp [ho, bool_false]
      have h2ls : 2 < ls.length := by omega
      have h4ls : 4 < ls.length := by omega
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
      have hps : psum acc (fun i => mem.byte (p + i)) j =
          run acc (fun i => mem.byte (p + i)) j + (mem.byte (p + j)).toNat := by
        rw [psum_eq, run_succ]
      by_cases hff : mem.byte (p + j) = 255
      · -- the byte is 255: back to the loop head with iteration `j + 1`
        have heq1 : ieq (BitVec.ofNat 32 (mem.byte (p + j)).toNat) (BitVec.ofNat 32 255) = 1 := by
          rw [hb255, hff]; rfl
        wasm_cstepu [extBody, heq1]
        · wasm_within [extBody]
        wasm_cstepu [extBody, one_ne]
        · wasm_within [extBody]
        wasm_cstepu [extBody]
        · wasm_within [extBody]
        wasm_cstepu [extBody]
        · wasm_within [extBody]
        have hinv : Inv ls inst p lim acc (fun i => mem.byte (p + i)) (j + 1)
            ⟨(((f.locals.set 4 (vI (p + j + 1))).set 15 (vI (mem.byte (p + j)).toNat)).set 17
              (vI (run acc (fun i => mem.byte (p + i)) j + (mem.byte (p + j)).toNat))).set 2
              (vI (p + j + 1)), f.inst⟩ :=
          { inst := hi.inst
            len := by simp [hlenf]
            others := fun i h₂ h₄ h₁₅ h₁₇ => by
              simp only
              rw [getElem?_set_of_ne (Ne.symm h₂), getElem?_set_of_ne (Ne.symm h₁₇),
                getElem?_set_of_ne (Ne.symm h₁₅), getElem?_set_of_ne (Ne.symm h₄)]
              exact hi.others i h₂ h₄ h₁₅ h₁₇
            l2 := by simp only; rw [List.getElem?_set_self (by simp; omega)]; rfl
            l15 := by
              simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
              rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
                List.getElem?_set_self (by simp; omega)]
            l17 := by
              simp only
              rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp; omega), run_succ]
            ff := fun i hi' => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
              · exact hi.ff i h
              · exact hff
            sums := fun i hi' => by
              rcases Nat.lt_or_ge i j with h | h
              · exact hi.sums i h
              · obtain rfl : i = j := by omega
                rw [hps]; omega
            bound := hle }
        have hnext := hk hle _ hinv
        simpa only [head, ctx9, Context.fill, extBody, List.map_cons, List.map_nil] using hnext
      · -- any other byte: the loop and block `@9` end, the normal exit
        have heq0 : ieq (BitVec.ofNat 32 (mem.byte (p + j)).toNat) (BitVec.ofNat 32 255) = 0 := by
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
        refine Until.done (Or.inl ⟨j, _, hi.ff, hff, hle, fun i hi' => ?_, ?_,
          by simp only [ctx8, Context.fill]; rfl⟩)
        · rcases Nat.lt_or_ge i j with h | h
          · exact hi.sums i h
          · obtain rfl : i = j := by omega
            rw [hps]; omega
        refine locals_of_inv hi hi.inst (by simp) (fun i h₂ h₄ h₁₅ h₁₇ => ?_) ?_ ?_ ?_ ?_
        · simp only
          rw [getElem?_set_of_ne (Ne.symm h₂), getElem?_set_of_ne (Ne.symm h₁₇),
            getElem?_set_of_ne (Ne.symm h₁₅), getElem?_set_of_ne (Ne.symm h₄)]
        · simp only; rw [List.getElem?_set_self (by simp; omega)]
        · simp only
          rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
            getElem?_set_of_ne (by decide), List.getElem?_set_self (by omega)]
        · simp only
          rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
            List.getElem?_set_self (by simp; omega)]; rfl
        · simp only
          rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp; omega), hps]; rfl

/-- Every iteration, by induction on the bytes left before `lim`. -/
theorem iter (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim acc : Nat)
    (h14 : ls[14]? = some (vI lim)) (h17 : ls[17]? = some (vI acc))
    (hm : inst.mems[0]? = some ma) (hmem : s.mems[ma]? = some mem)
    (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size) (hacc : acc < 2 ^ 31) :
    ∀ n j f, lim - (p + j) = n → Inv ls inst p lim acc (fun i => mem.byte (p + i)) j f →
    Until H (Within (fun m a => m = ma ∧ p ≤ a ∧ a < lim) (fun _ _ => False))
      (ExtExit C s inst ls p lim acc fun i => mem.byte (p + i)) (head C s f) := by
  intro n
  induction n with
  | zero =>
    intro j f hn hi
    exact one_iter H C s inst ls ma mem p lim acc j f h14 h17 hm hmem hlim hsize hacc hi
      (fun hle => absurd hle (by omega))
  | succ n ih =>
    intro j f hn hi
    exact one_iter H C s inst ls ma mem p lim acc j f h14 h17 hm hmem hlim hsize hacc hi
      (fun _ f' hi' => ih (j + 1) f' (by omega) hi')

/-- Checkpoint 1's statement, route D. -/
theorem ext_l1 : ExtL1 := by
  intro H C s inst ls ma mem p lim acc h2 h14 h17 hm hmem hpl hlim hsize hacc
  have hlen17 : 17 < ls.length := (List.getElem?_eq_some_iff.mp h17).1
  have hinv : Inv ls inst p lim acc (fun i => mem.byte (p + i)) 0 ⟨ls, inst⟩ :=
    { inst := rfl
      len := rfl
      others := fun _ _ _ _ _ => rfl
      l2 := by simpa using h2
      l15 := by simp
      l17 := by simpa [run_zero] using h17
      ff := fun _ h => absurd h (Nat.not_lt_zero _)
      sums := fun _ h => absurd h (by omega)
      bound := by omega }
  rw [extLoop_eq]
  simp only [ctx9, Context.fill]
  wasm_cstepu [extBody]
  · wasm_within [extBody]
  simpa only [head, ctx9, Context.fill, extBody, List.map_cons, List.map_nil] using
    iter H C s inst ls ma mem p lim acc h14 h17 hm hmem hlim hsize hacc _ 0 _ rfl hinv

end Subjects.Lz4C.Direct
