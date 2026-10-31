import FVATest.Subjects.Lz4C.O1.Common
import FVATest.Subjects.Lz4C.ExtDirect

/-! M4 repair, route D: the `-O1` loop with an invariant over the head frame, stating `ExtL1O1`'s
exits directly (proof support; outside the review surface). -/

namespace Subjects.Lz4C.O1.Direct

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.Lz4C.Direct

set_option maxHeartbeats 4000000

/-- The head frame of iteration `j`. -/
structure Inv (ls : List Val) (inst : ModuleInst) (p lim acc : Nat) (b : Nat → UInt8) (j : Nat)
    (f : Frame) : Prop where
  inst : f.inst = inst
  len : f.locals.length = ls.length
  others : ∀ i, i ≠ 3 → i ≠ 4 → i ≠ 16 → i ≠ 17 → i ≠ 18 → i ≠ 19 → i ≠ 20 →
    f.locals[i]? = ls[i]?
  l18 : f.locals[18]? = some (vI (p + j + 1))
  l19 : f.locals[19]? = some (vI (run acc b j))
  l16 : f.locals[16]? = if j = 0 then ls[16]? else some (vI (p + j))
  l17 : f.locals[17]? = if j = 0 then ls[17]? else some (vI (run acc b j))
  l20 : f.locals[20]? = if j = 0 then ls[20]? else some (vI (b (j - 1)).toNat)
  ff : ∀ i < j, b i = 255
  sums : ∀ i, i + 1 ≤ j → psum acc b i < 2 ^ 31
  bound : p + j ≤ lim

/-- One `-O1` iteration: an exit, or the head of iteration `j + 1`. -/
theorem one_iter (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim acc j : Nat) (f : Frame)
    (h14 : ls[14]? = some (vI lim)) (hm : inst.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some mem) (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size)
    (h20 : 20 < ls.length) (hacc : acc < 2 ^ 31)
    (hi : Inv ls inst p lim acc (fun i => mem.byte (p + i)) j f)
    (hk : p + j + 1 ≤ lim → ∀ f', Inv ls inst p lim acc (fun i => mem.byte (p + i)) (j + 1) f' →
      Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
        (ExtExit C s inst ls p lim acc (fun i => mem.byte (p + i))) (head C s f')) :
    Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
      (ExtExit C s inst ls p lim acc (fun i => mem.byte (p + i))) (head C s f) := by
  have ha : run acc (fun i => mem.byte (p + i)) j < 2 ^ 31 := by
    rcases j with _ | j
    · simpa [run_zero] using hacc
    · rw [← psum_eq]; exact hi.sums j le_rfl
  obtain ⟨a, ha_def⟩ : ∃ a, a = run acc (fun i => mem.byte (p + i)) j := ⟨_, rfl⟩
  rw [← ha_def] at ha
  have hl19 : f.locals[19]? = some (vI a) := by rw [hi.l19, ha_def]
  have hl17 : f.locals[17]? = if j = 0 then ls[17]? else some (vI a) := by rw [hi.l17, ha_def]
  have hj := hi.bound
  have hps : psum acc (fun i => mem.byte (p + i)) j = a + (mem.byte (p + j)).toNat := by
    rw [psum_eq, run_succ, ha_def]
  have hpsr : 0 < j → psum acc (fun i => mem.byte (p + i)) (j - 1) = a := fun h => by
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [ha_def, psum_eq]
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
  unfold head
  simp only [ctx, Context.fill]
  iterate 7 (wasm_cstepu [extBody, hi.l18, hl19, hf14, List.getElem?_set, List.length_set,
               hlenf, h3, h4, h20, hgt]
             · wasm_within [extBody])
  by_cases hb : lim < p + j + 1
  · have hc : Num.bool (decide (lim < p + j + 1)) = 1 := by simp [hb, bool_true]
    wasm_cstepu [extBody, hc, one_ne]
    · wasm_within [extBody]
    wasm_cstepu [extBody]
    · wasm_within [extBody]
    refine Until.done (Or.inr (Or.inl ⟨j, ⟨(f.locals.set 4 (vI a)).set 3 (vI (p + j + 1)), f.inst⟩,
      hi.ff, hb, hi.sums, ⟨hi.inst, by simp [hlenf], ?_⟩, by simp only [Context.fill]⟩))
    have hother := hi.others
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · locals_at [hi.l16, hl17, hi.l18, hl19, hi.l20, hlenf, h3, h4, hother, ha_def, run_zero]
    · have hj0' := Nat.pos_iff_ne_zero.mp hj0
      have h1 := hpsr hj0
      locals_at [hi.l16, hl17, hi.l18, hl19, hi.l20, hlenf, h3, h4, hother, hj0', h1]
  · have hc : Num.bool (decide (lim < p + j + 1)) = 0 := by simp [hb, bool_false]
    have hle : p + j + 1 ≤ lim := by omega
    have hm' : f.inst.mems[0]? = some ma := by rw [hi.inst]; exact hm
    have hq := iadd_minus_one (q := p + j + 1) (by omega) (by omega)
    have hpj : (BitVec.ofNat 32 (p + j + 1 - 1)).toNat = p + j := by
      rw [Nat.add_sub_cancel]; exact ofNat_toNat (by omega)
    have hblt : decide (mem.size < p + j + 1) = false := by simp; omega
    have hbyte : (mem.byte (p + j)).toNat < 256 := (mem.byte (p + j)).toNat_lt
    have hadd2 := iadd_ofNat a (mem.byte (p + j)).toNat
    have hlt := iltS_zero (a := a + (mem.byte (p + j)).toNat) (by omega)
    have hadd1 := iadd_ofNat (p + j + 1) 1
    wasm_cstepu [extBody, hc, zero_eq]
    · wasm_within [extBody]
    iterate 3 (wasm_cstepu [extBody, List.getElem?_set, List.length_set, hlenf, h3, h4, hq]
               · wasm_within [extBody])
    wasm_cstepu [extBody, hm', hmem, hpj, hblt, read_one, PackSize.bits, packedVal, Nat.add_zero]
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
      refine Until.done (Or.inr (Or.inr ⟨j,
        ⟨(((f.locals.set 4 (vI a)).set 3 (vI (p + j + 1))).set 20
        (vI (mem.byte (p + j)).toNat)).set 4 (vI (a + (mem.byte (p + j)).toNat)), f.inst⟩,
        hi.ff, hle, hi.sums, by rw [hps]; exact ho, ⟨hi.inst, by simp [hlenf], ?_⟩,
        by simp only [Context.fill]⟩))
      have hother := hi.others
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · locals_at [hi.l16, hl17, hi.l18, hl19, hi.l20, hlenf, h3, h4, h20, hother, hps,
          ha_def, run_zero]
      · have hj0' := Nat.pos_iff_ne_zero.mp hj0
        have h1 := hpsr hj0
        locals_at [hi.l16, hl17, hi.l18, hl19, hi.l20, hlenf, h3, h4, h20, hother, hps, hj0',
          h1]
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
        have hother := hi.others
        have hinv : Inv ls inst p lim acc (fun i => mem.byte (p + i)) (j + 1)
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
            l19 := by simp [hlenf, h19, run_succ, ha_def]
            l16 := by
              rw [show p + (j + 1) = p + j + 1 by omega]
              simp [hlenf, h16]
            l17 := by simp [hlenf, h17, run_succ, ha_def]
            l20 := by simp [hlenf, h20]
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
        refine Until.done (Or.inl ⟨j, _, hi.ff, hff, hle, fun i hi' => by
            rcases Nat.lt_or_ge i j with h | h
            · exact hi.sums i h
            · obtain rfl : i = j := by omega
              rw [hps]; omega, ?_, rfl⟩)
        refine (show LocalsAt _ _ ⟨(((((((f.locals.set 4 (vI a)).set 3 (vI (p + j + 1))).set 20
          (vI (mem.byte (p + j)).toNat)).set 4 (vI (a + (mem.byte (p + j)).toNat))).set 18
          (vI (p + j + 1 + 1))).set 19 (vI (a + (mem.byte (p + j)).toNat))).set 16
          (vI (p + j + 1))).set 17 (vI (a + (mem.byte (p + j)).toNat)), f.inst⟩ _ from
          ⟨hi.inst, by simp [hlenf], ?_⟩)
        have hother := hi.others
        have h2 : p + j + 1 + 1 = p + j + 2 := by omega
        locals_at [hlenf, h3, h4, h16, h17, h18, h19, h20, hother, h2, hps]

/-- Every `-O1` iteration, by induction on the bytes left before `lim`. -/
theorem iter (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (p lim acc : Nat)
    (h14 : ls[14]? = some (vI lim)) (hm : inst.mems[0]? = some ma)
    (hmem : s.mems[ma]? = some mem) (hlim : lim + 1 < 2 ^ 32) (hsize : lim ≤ mem.size)
    (h20 : 20 < ls.length) (hacc : acc < 2 ^ 31) :
    ∀ n j f, lim - (p + j) = n → Inv ls inst p lim acc (fun i => mem.byte (p + i)) j f →
    Until H (Within (fun m x => m = ma ∧ p ≤ x ∧ x < lim) (fun _ _ => False))
      (ExtExit C s inst ls p lim acc (fun i => mem.byte (p + i))) (head C s f) := by
  intro n
  induction n with
  | zero =>
    intro j f hn hi
    exact one_iter H C s inst ls ma mem p lim acc j f h14 hm hmem hlim hsize h20 hacc hi
      (fun hle => absurd hle (by have := hi.bound; omega))
  | succ n ih =>
    intro j f hn hi
    exact one_iter H C s inst ls ma mem p lim acc j f h14 hm hmem hlim hsize h20 hacc hi
      (fun _ f' hi' => ih (j + 1) f' (by omega) hi')

/-- `ExtL1` for the `-O1` loop, route D. -/
theorem ext_l1 : ExtL1O1 := by
  intro H C s inst ls ma mem p lim acc h18 h14 h19 h20 hm hmem hpl hlim hsize hacc
  have hinv : Inv ls inst p lim acc (fun i => mem.byte (p + i)) 0 ⟨ls, inst⟩ :=
    { inst := rfl, len := rfl, others := fun _ _ _ _ _ _ _ _ => rfl, l18 := by simpa using h18,
      l19 := by simpa [run_zero] using h19, l16 := by simp, l17 := by simp, l20 := by simp,
      ff := fun _ h => absurd h (Nat.not_lt_zero _), sums := fun _ h => absurd h (by omega),
      bound := by omega }
  rw [extLoop_eq]
  simp only [ctx, Context.fill]
  wasm_cstepu [extBody]
  · wasm_within [extBody]
  simpa only [head, ctx, Context.fill, extBody, List.map_cons, List.map_nil] using
    iter H C s inst ls ma mem p lim acc h14 hm hmem hlim hsize h20 hacc _ 0 _ rfl hinv

end Subjects.Lz4C.O1.Direct
