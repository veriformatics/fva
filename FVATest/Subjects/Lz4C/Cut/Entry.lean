import FVATest.Subjects.Lz4C.Cut.ErrRet
import FVATest.Subjects.Lz4C.ExtCommon

/-! `Entry` (`Seg.lean`) by stepping, in segments joined by `Until.trans` — one proof term per
segment keeps the kernel's recursion shallow (≈ 70 steps in one term exceed it): the invocation,
the null and negative-capacity guards, the zero-capacity block, the empty-input guard, the end
pointers and limits (two halves), blocks `@2 … @4` (proof support; outside the review surface). -/

namespace Subjects.Lz4C.Cut

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.Lz4C

set_option maxRecDepth 100000

/-- Block `@2` of the entry code: the zero-capacity case. -/
def zeroCap : List Instr := [.localGet 3, .brIf 0, .localGet 2, .iconst .w32 1, .irelop .w32 .ne,
  .brIf 1, .iconst .w32 4294967295, .iconst .w32 0, .localGet 0, .loadPacked .w32 .p8 .u ⟨0, 0⟩,
  .select none, .return_]

/-- The null-source and negative-capacity guards. -/
def codeA : List Instr := [.localGet 0, .itestEqz .w32, .brIf 0, .localGet 3, .iconst .w32 0,
  .irelop .w32 (.lt .s), .brIf 0]

/-- The empty-input guard. -/
def codeB : List Instr := [.localGet 2, .itestEqz .w32, .brIf 0]

/-- The end pointers and limits, first half: locals 5 … 10. -/
def codeC1 : List Instr := [.localGet 1, .localGet 3, .ibinop .w32 .add, .localTee 5,
  .iconst .w32 4294967264, .ibinop .w32 .add, .localSet 6, .localGet 0, .localGet 2,
  .ibinop .w32 .add, .localTee 7, .iconst .w32 4294967280, .ibinop .w32 .add, .localSet 8,
  .localGet 5, .iconst .w32 4294967291, .ibinop .w32 .add, .localSet 9, .localGet 5,
  .iconst .w32 4294967289, .ibinop .w32 .add, .localSet 10]

/-- Second half: locals 11 … 14, then `ip = src` (local 4), `op = dst` (local 3). -/
def codeC2 : List Instr := [.localGet 7, .iconst .w32 4294967292, .ibinop .w32 .add, .localSet 11,
  .localGet 7, .iconst .w32 4294967288, .ibinop .w32 .add, .localSet 12, .localGet 5,
  .iconst .w32 4294967284, .ibinop .w32 .add, .localSet 13, .localGet 7, .iconst .w32 4294967281,
  .ibinop .w32 .add, .localSet 14, .localGet 0, .localSet 4, .localGet 1, .localSet 3]

theorem body1_eq : body1 = codeA ++ .block .empty zeroCap :: codeB ++ codeC1 ++ codeC2 ++
    .block .empty body2 :: epi := by kernel_rfl
theorem func2_body : Lifted.func2.body =
    [.iconst .w32 4294967295, .localSet 4, .block .empty body1, .localGet 4] := by kernel_rfl
theorem func2_locals : Lifted.func2.locals = [(15, .num .i32)] := by kernel_rfl
theorem body2_eq : body2 = .block .empty body3 :: body2.drop 1 := by kernel_rfl
theorem body3_eq : body3 = .block .empty body4 :: body3.drop 1 := by kernel_rfl
theorem body4_eq : body4 = [mainLoop] := by kernel_rfl

-- A failed `rfl` would otherwise unfold the slices into the 8 KiB module (memory without bound).
attribute [local irreducible] body1 body2 body3 body4 mainLoop

/-- Block `@1`'s code `es` running with locals `ls` (func 2 invoked from outside). -/
noncomputable abbrev at1 (st : Store) (inst : ModuleInst) (ls : List Val) (es : List Instr) :
    Config :=
  (ctx1 F0).fill ⟨st, ⟨ls, inst⟩, es.map .plain⟩

/-- The locals once `local 4 ← −1` ran: the arguments, then zeros. -/
def ls0 (src dst n cap : Nat) : List Val :=
  [vI src, vI dst, vI n, vI cap, .i32 4294967295#32, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

/-- After `codeC1`. -/
def ls1 (src dst n cap : Nat) : List Val :=
  [vI src, vI dst, vI n, vI cap, .i32 4294967295#32, vI (dst + cap), vI (dst + cap - 32),
    vI (src + n), vI (src + n - 16), vI (dst + cap - 5), vI (dst + cap - 7), .i32 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

/-- After `codeC2`: the main loop's locals. -/
def ls2 (src dst n cap : Nat) : List Val :=
  [vI src, vI dst, vI n, vI dst, vI src, vI (dst + cap), vI (dst + cap - 32), vI (src + n),
    vI (src + n - 16), vI (dst + cap - 5), vI (dst + cap - 7), vI (src + n - 4), vI (src + n - 8),
    vI (dst + cap - 12), vI (src + n - 15), .i32 0, .i32 0, .i32 0, .i32 0]

/-- `Entry`'s exits. -/
def EntryQ (st : Store) (inst : ModuleInst) (mem : MemInst) (src dst n cap : Nat) (c : Config) :
    Prop :=
  ((src = 0 ∨ 2 ^ 31 ≤ cap ∨ (cap = 0 ∧ n ≠ 1) ∨ (cap ≠ 0 ∧ n = 0)) ∧
      c = ⟨st, ⟨[], {}⟩, vals [vNeg1]⟩) ∨
    (src ≠ 0 ∧ cap = 0 ∧ n = 1 ∧ c = ⟨st, ⟨[], {}⟩,
      vals [if mem.byte src = 0 then vI 0 else vNeg1]⟩) ∨
    (src ≠ 0 ∧ cap < 2 ^ 31 ∧ cap ≠ 0 ∧ n ≠ 0 ∧ ∃ ls, HeadLocals ls src dst n cap dst src ∧
      c = (ctx4 (ctx2 F0)).fill ⟨st, ⟨ls, inst⟩, [.plain mainLoop]⟩)

variable {H : HostSem} {st : Store} {inst : ModuleInst} {ma : Nat} {mem : MemInst}
  {src dst n cap : Nat}

/-- From block `@1`'s end, func 2 returns local 4. -/
theorem ret_local4 {R W : Nat → Nat → Prop} {Q : Config → Prop} {ls : List Val} {v : Val}
    (h4 : ls[4]? = some v) (hq : Q ⟨st, ⟨[], {}⟩, vals [v]⟩) :
    Until H (Within R W) Q (F0.fill ⟨st, ⟨ls, inst⟩, (Lifted.func2.body.drop 3).map .plain⟩) := by
  rw [fn_tail]
  wasm_cstepu [h4]
  · wasm_within []
  rw [F0, fnCtx, Context.fill.eq_2]
  wasm_cstepu []
  · wasm_within []
  rw [Context.fill.eq_3]
  wasm_cstepu []
  · wasm_within []
  exact Until.done hq

/-- The invocation: func 2's frame and label, `local 4 ← −1`, block `@1` entered. -/
theorem entry_open {a : Nat} (hfa : st.funcs[a]? = some (.wasm decType inst Lifted.func2)) :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => c = at1 st inst (ls0 src dst n cap) body1)
      (invokeConfig st a [vI src, vI dst, vI n, vI cap]) := by
  show Until H _ _ (Context.hole.fill (invokeConfig st a [vI src, vI dst, vI n, vI cap]))
  unfold invokeConfig
  wasm_cstepu [hfa, func2_locals, func2_body, decType]
  · wasm_within [hfa]
  change Until H _ _ (F0.fill ⟨st, _, _⟩)
  iterate 2 (wasm_cstepu []; · wasm_within [])
  rw [show [AInstr.plain (Instr.localGet 4)] = (Lifted.func2.body.drop 3).map .plain by
    rw [fn_tail]; rfl]
  exact Until.done rfl

/-- The null-source guard (never taken: `16 ≤ src`), the negative-capacity guard (−1). -/
theorem entry_guards (hs : 16 ≤ src) (hdc : dst + cap < 2 ^ 32) (hsn : src + n < 2 ^ 32) :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => EntryQ st inst mem src dst n cap c ∨ (cap < 2147483648 ∧
        c = at1 st inst (ls0 src dst n cap) (.block .empty zeroCap :: codeB ++ codeC1 ++ codeC2 ++
          .block .empty body2 :: epi)))
      (at1 st inst (ls0 src dst n cap) body1) := by
  have hz : ieqz (BitVec.ofNat 32 src) = 0 := by
    simp only [ieqz, ofNat32_toNat (show src < 2 ^ 32 by omega)]
    rw [show (src == 0) = false by simp; omega]; rfl
  have hlt := iltS_zero (a := cap) (by omega)
  show Until H _ _ ((ctx1 F0).fill ⟨st, ⟨_, inst⟩, _⟩)
  rw [body1_eq]
  iterate 2 (wasm_cstepu [codeA, ls0, hz, zero_eq]; · wasm_within [codeA])
  by_cases hcn : 2147483648 ≤ cap
  · -- `cap` negative as an `i32`: −1
    have hc : Num.bool (decide (2147483648 ≤ cap)) = 1 := by simp [hcn, bool_true]
    repeat (wasm_cstepu [codeA, ls0, hlt, hc, one_ne, zero_eq]
            · wasm_within [codeA])
    rw [ctx1, Context.fill.eq_2]
    wasm_cstepu []
    · wasm_within []
    exact ret_local4 rfl (Or.inl (Or.inl ⟨Or.inr (Or.inl (by omega)), rfl⟩))
  have hc : Num.bool (decide (2147483648 ≤ cap)) = 0 := by simp [hcn, bool_false]
  iterate 4 (wasm_cstepu [codeA, ls0, hlt, hc, zero_eq]; · wasm_within [codeA])
  exact Until.done (Or.inr ⟨by omega, rfl⟩)

/-- The zero-capacity block: `0`/−1 for one byte (reading `src[0]`), −1 otherwise; with room,
the code after the block. -/
theorem entry_zero (hm0 : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hs : 16 ≤ src) (hdc : dst + cap < 2 ^ 32) (hsn : src + n < 2 ^ 32)
    (h1 : n = 1 → src < mem.size) (hcn : cap < 2147483648) :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => EntryQ st inst mem src dst n cap c ∨ (cap ≠ 0 ∧
        c = at1 st inst (ls0 src dst n cap) (codeB ++ codeC1 ++ codeC2 ++
          .block .empty body2 :: epi)))
      (at1 st inst (ls0 src dst n cap) (.block .empty zeroCap :: codeB ++ codeC1 ++ codeC2 ++
          .block .empty body2 :: epi)) := by
  show Until H _ _ ((ctx1 F0).fill ⟨st, ⟨_, inst⟩, _⟩)
  iterate 2 (wasm_cstepu [zeroCap, ls0]; · wasm_within [zeroCap])
  by_cases hc0 : cap = 0
  · subst hc0
    have hne := ine_ofNat (a := n) (b := 1) (by omega) (by omega)
    by_cases hn1 : n = 1
    · -- no room, one byte: `0` for the block `0`, else −1
      subst hn1
      have hb0 : Num.bool ((1 : Nat) != 1) = 0 := rfl
      have hsrc : (BitVec.ofNat 32 src).toNat = src := ofNat32_toNat (by omega)
      have hblt : decide (mem.size < src + 1) = false := by simp; have := h1 rfl; omega
      repeat (wasm_cstepu [zeroCap, hne, hb0, ofNat_zero_eq, zero_eq, bool_false]
              · wasm_within [zeroCap])
      wasm_cstepu [hm0, hmem, hsrc, hblt, mem_read_one, PackSize.bits, packedVal, Nat.add_zero]
      · wasm_within [hm0, hmem, hsrc, hblt, PackSize.bits, Nat.add_zero]
        exact ⟨fun x h₁ h₂ => ⟨rfl, by omega, by omega⟩, by simp⟩
      by_cases hb : mem.byte src = 0
      · have hsel : decide (BitVec.ofNat 32 (mem.byte src).toNat = 0) = true := by rw [hb]; decide
        repeat (wasm_cstepu [hsel]
                · wasm_within [])
        rw [ctx1, Context.fill.eq_2, F0, fnCtx, Context.fill.eq_2, Context.fill.eq_3]
        repeat (wasm_cstepu []
                · wasm_within [])
        exact Until.done (Or.inl (Or.inr (Or.inl ⟨by omega, rfl, rfl,
          by rw [ite_eq_left hb]; rfl⟩)))
      · have hsel := ofNat_ne_zero (k := (mem.byte src).toNat)
          (fun h => hb (UInt8.toNat_inj.mp (by rw [h]; rfl)))
          (by have := (mem.byte src).toNat_lt; omega)
        repeat (wasm_cstepu [hsel]
                · wasm_within [])
        rw [ctx1, Context.fill.eq_2, F0, fnCtx, Context.fill.eq_2, Context.fill.eq_3]
        repeat (wasm_cstepu []
                · wasm_within [])
        exact Until.done (Or.inl (Or.inr (Or.inl ⟨by omega, rfl, rfl,
          by rw [ite_eq_right hb]; rfl⟩)))
    · -- no room, more than one byte: −1
      have hb1 : Num.bool (n != 1) = 1 := by rw [show (n != 1) = true by simp [hn1]]; rfl
      repeat (wasm_cstepu [zeroCap, hne, hb1, one_ne, ofNat_zero_eq]
              · wasm_within [zeroCap])
      rw [ctx1, Context.fill.eq_2]
      wasm_cstepu []
      · wasm_within []
      exact ret_local4 rfl (Or.inl (Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨rfl, hn1⟩)), rfl⟩))
  · have hcz := ofNat_ne_zero hc0 (show cap < 2 ^ 32 by omega)
    iterate 2 (wasm_cstepu [zeroCap, hcz]; · wasm_within [zeroCap])
    exact Until.done (Or.inr ⟨hc0, rfl⟩)

/-- The empty-input guard: −1 for `n = 0`. -/
theorem entry_n (hs : 16 ≤ src) (hsn : src + n < 2 ^ 32) (hc0 : cap ≠ 0) :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => EntryQ st inst mem src dst n cap c ∨ (n ≠ 0 ∧
        c = at1 st inst (ls0 src dst n cap) (codeC1 ++ codeC2 ++ .block .empty body2 :: epi)))
      (at1 st inst (ls0 src dst n cap) (codeB ++ codeC1 ++ codeC2 ++
          .block .empty body2 :: epi)) := by
  have hz2 : ieqz (BitVec.ofNat 32 n) = Num.bool (n == 0) := by
    simp only [ieqz, ofNat32_toNat (show n < 2 ^ 32 by omega)]
  show Until H _ _ ((ctx1 F0).fill ⟨st, ⟨_, inst⟩, _⟩)
  by_cases hn0 : n = 0
  · subst hn0
    repeat (wasm_cstepu [codeB, ls0, hz2, bool_true, one_ne]
            · wasm_within [codeB])
    rw [ctx1, Context.fill.eq_2]
    wasm_cstepu []
    · wasm_within []
    exact ret_local4 rfl (Or.inl (Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨hc0, rfl⟩)), rfl⟩))
  have hn0' : decide (n = 0) = false := by simp [hn0]
  iterate 3 (wasm_cstepu [codeB, ls0, hz2, hn0', bool_false, zero_eq]
             · wasm_within [codeB])
  exact Until.done (Or.inr ⟨hn0, rfl⟩)

/-- The end pointers and limits, first half. -/
theorem entry_c1 (hd : 32 ≤ dst) (hs : 16 ≤ src) :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => c = at1 st inst (ls1 src dst n cap) (codeC2 ++ .block .empty body2 :: epi))
      (at1 st inst (ls0 src dst n cap) (codeC1 ++ codeC2 ++ .block .empty body2 :: epi)) := by
  have h6 := iadd_neg (x := dst + cap) (c := 4294967264) (k := 32) rfl (by omega)
  have h8 := iadd_neg (x := src + n) (c := 4294967280) (k := 16) rfl (by omega)
  have h9 := iadd_neg (x := dst + cap) (c := 4294967291) (k := 5) rfl (by omega)
  have h10 := iadd_neg (x := dst + cap) (c := 4294967289) (k := 7) rfl (by omega)
  show Until H _ _ ((ctx1 F0).fill ⟨st, ⟨_, inst⟩, _⟩)
  repeat (wasm_cstepu [codeC1, ls0, h6, h8, h9, h10, add32]
          · wasm_within [codeC1])
  exact Until.done rfl

/-- Second half: the main loop's locals, block `@2` entered. -/
theorem entry_c2 (hd : 32 ≤ dst) (hs : 16 ≤ src) :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => c = (ctx1 F0).fill ⟨st, ⟨ls2 src dst n cap, inst⟩,
        .label 0 [] (body2.map .plain) :: epi.map .plain⟩)
      (at1 st inst (ls1 src dst n cap) (codeC2 ++ .block .empty body2 :: epi)) := by
  have h11 := iadd_neg (x := src + n) (c := 4294967292) (k := 4) rfl (by omega)
  have h12 := iadd_neg (x := src + n) (c := 4294967288) (k := 8) rfl (by omega)
  have h13 := iadd_neg (x := dst + cap) (c := 4294967284) (k := 12) rfl (by omega)
  have h14 := iadd_neg (x := src + n) (c := 4294967281) (k := 15) rfl (by omega)
  show Until H _ _ ((ctx1 F0).fill ⟨st, ⟨_, inst⟩, _⟩)
  repeat (wasm_cstepu [codeC2, ls1, h11, h12, h13, h14]
          · wasm_within [codeC2])
  exact Until.done rfl

/-- Blocks `@3`, `@4`: the main loop's head. -/
theorem entry_blocks :
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => c = (ctx4 (ctx2 F0)).fill ⟨st, ⟨ls2 src dst n cap, inst⟩, [.plain mainLoop]⟩)
      ((ctx1 F0).fill ⟨st, ⟨ls2 src dst n cap, inst⟩,
        .label 0 [] (body2.map .plain) :: epi.map .plain⟩) := by
  rw [← epi_eq]
  change Until H _ _ ((ctx2 F0).fill ⟨st, ⟨ls2 src dst n cap, inst⟩, body2.map .plain⟩)
  rw [body2_eq]
  wasm_cstepu []
  · wasm_within []
  rw [body3_eq]
  wasm_cstepu []
  · wasm_within []
  rw [body4_eq]
  exact Until.done rfl

theorem headLocals_ls2 : HeadLocals (ls2 src dst n cap) src dst n cap dst src :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem entry : Entry := by
  intro H st inst a ma mem src dst n cap hfa hm0 hmem hd hs hdc hsn h1
  refine Until.trans (entry_open (src := src) (n := n) hfa) ?_
  rintro _ rfl
  refine Until.trans (entry_guards (dst := dst) (mem := mem) hs hdc hsn) ?_
  rintro c (hq | ⟨hcn, rfl⟩)
  · exact Until.done hq
  refine Until.trans (entry_zero hm0 hmem hs hdc hsn h1 hcn) ?_
  rintro c (hq | ⟨hc0, rfl⟩)
  · exact Until.done hq
  refine Until.trans (entry_n (dst := dst) (mem := mem) hs hsn hc0) ?_
  rintro c (hq | ⟨hn0, rfl⟩)
  · exact Until.done hq
  refine Until.trans (entry_c1 hd hs) ?_
  rintro _ rfl
  refine Until.trans (entry_c2 hd hs) ?_
  rintro _ rfl
  refine Until.trans entry_blocks ?_
  rintro _ rfl
  exact Until.done (Or.inr (Or.inr ⟨by omega, by omega, hc0, hn0, _, headLocals_ls2, rfl⟩))

end Subjects.Lz4C.Cut
