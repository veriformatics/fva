import FVA.Proof.Valid.ProgressBase

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

private theorem one {s : Store} {vs : List Val} {t : OpType}
    (h : List.Forall₂ (HasOpType s) vs [t]) : ∃ v, vs = [v] ∧ HasOpType s v t := by
  cases h with | cons hv hs => cases hs; exact ⟨_, rfl, hv⟩

private theorem two {s : Store} {vs : List Val} {t u : OpType}
    (h : List.Forall₂ (HasOpType s) vs [t, u]) :
    ∃ v w, vs = [v, w] ∧ HasOpType s v t ∧ HasOpType s w u := by
  cases h with | cons hv hs =>
    cases hs with | cons hw hs => cases hs; exact ⟨_, _, rfl, hv, hw⟩

private theorem three {s : Store} {vs : List Val} {t u w : OpType}
    (h : List.Forall₂ (HasOpType s) vs [t, u, w]) :
    ∃ v₁ v₂ v₃, vs = [v₁, v₂, v₃] ∧ HasOpType s v₁ t ∧ HasOpType s v₂ u ∧
      HasOpType s v₃ w := by
  cases h with | cons h₁ hs =>
    cases hs with | cons h₂ hs =>
      cases hs with | cons h₃ hs => cases hs; exact ⟨_, _, _, rfl, h₁, h₂, h₃⟩

private theorem one_i32 {s : Store} {vs : List Val}
    (h : List.Forall₂ (HasOpType s) vs [i32]) : ∃ v, vs = [.i32 v] := by
  obtain ⟨v, rfl, hv⟩ := one h
  obtain ⟨b, rfl⟩ := hasOp_i32.mp hv
  exact ⟨b, rfl⟩

private theorem three_i32 {s : Store} {vs : List Val}
    (h : List.Forall₂ (HasOpType s) vs [i32, i32, i32]) :
    ∃ d src n, vs = [.i32 d, .i32 src, .i32 n] := by
  obtain ⟨d, src, n, rfl, hd, hs, hn⟩ := three h
  obtain ⟨d, rfl⟩ := hasOp_i32.mp hd
  obtain ⟨src, rfl⟩ := hasOp_i32.mp hs
  obtain ⟨n, rfl⟩ := hasOp_i32.mp hn
  exact ⟨d, src, n, rfl⟩

private theorem ref_of_type {s : Store} {v : Val} {rt : RefType}
    (h : HasOpType s v (.val (.ref rt))) : ∃ r, v = .ref r := by
  cases v <;> simp_all [HasOpType, Val.HasType]

private theorem bits_of_type {s : Store} {v : Val} {t : NumType}
    (h : HasOpType s v (.val (.num t))) : ∃ n, v.numBits t = some n := by
  cases t <;> cases v <;> simp_all [HasOpType, Val.HasType, Val.numBits]

private theorem intBits_of_type {s : Store} {v : Val} {w : Width}
    (h : HasOpType s v (int w)) : ∃ n, v.intBits w = some n := by
  cases w with
  | w32 => obtain ⟨v, rfl⟩ := hasOp_i32.mp h; exact ⟨_, rfl⟩
  | w64 => obtain ⟨v, rfl⟩ := hasOp_i64.mp h; exact ⟨_, rfl⟩

private theorem zero_or_pos (n : BitVec 32) : n = 0 ∨ 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with hz | hp
  · exact .inl (BitVec.eq_of_toNat_eq hz)
  · exact .inr hp

set_option maxHeartbeats 2000000 in
theorem instr_progress {H : HostSem} {s : Store} {f : Frame} {C : Context}
    {i : Instr} {st : StackType} {args : List Val} (hi : InstrT C i st)
    (hf : FrameCtx s f C) (hargs : List.Forall₂ (HasOpType s) args st.ins) :
    FragmentProgress H s f C (vals args ++ [.plain i]) := by
  classical
  by_cases hn : Numeric i
  · obtain ⟨r, hr⟩ := numResults_nonempty hi hn hargs
    exact .step (.num hr)
  cases hi <;> simp only [Numeric, not_true_eq_false] at hn
  case iconst w n h =>
    cases hargs
    cases w with
    | w32 => exact .values [.i32 (BitVec.ofNatLT n h)]
    | w64 => exact .values [.i64 (BitVec.ofNatLT n h)]
  case fconst w n h =>
    cases hargs
    cases w with
    | w32 => exact .values [.f32 (BitVec.ofNatLT n h)]
    | w64 => exact .values [.f64 (BitVec.ofNatLT n h)]
  case refNull rt => cases hargs; exact .values [.ref (.null rt)]
  case refIsNull rt =>
    obtain ⟨v, rfl, hv⟩ := one hargs
    obtain ⟨r, rfl⟩ := ref_of_type hv
    exact .step .refIsNull
  case refFunc x ft hx hr =>
    cases hargs
    obtain ⟨addr, fi, ha, _, _⟩ := hf.funcs hx
    exact .step (.refFunc ha)
  case drop t => obtain ⟨v, rfl, _⟩ := one hargs; exact .step .drop
  case select t ht | selectT t =>
    obtain ⟨v₁, v₂, v₃, rfl, _, _, h₃⟩ := three hargs
    obtain ⟨c, rfl⟩ := hasOp_i32.mp h₃
    exact .step .select
  case localGet x t hx =>
    cases hargs
    obtain ⟨v, hv, _⟩ := hf.locals hx
    exact .step (.localGet hv)
  case localSet x t hx =>
    obtain ⟨v, rfl, _⟩ := one hargs
    obtain ⟨v', hv, _⟩ := hf.locals hx
    exact .step (.localSet (List.getElem?_eq_some_iff.mp hv).1)
  case localTee x t hx => obtain ⟨v, rfl, _⟩ := one hargs; exact .step .localTee
  case globalGet x gt hx =>
    cases hargs
    obtain ⟨addr, g, ha, hg, _⟩ := hf.globals hx
    exact .step (.globalGet ha hg)
  case globalSet x t hx =>
    obtain ⟨v, rfl, _⟩ := one hargs
    obtain ⟨addr, g, ha, hg, _⟩ := hf.globals hx
    exact .step (.globalSet ha hg)
  case tableGet x tt hx =>
    obtain ⟨i, rfl⟩ := one_i32 hargs
    obtain ⟨addr, ti, ha, hti, _⟩ := hf.tables hx
    cases hr : ti.elem[i.toNat]? with
    | some r => exact .step (.tableGet ha hti hr)
    | none => exact .step (.tableGetTrap ha hti (List.getElem?_eq_none_iff.mp hr))
  case tableSet x tt hx =>
    obtain ⟨v, w, rfl, hv, hw⟩ := two hargs
    obtain ⟨i, rfl⟩ := hasOp_i32.mp hv
    obtain ⟨r, rfl⟩ := ref_of_type hw
    obtain ⟨addr, ti, ha, hti, _⟩ := hf.tables hx
    by_cases hb : i.toNat < ti.elem.length
    · exact .step (.tableSet ha hti hb)
    · exact .step (.tableSetTrap ha hti (Nat.le_of_not_gt hb))
  case tableSize x tt hx =>
    cases hargs
    obtain ⟨addr, ti, ha, hti, _⟩ := hf.tables hx
    exact .step (.tableSize ha hti)
  case tableGrow x tt hx =>
    obtain ⟨v, w, rfl, hv, hw⟩ := two hargs
    obtain ⟨r, rfl⟩ := ref_of_type hv
    obtain ⟨n, rfl⟩ := hasOp_i32.mp hw
    exact .step .tableGrowFail
  case tableFill x tt hx =>
    obtain ⟨v₁, v₂, v₃, rfl, h₁, h₂, h₃⟩ := three hargs
    obtain ⟨i, rfl⟩ := hasOp_i32.mp h₁
    obtain ⟨r, rfl⟩ := ref_of_type h₂
    obtain ⟨n, rfl⟩ := hasOp_i32.mp h₃
    obtain ⟨addr, ti, ha, hti, _⟩ := hf.tables hx
    by_cases hb : i.toNat + n.toNat ≤ ti.elem.length
    · rcases zero_or_pos n with rfl | hp
      · exact .step (.tableFillZero ha hti (by simpa
          using hb))
      · exact .step (.tableFill ha hti hp hb)
    · exact .step (.tableFillTrap ha hti (Nat.lt_of_not_ge hb))
  case tableCopy x y tx ty he hx hy =>
    obtain ⟨d, src, n, rfl⟩ := three_i32 hargs
    obtain ⟨ax, Tx, hax, htx, _⟩ := hf.tables hx
    obtain ⟨ay, Ty, hay, hty, _⟩ := hf.tables hy
    by_cases hs : src.toNat + n.toNat ≤ Ty.elem.length
    · by_cases hd : d.toNat + n.toNat ≤ Tx.elem.length
      · rcases zero_or_pos n with rfl | hp
        · exact .step (.tableCopyZero hax hay htx hty
            (by simpa using hs)
            (by simpa using hd))
        · by_cases hc : d.toNat ≤ src.toNat
          · exact .step (.tableCopyUp hax hay htx hty hp hs hd hc)
          · exact .step (.tableCopyDown hax hay htx hty hp hs hd (Nat.lt_of_not_ge hc))
      · exact .step (.tableCopyTrap hax hay (.inr ⟨Tx, htx, Nat.lt_of_not_ge hd⟩))
    · exact .step (.tableCopyTrap hax hay (.inl ⟨Ty, hty, Nat.lt_of_not_ge hs⟩))
  case tableInit x y tt rt he hx hy =>
    obtain ⟨d, src, n, rfl⟩ := three_i32 hargs
    obtain ⟨ax, T, hax, htx, _⟩ := hf.tables hx
    obtain ⟨ay, E, hay, hey, _⟩ := hf.elems hy
    by_cases hs : src.toNat + n.toNat ≤ E.elem.length
    · by_cases hd : d.toNat + n.toNat ≤ T.elem.length
      · rcases zero_or_pos n with rfl | hp
        · exact .step (.tableInitZero hax hay htx hey
            (by simpa using hs)
            (by simpa using hd))
        · have hb : src.toNat < E.elem.length := by omega
          exact .step (.tableInit hax hay htx hey hp hs hd (List.getElem?_eq_getElem hb))
      · exact .step (.tableInitTrap hax hay (.inr ⟨T, htx, Nat.lt_of_not_ge hd⟩))
    · exact .step (.tableInitTrap hax hay (.inl ⟨E, hey, Nat.lt_of_not_ge hs⟩))
  case elemDrop x rt hx =>
    cases hargs
    obtain ⟨addr, ei, ha, hei, _⟩ := hf.elems hx
    exact .step (.elemDrop ha hei)
  case load t m lim ha hm =>
    obtain ⟨i, rfl⟩ := one_i32 hargs
    obtain ⟨addr, mem, hma, hmem, _⟩ := hf.mems hm
    by_cases hb : i.toNat + m.offset + t.bytes ≤ mem.size
    · exact .step (.load hma hmem hb)
    · exact .step (.loadTrap hma hmem (Nat.lt_of_not_ge hb))
  case loadPacked w p sx m lim hl ha hm =>
    obtain ⟨i, rfl⟩ := one_i32 hargs
    obtain ⟨addr, mem, hma, hmem, _⟩ := hf.mems hm
    by_cases hb : i.toNat + m.offset + p.bits / 8 ≤ mem.size
    · exact .step (.loadPacked hma hmem hb)
    · exact .step (.loadPackedTrap hma hmem (Nat.lt_of_not_ge hb))
  case store t m lim ha hm =>
    obtain ⟨v, w, rfl, hv, hw⟩ := two hargs
    obtain ⟨i, rfl⟩ := hasOp_i32.mp hv
    obtain ⟨n, hn⟩ := bits_of_type hw
    obtain ⟨addr, mem, hma, hmem, _⟩ := hf.mems hm
    by_cases hb : i.toNat + m.offset + t.bytes ≤ mem.size
    · exact .step (.store hma hmem hn hb)
    · exact .step (.storeTrap hma hmem hn (Nat.lt_of_not_ge hb))
  case storePacked w p m lim hl ha hm =>
    obtain ⟨v, val, rfl, hv, hw⟩ := two hargs
    obtain ⟨i, rfl⟩ := hasOp_i32.mp hv
    obtain ⟨n, hn⟩ := intBits_of_type hw
    obtain ⟨addr, mem, hma, hmem, _⟩ := hf.mems hm
    by_cases hb : i.toNat + m.offset + p.bits / 8 ≤ mem.size
    · exact .step (.storePacked hma hmem hn hb)
    · exact .step (.storePackedTrap hma hmem hn (Nat.lt_of_not_ge hb))
  case memorySize lim hm =>
    cases hargs
    obtain ⟨addr, mem, ha, hmem, _⟩ := hf.mems hm
    exact .step (.memorySize ha hmem)
  case memoryGrow lim hm =>
    obtain ⟨n, rfl⟩ := one_i32 hargs
    exact .step .memoryGrowFail
  case memoryFill lim hm =>
    obtain ⟨d, v, n, rfl⟩ := three_i32 hargs
    obtain ⟨addr, mem, ha, hmem, _⟩ := hf.mems hm
    by_cases hb : d.toNat + n.toNat ≤ mem.size
    · rcases zero_or_pos n with rfl | hp
      · exact .step (.memoryFillZero ha hmem
          (by simpa using hb))
      · exact .step (.memoryFill ha hmem hp hb)
    · exact .step (.memoryFillTrap ha hmem (Nat.lt_of_not_ge hb))
  case memoryCopy lim hm =>
    obtain ⟨d, src, n, rfl⟩ := three_i32 hargs
    obtain ⟨addr, mem, ha, hmem, _⟩ := hf.mems hm
    by_cases hs : src.toNat + n.toNat ≤ mem.size
    · by_cases hd : d.toNat + n.toNat ≤ mem.size
      · rcases zero_or_pos n with rfl | hp
        · exact .step (.memoryCopyZero ha hmem
            (by simpa using hs)
            (by simpa using hd))
        · by_cases hc : d.toNat ≤ src.toNat
          · exact .step (.memoryCopyUp ha hmem hp hs hd hc)
          · exact .step (.memoryCopyDown ha hmem hp hs hd (Nat.lt_of_not_ge hc))
      · exact .step (.memoryCopyTrap ha hmem (.inr (Nat.lt_of_not_ge hd)))
    · exact .step (.memoryCopyTrap ha hmem (.inl (Nat.lt_of_not_ge hs)))
  case memoryInit x lim hm hd =>
    obtain ⟨d, src, n, rfl⟩ := three_i32 hargs
    obtain ⟨ma, mem, hma, hmem, _⟩ := hf.mems hm
    obtain ⟨da, di, hda, hdi⟩ := hf.datas hd
    by_cases hs : src.toNat + n.toNat ≤ di.data.length
    · by_cases hd : d.toNat + n.toNat ≤ mem.size
      · rcases zero_or_pos n with rfl | hp
        · exact .step (.memoryInitZero hma hda hmem hdi
            (by simpa using hs)
            (by simpa using hd))
        · have hb : src.toNat < di.data.length := by omega
          exact .step (.memoryInit hma hda hmem hdi hp hs hd (List.getElem?_eq_getElem hb))
      · exact .step (.memoryInitTrap hma hda hmem (.inr (Nat.lt_of_not_ge hd)))
    · exact .step (.memoryInitTrap hma hda hmem (.inl ⟨di, hdi, Nat.lt_of_not_ge hs⟩))
  case dataDrop x hd =>
    cases hargs
    obtain ⟨da, di, hda, hdi⟩ := hf.datas hd
    exact .step (.dataDrop hda hdi)
  case nop => cases hargs; exact .step .nop
  case unreachable t₁ t₂ =>
    simpa only [List.append_nil] using FragmentProgress.step (C := C)
      (Step.seq (H := H) (s := s) (f := f) (vs := args) (rest := []) Step.unreachable)
  case block bt body ft hb hs =>
    exact .step (.block ((hf.blockType bt).symm.trans hb)
      (by simpa only [ops, List.length_map] using hargs.length_eq))
  case loop bt body ft hb hs =>
    exact .step (.loop ((hf.blockType bt).symm.trans hb)
      (by simpa only [ops, List.length_map] using hargs.length_eq))
  case if_ bt thn els ft hb ht he =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    obtain ⟨v, rfl⟩ := one_i32 hlast
    have hstep : FragmentProgress H s f C
        [(Val.i32 v).instr, .plain (.if_ bt thn els)] := by
      by_cases hv : v = 0
      · subst v; exact .step .ifFalse
      · exact .step (.ifTrue hv)
    simpa only [List.map_append, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append] using hstep.prepend pre
  case br l ts t₁ t₂ ht =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    have hl : args.length = ts.length := by
      simpa only [ops, List.length_map] using hlast.length_eq
    simpa only [BlockCtx.fill, List.map_append, List.append_assoc, List.append_nil,
      Nat.zero_add] using FragmentProgress.branch (H := H) (s := s) (f := f)
      (BlockCtx.base pre []) ht hl
  case brIf l ts ht =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    obtain ⟨v, rfl⟩ := one_i32 hlast
    have hstep : FragmentProgress H s f C [(Val.i32 v).instr, .plain (.brIf l)] := by
      by_cases hv : v = 0
      · subst v; exact .step .brIfFalse
      · exact .step (.brIfTrue hv)
    simpa only [List.map_append, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append] using hstep.prepend pre
  case brTable ls l ts t₁ t₂ ht =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    obtain ⟨v, rfl⟩ := one_i32 hlast
    have hstep : FragmentProgress H s f C [(Val.i32 v).instr, .plain (.brTable ls l)] :=
      .step .brTable
    simpa only [List.map_append, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append] using hstep.prepend pre
  case return_ ts t₁ t₂ ht =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    have hl : args.length = ts.length := by
      simpa only [ops, List.length_map] using hlast.length_eq
    simpa only [BlockCtx.fill, List.map_append, List.append_assoc, List.append_nil] using
      FragmentProgress.return_ (H := H) (s := s) (f := f) (BlockCtx.base pre []) ht hl
  case call x ft hx =>
    obtain ⟨addr, fi, ha, _, _⟩ := hf.funcs hx
    simpa only [List.append_nil] using FragmentProgress.step (C := C)
      (Step.seq (H := H) (s := s) (f := f) (vs := args) (rest := []) (Step.call ha))
  case callIndirect x y tt ft hx he hy =>
    obtain ⟨pre, args, rfl, _, hlast⟩ := typed_split hargs
    obtain ⟨v, rfl⟩ := one_i32 hlast
    have hstep : FragmentProgress H s f C [(Val.i32 v).instr, .plain (.callIndirect x y)] := by
      by_cases ht : ∃ addr, CallTarget s f x y v addr
      · obtain ⟨addr, ht⟩ := ht; exact .step (.callIndirect ht)
      · exact .step (.callIndirectTrap (by simpa only [not_exists] using ht))
    simpa only [List.map_append, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append] using hstep.prepend pre

end FVA.Wasm.Valid
