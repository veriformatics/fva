import FVA.Proof.Valid.Redex

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem FrameCtx.tableType {s : Store} {f : Frame} {C : Context} (hf : FrameCtx s f C)
    {x addr : Nat} {tt : TableType} {ti : TableInst} (hx : C.tables[x]? = some tt)
    (ha : f.inst.tables[x]? = some addr) (hti : s.tables[addr]? = some ti) : ti.type = tt := by
  obtain ⟨a', ti', ha', hti', ht⟩ := hf.tables hx
  have heqa := Option.some.inj (ha'.symm.trans ha)
  subst a'
  have heqt := Option.some.inj (hti'.symm.trans hti)
  subst ti'
  exact ht

theorem FrameCtx.elemType {s : Store} {f : Frame} {C : Context} (hf : FrameCtx s f C)
    {x addr : Nat} {rt : RefType} {ei : ElemInst} (hx : C.elems[x]? = some rt)
    (ha : f.inst.elems[x]? = some addr) (hei : s.elems[addr]? = some ei) : ei.type = rt := by
  obtain ⟨a', ei', ha', hei', ht⟩ := hf.elems hx
  have heqa := Option.some.inj (ha'.symm.trans ha)
  subst a'
  have heqe := Option.some.inj (hei'.symm.trans hei)
  subst ei'
  exact ht

theorem ASeqT.tableGet {s : Store} {f : Frame} {C : Context} {x addr : Nat} {ti : TableInst}
    {i : BitVec 32} {r : Ref} {a b : List OpType} (hok : StoreOK s) (hf : FrameCtx s f C)
    (h : ASeqT s C [(Val.i32 i).instr, .plain (.tableGet x)] ⟨a, b⟩)
    (ha : f.inst.tables[x]? = some addr) (hti : s.tables[addr]? = some ti)
    (hr : ti.elem[i.toNat]? = some r) : ASeqT s C [(Val.ref r).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | tableGet hx =>
        have ht := hf.tableType hx ha hti
        have hv := (hok.tables ti (List.mem_of_getElem? hti)).2.2 r (List.mem_of_getElem? hr)
        exact .single (.value (by simpa only [ht] using hv))

theorem ASeqT.tableSet {s : Store} {f : Frame} {C : Context} {x addr : Nat} {ti : TableInst}
    {i : BitVec 32} {r : Ref} {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [(Val.i32 i).instr, (Val.ref r).instr, .plain (.tableSet x)] ⟨a, b⟩)
    (ha : f.inst.tables[x]? = some addr) (hti : s.tables[addr]? = some ti) :
    Val.HasType s (.ref r) (.ref ti.type.elem) ∧ Matches a b := by
  obtain ⟨p, ts, out, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (vs := [.i32 i, .ref r]) (by
    intro x y hi
    cases hi with | plain hi => cases hi; rfl)
  cases hi with | plain hi =>
    cases hi with | tableSet hx =>
      cases hvs with | cons _ hs =>
        cases hs with | cons hv hs =>
          exact ⟨by simpa only [hf.tableType hx ha hti, HasOpType] using hv,
            hp.trans (by simpa using hout)⟩

theorem ASeqT.tableSize {s : Store} {C : Context} {x : Nat} {a b : List OpType}
    (h : ASeqT s C [.plain (.tableSize x)] ⟨a, b⟩) (n : Nat) :
    ASeqT s C [vi32 n] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .single (.value trivial)

theorem ASeqT.tableGrow_ref {s : Store} {f : Frame} {C : Context} {x addr : Nat}
    {ti : TableInst} {n : BitVec 32} {r : Ref} {a b : List OpType} (hf : FrameCtx s f C)
    (h : ASeqT s C [(Val.ref r).instr, (Val.i32 n).instr, .plain (.tableGrow x)] ⟨a, b⟩)
    (ha : f.inst.tables[x]? = some addr) (hti : s.tables[addr]? = some ti) :
    Val.HasType s (.ref r) (.ref ti.type.elem) := by
  obtain ⟨p, ts, out, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (vs := [.ref r, .i32 n]) (by
    intro x y hi
    cases hi with | plain hi => cases hi; rfl)
  cases hi with | plain hi =>
    cases hi with | tableGrow hx =>
      cases hvs with | cons hv hs =>
        simpa only [hf.tableType hx ha hti, HasOpType] using hv

theorem ASeqT.tableGrow {s : Store} {C : Context} {x : Nat} {n : BitVec 32} {r : Ref}
    {a b : List OpType}
    (h : ASeqT s C [(Val.ref r).instr, (Val.i32 n).instr, .plain (.tableGrow x)] ⟨a, b⟩)
    (v : BitVec 32) : ASeqT s C [(Val.i32 v).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.ref r, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .single (.value trivial)

theorem ASeqT.tableFillZero {s : Store} {C : Context} {x : Nat} {i n : BitVec 32} {r : Ref}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, (Val.ref r).instr, (Val.i32 n).instr,
      .plain (.tableFill x)] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i, .ref r, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.tableFill {s : Store} {C : Context} {x : Nat} {i n : BitVec 32} {r : Ref}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, (Val.ref r).instr, (Val.i32 n).instr,
      .plain (.tableFill x)] ⟨a, b⟩) :
    ASeqT s C [(Val.i32 i).instr, (Val.ref r).instr, .plain (.tableSet x),
      vi32 (i.toNat + 1), (Val.ref r).instr, vi32 (n.toNat - 1), .plain (.tableFill x)]
      ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i, .ref r, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro ins out hi hvs
    cases hi with | plain hi =>
      cases hi with | @tableFill _ _ tt hx =>
        cases hvs with | cons _ hs =>
          cases hs with | cons hv hs =>
            have h₁ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
              (ASeqT.values (vs := [.i32 i, .ref r]) (ts := [.num .i32, .ref tt.elem])
                (.cons trivial (.cons hv .nil)))
              (Matches.refl _) (.plain (.tableSet hx))
            have h₂ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
              (ASeqT.values (vs := [.i32 (BitVec.ofNat 32 (i.toNat + 1)), .ref r,
                .i32 (BitVec.ofNat 32 (n.toNat - 1))])
                (ts := [.num .i32, .ref tt.elem, .num .i32])
                (.cons trivial (.cons hv (.cons trivial .nil))))
              (Matches.refl _) (.plain (.tableFill hx))
            exact h₁.append h₂

theorem ASeqT.tableCopyZero {s : Store} {C : Context} {x y : Nat} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.tableCopy x y)] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

private theorem table_copy_chunk {s : Store} {C : Context} {x y : Nat} {tx ty : TableType}
    (hx : C.tables[x]? = some tx) (hy : C.tables[y]? = some ty) (he : tx.elem = ty.elem)
    (d src : BitVec 32) :
    ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, .plain (.tableGet y),
      .plain (.tableSet x)] ⟨[], []⟩ := by
  have h₀ := ASeqT.values (s := s) (C := C) (vs := [.i32 d, .i32 src])
    (ts := [.num .i32, .num .i32]) (.cons trivial (.cons trivial .nil))
  have h₁ := ASeqT.snoc (t₀ := [i32]) h₀ (Matches.refl _) (.plain (.tableGet hy))
  have hm : Matches [i32, .val (.ref ty.elem)] [i32, .val (.ref tx.elem)] :=
    .cons rfl (.cons (congrArg ValType.ref he.symm) .nil)
  exact .snoc (t₀ := []) h₁ hm (.plain (.tableSet hx))

private theorem table_copy_again {s : Store} {C : Context} {x y : Nat} {tx ty : TableType}
    (hx : C.tables[x]? = some tx) (hy : C.tables[y]? = some ty) (he : tx.elem = ty.elem)
    (d src n : BitVec 32) :
    ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.tableCopy x y)] ⟨[], []⟩ :=
  .snoc (t₀ := []) (.values (vs := [.i32 d, .i32 src, .i32 n])
    (ts := [.num .i32, .num .i32, .num .i32])
    (.cons trivial (.cons trivial (.cons trivial .nil))))
    (Matches.refl _) (.plain (.tableCopy hx hy he))

theorem ASeqT.tableCopyUp {s : Store} {C : Context} {x y : Nat} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.tableCopy x y)] ⟨a, b⟩) :
    ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, .plain (.tableGet y),
      .plain (.tableSet x), vi32 (d.toNat + 1), vi32 (src.toNat + 1), vi32 (n.toNat - 1),
      .plain (.tableCopy x y)] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | tableCopy hx hy he =>
        exact (table_copy_chunk hx hy he d src).append
          (table_copy_again hx hy he (BitVec.ofNat 32 (d.toNat + 1))
            (BitVec.ofNat 32 (src.toNat + 1)) (BitVec.ofNat 32 (n.toNat - 1)))

theorem ASeqT.tableCopyDown {s : Store} {C : Context} {x y : Nat} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.tableCopy x y)] ⟨a, b⟩) :
    ASeqT s C [vi32 (d.toNat + n.toNat - 1), vi32 (src.toNat + n.toNat - 1),
      .plain (.tableGet y), .plain (.tableSet x), (Val.i32 d).instr, (Val.i32 src).instr,
      vi32 (n.toNat - 1), .plain (.tableCopy x y)] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | tableCopy hx hy he =>
        exact (table_copy_chunk hx hy he (BitVec.ofNat 32 (d.toNat + n.toNat - 1))
          (BitVec.ofNat 32 (src.toNat + n.toNat - 1))).append
          (table_copy_again hx hy he d src (BitVec.ofNat 32 (n.toNat - 1)))

theorem ASeqT.tableInitZero {s : Store} {C : Context} {x y : Nat} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.tableInit x y)] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.tableInit {s : Store} {f : Frame} {C : Context} {x y addr : Nat}
    {ei : ElemInst} {r : Ref} {d src n : BitVec 32} {a b : List OpType}
    (hok : StoreOK s) (hf : FrameCtx s f C)
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.tableInit x y)] ⟨a, b⟩)
    (ha : f.inst.elems[y]? = some addr) (hei : s.elems[addr]? = some ei)
    (hr : ei.elem[src.toNat]? = some r) :
    ASeqT s C [(Val.i32 d).instr, (Val.ref r).instr, .plain (.tableSet x),
      vi32 (d.toNat + 1), vi32 (src.toNat + 1), vi32 (n.toNat - 1),
      .plain (.tableInit x y)] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro ins out hi _
    cases hi with | plain hi =>
      cases hi with | @tableInit _ _ _ tt rt hx hy he =>
        have hv : Val.HasType s (.ref r) (.ref tt.elem) := by
          simpa only [hf.elemType hy ha hei, he] using
            hok.elems ei (List.mem_of_getElem? hei) r (List.mem_of_getElem? hr)
        have h₁ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
          (ASeqT.values (vs := [.i32 d, .ref r]) (ts := [.num .i32, .ref tt.elem])
            (.cons trivial (.cons hv .nil)))
          (Matches.refl _) (.plain (.tableSet hx))
        have h₂ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
          (ASeqT.values (vs := [.i32 (BitVec.ofNat 32 (d.toNat + 1)),
            .i32 (BitVec.ofNat 32 (src.toNat + 1)), .i32 (BitVec.ofNat 32 (n.toNat - 1))])
            (ts := [.num .i32, .num .i32, .num .i32])
            (.cons trivial (.cons trivial (.cons trivial .nil))))
          (Matches.refl _) (.plain (.tableInit hx hy he))
        exact h₁.append h₂

theorem ASeqT.elemDrop {s : Store} {C : Context} {idx : Nat} {a b : List OpType}
    (h : ASeqT s C [.plain (.elemDrop idx)] ⟨a, b⟩) : Matches a b := by
  apply ASeqT.nil_iff.mp
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

end FVA.Wasm.Valid
