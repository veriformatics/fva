import FVA.Proof.Valid.Redex

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem numVal_typed (s : Store) (t : NumType) (n : Nat) :
    (t.val n).HasType s (.num t) := by cases t <;> trivial

theorem packedVal_typed (s : Store) (w : Width) (n : Nat) (sx : Sx) (v : Nat) :
    (packedVal w n sx v).HasType s (.num w.int) := by cases w <;> cases sx <;> trivial

theorem ASeqT.load {s : Store} {C : Context} {i : BitVec 32} {t : NumType} {m : MemArg}
    {a b : List OpType} (h : ASeqT s C [(Val.i32 i).instr, .plain (.load t m)] ⟨a, b⟩)
    (v : Nat) : ASeqT s C [(t.val v).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .single (.value (numVal_typed s t v))

theorem ASeqT.loadPacked {s : Store} {C : Context} {i : BitVec 32} {w : Width}
    {p : PackSize} {sx : Sx} {m : MemArg} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, .plain (.loadPacked w p sx m)] ⟨a, b⟩) (v : Nat) :
    ASeqT s C [(packedVal w p.bits sx v).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi
      exact .single (.value (packedVal_typed s w p.bits sx v))

theorem ASeqT.store {s : Store} {C : Context} {i : BitVec 32} {v : Val} {t : NumType}
    {m : MemArg} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, v.instr, .plain (.store t m)] ⟨a, b⟩) : Matches a b := by
  apply ASeqT.nil_iff.mp
  apply h.replace_fixed (vs := [.i32 i, v])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.storePacked {s : Store} {C : Context} {i : BitVec 32} {v : Val} {w : Width}
    {p : PackSize} {m : MemArg} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, v.instr, .plain (.storePacked w p m)] ⟨a, b⟩) :
    Matches a b := by
  apply ASeqT.nil_iff.mp
  apply h.replace_fixed (vs := [.i32 i, v])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.memorySize {s : Store} {C : Context} {a b : List OpType}
    (h : ASeqT s C [.plain .memorySize] ⟨a, b⟩) (n : Nat) :
    ASeqT s C [vi32 n] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .single (.value trivial)

theorem ASeqT.memoryGrow {s : Store} {C : Context} {i : BitVec 32} {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, .plain .memoryGrow] ⟨a, b⟩) (v : BitVec 32) :
    ASeqT s C [(Val.i32 v).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .single (.value trivial)

theorem ASeqT.memoryFillZero {s : Store} {C : Context} {i n : BitVec 32} {v : Val}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, v.instr, (Val.i32 n).instr, .plain .memoryFill]
      ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i, v, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.memoryFill {s : Store} {C : Context} {i n : BitVec 32} {v : Val}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 i).instr, v.instr, (Val.i32 n).instr, .plain .memoryFill]
      ⟨a, b⟩) :
    ASeqT s C [(Val.i32 i).instr, v.instr, .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
      vi32 (i.toNat + 1), v.instr, vi32 (n.toNat - 1), .plain .memoryFill] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 i, v, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi with | memoryFill hm =>
        cases hvs with | cons _ hs =>
          cases hs with | cons hv hs =>
            have h₁ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
              (ASeqT.values (vs := [.i32 i, v]) (ts := [.num .i32, .num .i32])
                (.cons trivial (.cons hv .nil)))
              (Matches.refl _) (.plain (.storePacked (w := .w32) (p := .p8)
                (m := ⟨0, 0⟩) hm trivial (by constructor <;> decide)))
            have h₂ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
              (ASeqT.values (vs := [.i32 (BitVec.ofNat 32 (i.toNat + 1)), v,
                .i32 (BitVec.ofNat 32 (n.toNat - 1))])
                (ts := [.num .i32, .num .i32, .num .i32])
                (.cons trivial (.cons hv (.cons trivial .nil))))
              (Matches.refl _) (.plain (.memoryFill hm))
            exact h₁.append h₂

theorem ASeqT.memoryCopyZero {s : Store} {C : Context} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain .memoryCopy] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

private theorem copy_chunk {s : Store} {C : Context} {lim : Limits}
    (hm : C.mems[0]? = some lim) (d src : Nat) :
    ASeqT s C [vi32 d, vi32 src, .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩),
      .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ⟨[], []⟩ := by
  have h₀ := ASeqT.values (s := s) (C := C)
    (vs := [.i32 (BitVec.ofNat 32 d), .i32 (BitVec.ofNat 32 src)])
    (ts := [.num .i32, .num .i32]) (.cons trivial (.cons trivial .nil))
  have h₁ := ASeqT.snoc (t₀ := [i32]) h₀ (Matches.refl _)
    (.plain (.loadPacked (w := .w32) (p := .p8) (sx := .u) (m := ⟨0, 0⟩)
      hm trivial (by constructor <;> decide)))
  exact .snoc (t₀ := []) h₁ (Matches.refl _)
    (.plain (.storePacked (w := .w32) (p := .p8) (m := ⟨0, 0⟩)
      hm trivial (by constructor <;> decide)))

private theorem copy_again {s : Store} {C : Context} {lim : Limits}
    (hm : C.mems[0]? = some lim) (d src n : BitVec 32) :
    ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain .memoryCopy] ⟨[], []⟩ :=
  .snoc (t₀ := []) (.values (vs := [.i32 d, .i32 src, .i32 n])
    (ts := [.num .i32, .num .i32, .num .i32])
    (.cons trivial (.cons trivial (.cons trivial .nil))))
    (Matches.refl _) (.plain (.memoryCopy hm))

theorem ASeqT.memoryCopyUp {s : Store} {C : Context} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain .memoryCopy] ⟨a, b⟩) :
    ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr,
      .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
      vi32 (d.toNat + 1), vi32 (src.toNat + 1), vi32 (n.toNat - 1), .plain .memoryCopy]
      ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | memoryCopy hm =>
        simpa only [vi32, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.cons_append,
          List.nil_append] using
          (copy_chunk (s := s) hm d.toNat src.toNat).append
            (copy_again hm (BitVec.ofNat 32 (d.toNat + 1))
              (BitVec.ofNat 32 (src.toNat + 1)) (BitVec.ofNat 32 (n.toNat - 1)))

theorem ASeqT.memoryCopyDown {s : Store} {C : Context} {d src n : BitVec 32}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain .memoryCopy] ⟨a, b⟩) :
    ASeqT s C [vi32 (d.toNat + n.toNat - 1), vi32 (src.toNat + n.toNat - 1),
      .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
      (Val.i32 d).instr, (Val.i32 src).instr, vi32 (n.toNat - 1), .plain .memoryCopy]
      ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | memoryCopy hm =>
        exact (copy_chunk hm (d.toNat + n.toNat - 1) (src.toNat + n.toNat - 1)).append
          (copy_again hm d src (BitVec.ofNat 32 (n.toNat - 1)))

theorem ASeqT.memoryInitZero {s : Store} {C : Context} {d src n : BitVec 32} {idx : Nat}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.memoryInit idx)] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.memoryInit {s : Store} {C : Context} {d src n : BitVec 32} {idx : Nat}
    {a b : List OpType}
    (h : ASeqT s C [(Val.i32 d).instr, (Val.i32 src).instr, (Val.i32 n).instr,
      .plain (.memoryInit idx)] ⟨a, b⟩) (byte : UInt8) :
    ASeqT s C [(Val.i32 d).instr, vi32 byte.toNat,
      .plain (.storePacked .w32 .p8 ⟨0, 0⟩), vi32 (d.toNat + 1), vi32 (src.toNat + 1),
      vi32 (n.toNat - 1), .plain (.memoryInit idx)] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.i32 d, .i32 src, .i32 n])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi =>
      cases hi with | memoryInit hm hd =>
        have h₁ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
          (ASeqT.values (vs := [.i32 d, .i32 (BitVec.ofNat 32 byte.toNat)])
            (ts := [.num .i32, .num .i32]) (.cons trivial (.cons trivial .nil)))
          (Matches.refl _) (.plain (.storePacked (w := .w32) (p := .p8) (m := ⟨0, 0⟩)
            hm trivial (by constructor <;> decide)))
        have h₂ := ASeqT.snoc (s := s) (C := C) (t₀ := [])
          (ASeqT.values (vs := [.i32 (BitVec.ofNat 32 (d.toNat + 1)),
            .i32 (BitVec.ofNat 32 (src.toNat + 1)), .i32 (BitVec.ofNat 32 (n.toNat - 1))])
            (ts := [.num .i32, .num .i32, .num .i32])
            (.cons trivial (.cons trivial (.cons trivial .nil))))
          (Matches.refl _) (.plain (.memoryInit hm hd))
        exact h₁.append h₂

theorem ASeqT.dataDrop {s : Store} {C : Context} {idx : Nat} {a b : List OpType}
    (h : ASeqT s C [.plain (.dataDrop idx)] ⟨a, b⟩) : Matches a b := by
  apply ASeqT.nil_iff.mp
  apply h.replace_fixed (vs := [])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

end FVA.Wasm.Valid
