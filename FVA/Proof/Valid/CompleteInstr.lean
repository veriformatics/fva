import FVA.Proof.Valid.CompleteFixed

namespace FVA.Wasm.Valid

open FVA.Wasm Check ValidatorProof

namespace CompletenessProof

theorem memArg_num_complete {m : MemArg} {t : NumType} (h : m.WF t.bytes) :
    memArg m t.bytes = true :=
  memArg_complete h (by cases t <;> decide)

theorem memArg_pack_complete {m : MemArg} {p : PackSize} (h : m.WF (p.bits / 8)) :
    memArg m (p.bits / 8) = true :=
  memArg_complete h (by cases p <;> decide)

theorem catchOk_complete {C : Context} {c : Catch} (h : CatchOK C c) : catchOk C c = true := by
  cases c with
  | tag x l =>
    obtain ⟨ts, lts, ht, hl, hs⟩ := h
    simp [catchOk, ht, hl, subTypes_complete hs]
  | tagRef x l =>
    obtain ⟨ts, lts, ht, hl, hs⟩ := h
    simp [catchOk, ht, hl, subTypes_complete hs]
  | all l => simp only [CatchOK] at h; simp [catchOk, h]
  | allRef l =>
    obtain ⟨lts, hl, hs⟩ := h
    simp [catchOk, hl, subTypes_complete hs]

theorem tailCall_complete {C : Context} {ft : FuncType} {rs : List ValType}
    {operands : List ValType} {s : Stack} {pre discard : List OpType}
    (hr : C.return_ = some rs) (hs : ResultSub ft.results rs)
    (h : Conforms s (pre ++ (discard ++ ops operands))) :
    tailCall C ft operands s = some ⟨[], true⟩ := by
  simp [tailCall, hr, subTypes_complete hs, branch_complete h]

theorem instr_complete {C : Context} {i : Instr} {st : StackType} (hi : InstrT C i st)
    {s : Stack} {pre : List OpType} (h : Conforms s (pre ++ st.ins)) :
    ∃ out, instr C i s = some out ∧ Conforms out (pre ++ st.outs) := by
  induction hi using InstrT.rec
    (motive_2 := fun C is st _ => ∀ {s pre}, Conforms s (pre ++ st.ins) →
      ∃ out, seq C is s = some out ∧ Conforms out (pre ++ st.outs)) generalizing s pre with
  | unreachable => exact ⟨⟨[], true⟩, rfl, conforms_reset _⟩
  | drop =>
    obtain ⟨a, rest, hp, _, hr⟩ := conforms_pop h
    exact ⟨rest, by simp [instr, hp], by simpa using hr⟩
  | @refIsNull C t =>
    obtain ⟨a, rest, hp, ha, hr⟩ := conforms_pop h
    refine ⟨push [i32] rest, ?_, conforms_push hr (matches_refl _)⟩
    cases a with
    | bot => simp [instr, hp]
    | refBot => simp [instr, hp]
    | val u =>
      cases u with
      | num _ => exact ha.elim
      | ref r => simp [instr, hp]
  | @refAsNonNull C hh =>
    obtain ⟨a, rest, hp, ha, hr⟩ := conforms_pop h
    obtain ⟨h', hh', ha', hout⟩ := refHeap_complete ha
    obtain ⟨out, ho, hc⟩ := apply_complete (st := ⟨[refOp true h'], [refOp false h']⟩)
      (pre := pre) (conforms_snoc hp hr ha')
    refine ⟨out, by simp [instr, hp, hh', ho], ?_⟩
    exact conforms_mono hc (matches_append (matches_refl pre) (.cons hout .nil))
  | select ht => exact select_complete ht h
  | block hb hs ih =>
    obtain ⟨inner, he, hc⟩ := ih (pre := []) (by simpa using conforms_start _)
    have hf := finish_complete (by simpa using hc)
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, blockType_eq, hb, he, hf] using ho, hc⟩
  | loop hb hs ih =>
    obtain ⟨inner, he, hc⟩ := ih (pre := []) (by simpa using conforms_start _)
    have hf := finish_complete (by simpa using hc)
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, blockType_eq, hb, he, hf] using ho, hc⟩
  | if_ hb hs₁ hs₂ ih₁ ih₂ =>
    obtain ⟨inner₁, he₁, hc₁⟩ := ih₁ (pre := []) (by simpa using conforms_start _)
    obtain ⟨inner₂, he₂, hc₂⟩ := ih₂ (pre := []) (by simpa using conforms_start _)
    have hf₁ := finish_complete (by simpa using hc₁)
    have hf₂ := finish_complete (by simpa using hc₂)
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, blockType_eq, hb, he₁, he₂, hf₁, hf₂] using ho, hc⟩
  | tryTable hb hs hcs ih =>
    obtain ⟨inner, he, hc⟩ := ih (pre := []) (by simpa using conforms_start _)
    have hf := finish_complete (by simpa using hc)
    have hca : ∀ c ∈ _, catchOk _ c = true := fun c hc' => catchOk_complete (hcs c hc')
    obtain ⟨out, ho, hc⟩ := apply_complete h
    refine ⟨out, ?_, hc⟩
    simp only [instr, blockType_eq, hb, he, hf, Bool.true_and, Bool.cond_eq_ite]
    simp only [List.all_eq_true.mpr hca, ↓reduceIte]
    exact ho
  | br hl =>
    exact ⟨⟨[], true⟩, by simpa [instr, hl] using branch_complete h, conforms_reset _⟩
  | return_ hr =>
    exact ⟨⟨[], true⟩, by simpa [instr, hr] using branch_complete h, conforms_reset _⟩
  | brTable ht => exact brTable_complete ht h
  | @brOnNull C l ts hh hl =>
    have h' : Conforms s ((pre ++ ops ts) ++ [refOp true hh]) := by
      simpa [List.append_assoc] using h
    obtain ⟨a, rest, hp, ha, hr⟩ := conforms_pop h'
    obtain ⟨h₁, hh₁, ha₁, hout⟩ := refHeap_complete ha
    obtain ⟨out, ho, hc⟩ := apply_complete
      (st := ⟨ops ts ++ [refOp true h₁], ops ts ++ [refOp false h₁]⟩) (pre := pre)
      (by simpa [List.append_assoc] using conforms_snoc hp hr ha₁)
    refine ⟨out, by simp [instr, hl, hp, hh₁, ho], ?_⟩
    exact conforms_mono hc (matches_append (matches_refl pre)
      (matches_append (matches_refl _) (.cons hout .nil)))
  | @returnCall C x ft rs t₃ t₄ hf hr hs =>
    exact ⟨⟨[], true⟩, by simp [instr, hf, tailCall_complete hr hs (discard := t₃) h],
      conforms_reset _⟩
  | @returnCallIndirect C x y tt ft rs t₃ t₄ ht he hy hr hs =>
    have h' : Conforms s (pre ++ (t₃ ++ ops (ft.params ++ [.num .i32]))) := by
      simpa [ops, List.map_append, List.append_assoc] using h
    exact ⟨⟨[], true⟩, by simp [instr, ht, hy, subType_complete he, tailCall_complete hr hs h'],
      conforms_reset _⟩
  | @returnCallRef C y dt ft rs t₃ t₄ hy he hr hs =>
    have h' : Conforms s (pre ++ (t₃ ++ ops (ft.params ++ [.ref ⟨true, .def_ dt⟩]))) := by
      simpa [ops, List.map_append, List.append_assoc] using h
    exact ⟨⟨[], true⟩, by simp [instr, hy, he, tailCall_complete hr hs h'], conforms_reset _⟩
  | throw hx =>
    exact ⟨⟨[], true⟩, by simpa [instr, hx] using branch_complete h, conforms_reset _⟩
  | throwRef =>
    exact ⟨⟨[], true⟩, by simpa [instr] using branch_complete (ts := [.ref .exnref]) h,
      conforms_reset _⟩
  | nil => exact ⟨_, rfl, by assumption⟩
  | @snoc C is i t₁ t₀ t' t t₃ hs hm hi ihs ihi =>
    rename_i s pre h
    obtain ⟨next, he, hc⟩ := ihs h
    have hc' : Conforms next ((pre ++ t₀) ++ t) :=
      conforms_mono (by simpa [List.append_assoc] using hc)
        (matches_append (matches_refl (pre ++ t₀)) hm)
    obtain ⟨out, ho, hc⟩ := ihi hc'
    exact ⟨out, by simp [seq_append, he, seq, ho],
      by simpa [List.append_assoc] using hc⟩
  | sub hs hm ih =>
    rename_i s pre h
    obtain ⟨out, he, hc⟩ := ih h
    exact ⟨out, he, conforms_mono hc (matches_append (matches_refl _) hm)⟩
  | refNull hs =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, heapSrc_complete hs] using ho, hc⟩
  | selectT hs =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, valSrc_complete hs] using ho, hc⟩
  | @localGet C x lt hx hs =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    refine ⟨out, ?_, hc⟩
    have hb : (lt.set || C.dead || C.sets.any (Nat.beq x)) = true := by
      rcases hs with hs | hs | hs
      · simp [hs]
      · simp [List.any_eq_true, Nat.beq_eq, hs]
      · simp [hs]
    simpa [instr, fixed, local_eq, hx, hb] using ho
  | tableCopy hx hy he =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, hx, hy, subType_complete he] using ho, hc⟩
  | tableInit hx hy he =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, hx, hy, subType_complete he] using ho, hc⟩
  | @brOnNonNull C l ts n hh hl =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, hl] using ho, hc⟩
  | callIndirect ht he hy =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, ht, hy, subType_complete he] using ho, hc⟩
  | callRef hy he =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, hy, he] using ho, hc⟩
  | _ =>
    obtain ⟨out, ho, hc⟩ := apply_complete h
    refine ⟨out, ?_, hc⟩
    simp_all [instr, fixed, local_eq, Nat.blt_eq, unary_complete, packed_complete,
      memArg_num_complete, memArg_pack_complete, List.any_eq_true, Nat.beq_eq]

theorem seq_complete {C : Context} {is : List Instr} {st : StackType} (hs : SeqT C is st)
    {s : Stack} {pre : List OpType} (h : Conforms s (pre ++ st.ins)) :
    ∃ out, seq C is s = some out ∧ Conforms out (pre ++ st.outs) := by
  induction hs using SeqT.rec (motive_1 := fun _ _ _ _ => True) generalizing s pre with
  | nil => exact ⟨s, rfl, h⟩
  | @snoc C is i t₁ t₀ t' t t₃ hs hm hi ih _ =>
    obtain ⟨next, he, hc⟩ := ih h
    have hc' : Conforms next ((pre ++ t₀) ++ t) :=
      conforms_mono (by simpa [List.append_assoc] using hc)
        (matches_append (matches_refl (pre ++ t₀)) hm)
    obtain ⟨out, ho, hc⟩ := instr_complete hi hc'
    exact ⟨out, by simp [seq_append, he, seq, ho],
      by simpa [List.append_assoc] using hc⟩
  | sub hs hm ih =>
    obtain ⟨out, he, hc⟩ := ih h
    exact ⟨out, he, conforms_mono hc (matches_append (matches_refl _) hm)⟩
  | _ => trivial

theorem expr_complete {C : Context} {e : Expr} {ts : List ValType} (h : ExprT C e ts) :
    expr C e ts = true := by
  obtain ⟨actual, ht, hm⟩ := h
  obtain ⟨out, he, hc⟩ := seq_complete ht (pre := []) (by simpa using conforms_start [])
  have hf := finish_complete (conforms_mono (by simpa using hc) hm)
  simp [expr, he, hf]

#print axioms instr_complete
#print axioms seq_complete
#print axioms expr_complete

end CompletenessProof
end FVA.Wasm.Valid
