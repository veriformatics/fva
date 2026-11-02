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
  | refIsNull =>
    obtain ⟨a, rest, hp, ha, hr⟩ := conforms_pop h
    cases a with
    | bot =>
      exact ⟨push [i32] rest, by simp [instr, hp], conforms_push hr (matches_refl _)⟩
    | val t =>
      simp only [OpType.Matches] at ha
      subst t
      exact ⟨push [i32] rest, by simp [instr, hp], conforms_push hr (matches_refl _)⟩
  | select ht => exact select_complete ht h
  | block hb hs ih =>
    obtain ⟨inner, he, hc⟩ := ih (pre := []) (by simpa using conforms_start _)
    have hf := finish_complete (by simpa using hc)
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, hb, he, hf] using ho, hc⟩
  | loop hb hs ih =>
    obtain ⟨inner, he, hc⟩ := ih (pre := []) (by simpa using conforms_start _)
    have hf := finish_complete (by simpa using hc)
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, hb, he, hf] using ho, hc⟩
  | if_ hb hs₁ hs₂ ih₁ ih₂ =>
    obtain ⟨inner₁, he₁, hc₁⟩ := ih₁ (pre := []) (by simpa using conforms_start _)
    obtain ⟨inner₂, he₂, hc₂⟩ := ih₂ (pre := []) (by simpa using conforms_start _)
    have hf₁ := finish_complete (by simpa using hc₁)
    have hf₂ := finish_complete (by simpa using hc₂)
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, hb, he₁, he₂, hf₁, hf₂] using ho, hc⟩
  | br hl =>
    exact ⟨⟨[], true⟩, by simpa [instr, hl] using branch_complete h, conforms_reset _⟩
  | return_ hr =>
    exact ⟨⟨[], true⟩, by simpa [instr, hr] using branch_complete h, conforms_reset _⟩
  | brTable ht => exact brTable_complete ht h
  | @callIndirect C x y tt ft ht he hy =>
    rcases tt with ⟨limits, elem⟩
    simp only at he
    subst elem
    obtain ⟨out, ho, hc⟩ := apply_complete h
    exact ⟨out, by simpa [instr, fixed, ht, hy] using ho, hc⟩
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
