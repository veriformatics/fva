import FVA.Proof.Valid.ValidatorFixed

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

theorem pop_typed {C : Context} {i : Instr} {s rest : Stack} {a wanted : OpType}
    {out : List OpType} (hp : pop s = some (a, rest)) (hm : a.Matches wanted)
    (hi : InstrT C i ⟨[wanted], out⟩) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) : Typed C (es ++ [i]) ins (push out rest) := by
  intro ts hs
  obtain ⟨before, hb, rfl⟩ := push_fits hs
  exact .snoc (ht _ (pop_fits hp hb)) (.cons hm .nil) hi

theorem reset_typed {C : Context} {es : List Instr} {ins : List OpType} {s : Stack}
    (ht : Typed C es ins s) : Typed C (es ++ [.unreachable]) ins ⟨[], true⟩ := by
  intro out _
  exact .snoc (t₀ := []) (ht _ (fits_self s)) (matches_refl _) .unreachable

theorem branch_typed {C : Context} {i : Instr} {ts : List ValType} {s out : Stack}
    (hi : ∀ pre result, InstrT C i ⟨pre ++ ops ts, result⟩)
    (h : branch ts s = some out) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) : Typed C (es ++ [i]) ins out := by
  simp only [branch] at h
  cases hp : pops (ops ts).reverse s with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨actual, rest⟩
    simp only [hp, Option.some.injEq] at h
    subst out
    intro result _
    obtain ⟨hm, hf⟩ := pops_fits hp
    have hstack := ht _ (hf rest.types.reverse (fits_self rest))
    have hm' : Matches (rest.types.reverse ++ actual.reverse)
        (rest.types.reverse ++ ops ts) :=
      matches_append (matches_refl _) (by simpa using matches_reverse hm)
    exact .snoc (t₀ := []) hstack hm' (hi rest.types.reverse result)

theorem selectType_sound {a b v : OpType} (h : selectType a b = some v) :
    (v = .bot ∨ ∃ n, v = .val (.num n)) ∧ a.Matches v ∧ b.Matches v := by
  cases a with
  | bot =>
    cases b with
    | bot => cases h; exact ⟨.inl rfl, trivial, trivial⟩
    | val t =>
      cases t with
      | ref r => simp [selectType] at h
      | num n => cases h; exact ⟨.inr ⟨n, rfl⟩, trivial, rfl⟩
  | val t =>
    cases t with
    | ref r => cases b <;> simp [selectType] at h
    | num n =>
      cases b with
      | bot => cases h; exact ⟨.inr ⟨n, rfl⟩, rfl, trivial⟩
      | val u =>
        cases u with
        | ref r => simp [selectType] at h
        | num m =>
          simp only [selectType, Bool.cond_eq_ite, decide_eq_true_eq] at h
          split at h <;> simp_all [OpType.Matches]
          subst v
          simp

theorem select_typed {C : Context} {s r₀ r₁ r₂ : Stack} {selector : List OpType}
    {a b v : OpType} (hp₀ : pops [i32] s = some (selector, r₀))
    (hp₁ : pop r₀ = some (a, r₁)) (hp₂ : pop r₁ = some (b, r₂))
    (hv : selectType a b = some v) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) : Typed C (es ++ [.select none]) ins (push [v] r₂) := by
  intro out hout
  obtain ⟨before, hb, rfl⟩ := push_fits hout
  obtain ⟨hsel, hf⟩ := pops_fits hp₀
  cases hsel with
  | cons hc hn =>
    cases hn
    obtain ⟨hv, ha, hb'⟩ := selectType_sound hv
    have hstack := ht _ (hf _ (pop_fits hp₁ (pop_fits hp₂ hb)))
    apply SeqT.snoc (t₀ := before) (t' := [b, a, _])
      (by simpa [List.append_assoc] using hstack)
    · exact .cons hb' (.cons ha (.cons hc .nil))
    · exact .select hv

theorem targets_sound {C : Context} {as : List OpType} {ls : List Nat}
    (h : targets C as ls = true) :
    ∀ k ∈ ls, ∃ ts, C.labels[k]? = some ts ∧ Matches as.reverse (ops ts) := by
  simp only [targets, List.all_eq_true] at h
  intro k hk
  have ht := h k hk
  cases hl : C.labels[k]? with
  | none => simp [hl] at ht
  | some ts =>
    refine ⟨ts, rfl, ?_⟩
    simp only [hl] at ht
    simpa using matches_reverse (matchTypeList_sound ht)

theorem brTable_typed {C : Context} {ls : List Nat} {l : Nat} {ts : List ValType}
    {s r₀ r₁ : Stack} {selector actual : List OpType}
    (hl : C.labels[l]? = some ts) (hp₀ : pops [i32] s = some (selector, r₀))
    (hp₁ : pops (ops ts).reverse r₀ = some (actual, r₁)) (htg : targets C actual ls = true)
    {es : List Instr} {ins : List OpType} (ht : Typed C es ins s) :
    Typed C (es ++ [.brTable ls l]) ins ⟨[], true⟩ := by
  intro out _
  obtain ⟨hs, hf₀⟩ := pops_fits hp₀
  obtain ⟨ha, hf₁⟩ := pops_fits hp₁
  have hstack := ht _ (hf₀ _ (hf₁ _ (fits_self r₁)))
  apply SeqT.snoc (t₀ := []) hstack
    (matches_append (matches_refl (r₁.types.reverse ++ actual.reverse))
      (by simpa using matches_reverse hs))
  apply InstrT.brTable (ts := actual.reverse) (t₁ := r₁.types.reverse) (t₂ := out)
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨ts, hl, by simpa using matches_reverse ha⟩
  · exact targets_sound htg k hk

end ValidatorProof
end FVA.Wasm.Valid
