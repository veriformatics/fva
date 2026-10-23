import FVA.Impl.Valid

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

theorem matchType_sound {a b : OpType} (h : matchType a b = true) : a.Matches b := by
  cases a <;> cases b <;> simp_all [matchType, OpType.Matches]

theorem matchTypeList_sound {as bs : List OpType} (h : matchTypeList as bs = true) :
    Matches as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [matchTypeList, Matches]
  | cons a as ih =>
    cases bs with
    | nil => simp [matchTypeList] at h
    | cons b bs =>
      simp only [matchTypeList, Bool.and_eq_true] at h
      exact .cons (matchType_sound h.1) (ih h.2)

theorem matches_refl (ts : List OpType) : Matches ts ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons (by cases t <;> simp [OpType.Matches]) ih

theorem matches_append {as bs cs ds : List OpType} (h : Matches as bs) (h' : Matches cs ds) :
    Matches (as ++ cs) (bs ++ ds) := by
  induction h with
  | nil => exact h'
  | cons hab h ih => exact .cons hab ih

theorem matches_reverse {as bs : List OpType} (h : Matches as bs) :
    Matches as.reverse bs.reverse := by
  induction h with
  | nil => exact .nil
  | cons hab h ih =>
    simpa [List.reverse_cons] using matches_append ih (.cons hab .nil)

/-- A polymorphic prefix exists only below the current frame's explicit operands. -/
def Fits (s : Stack) (ts : List OpType) : Prop :=
  ∃ pre, (s.unreachable = true ∨ pre = []) ∧ ts = pre ++ s.types.reverse

/-- Every admissible operand prefix has a declarative sequence derivation. -/
def Typed (C : Context) (es : List Instr) (ins : List OpType) (s : Stack) : Prop :=
  ∀ ts, Fits s ts → SeqT C es ⟨ins, ts⟩

theorem fits_self (s : Stack) : Fits s s.types.reverse := ⟨[], .inr rfl, rfl⟩

theorem pop_fits {s rest : Stack} {a : OpType} (h : pop s = some (a, rest))
    {ts : List OpType} (ht : Fits rest ts) : Fits s (ts ++ [a]) := by
  rcases s with ⟨ss, u⟩
  cases ss with
  | nil =>
    cases u with
    | false => simp [pop] at h
    | true =>
      cases h
      exact ⟨ts ++ [.bot], .inl rfl, by simp⟩
  | cons b bs =>
    simp only [pop, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rcases ht with ⟨pre, hp, rfl⟩
    exact ⟨pre, hp, by simp [List.reverse_cons, List.append_assoc]⟩

theorem pops_fits {expected actual : List OpType} {s rest : Stack}
    (h : pops expected s = some (actual, rest)) :
    Matches actual expected ∧ ∀ ts, Fits rest ts → Fits s (ts ++ actual.reverse) := by
  induction expected generalizing actual s rest with
  | nil =>
    simp only [pops, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨.nil, fun ts ht => by simpa using ht⟩
  | cons e es ih =>
    simp only [pops] at h
    cases hp : pop s with
    | none => simp [hp] at h
    | some pair =>
      rcases pair with ⟨a, s'⟩
      simp only [hp] at h
      cases hm : matchType a e with
      | false => simp [hm] at h
      | true =>
        simp only [hm, Bool.cond_true] at h
        cases hr : pops es s' with
        | none => simp [hr] at h
        | some pair =>
          rcases pair with ⟨as, rest'⟩
          simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨hm', hf⟩ := ih hr
          refine ⟨.cons (matchType_sound hm) hm', ?_⟩
          intro ts ht
          simpa [List.reverse_cons, List.append_assoc] using pop_fits hp (hf ts ht)

theorem push_fits {s : Stack} {ts out : List OpType} (h : Fits (push ts s) out) :
    ∃ before, Fits s before ∧ out = before ++ ts := by
  rcases h with ⟨pre, hp, he⟩
  refine ⟨pre ++ s.types.reverse, ⟨pre, hp, rfl⟩, ?_⟩
  simpa [push, List.reverse_append, List.append_assoc] using he

theorem apply_typed {C : Context} {i : Instr} {st : StackType} {s s' : Stack}
    (hi : InstrT C i st) (h : apply st s = some s')
    {es : List Instr} {ins : List OpType} (ht : Typed C es ins s) :
    Typed C (es ++ [i]) ins s' := by
  simp only [apply] at h
  cases hp : pops st.ins.reverse s with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨actual, rest⟩
    simp only [hp, Option.some.injEq] at h
    subst s'
    intro out hout
    obtain ⟨before, hbefore, rfl⟩ := push_fits hout
    obtain ⟨hm, hf⟩ := pops_fits hp
    exact .snoc (ht _ (hf before hbefore))
      (by simpa using matches_reverse hm) hi

theorem start_typed (C : Context) (ins : List OpType) :
    Typed C [] ins ⟨ins.reverse, false⟩ := by
  intro ts ht
  rcases ht with ⟨pre, hp, rfl⟩
  rcases hp with hp | rfl
  · cases hp
  · simpa using (SeqT.nil (C := C) (ts := ins))

theorem finish_typed {C : Context} {es : List Instr} {ins : List OpType} {s : Stack}
    {out : List ValType} (h : finish out s = true) (ht : Typed C es ins s) :
    SeqT C es ⟨ins, ops out⟩ := by
  simp only [finish] at h
  cases hp : pops (ops out).reverse s with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨actual, rest⟩
    simp only [hp, List.isEmpty_iff] at h
    obtain ⟨hm, hf⟩ := pops_fits hp
    have he : Fits rest [] := ⟨[], .inr rfl, by simp [h]⟩
    exact .sub (ht _ (by simpa using hf [] he)) (by simpa using matches_reverse hm)

end ValidatorProof
end FVA.Wasm.Valid
