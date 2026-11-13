import FVA.Impl.Valid
import FVA.Proof.Valid.Entails

namespace FVA.Wasm.Valid

open FVA.Wasm Check

theorem _root_.FVA.Wasm.ValType.sub_refl (t : ValType) : t.Sub t := by
  cases t with
  | num _ => rfl
  | ref _ => exact ⟨id, .inl rfl⟩

theorem OpType.matches_refl (t : OpType) : t.Matches t := by
  cases t with
  | bot | refBot => trivial
  | val t => exact t.sub_refl

namespace ValidatorProof

theorem heapSrc_sound {k : Nat} {h : HeapType} (hs : heapSrc k h = true) : h.Src k := by
  cases h <;> simp_all [heapSrc, HeapType.Src, Nat.blt_eq]

theorem valSrc_sound {k : Nat} {t : ValType} (hs : valSrc k t = true) : t.Src k := by
  cases t with
  | num _ => trivial
  | ref r => exact heapSrc_sound hs

theorem defFunc_sound {h₁ h₂ : HeapType} (h : defFunc h₁ h₂ = true) :
    ∃ d, h₁ = .def_ d ∧ h₂ = .abs .func := by
  cases h₁ with
  | def_ d =>
    cases h₂ with
    | abs a => cases a <;> simp_all [defFunc]
    | _ => simp [defFunc] at h
  | _ => simp [defFunc] at h

theorem subType_sound {t u : ValType} (h : subType t u = true) : t.Sub u := by
  cases t with
  | num a =>
    cases u with
    | num b => simpa [subType, ValType.Sub] using h
    | ref _ => simp [subType] at h
  | ref r =>
    cases u with
    | num _ => simp [subType] at h
    | ref r' =>
      rcases r with ⟨n₁, h₁⟩
      rcases r' with ⟨n₂, h₂⟩
      simp only [subType, Bool.and_eq_true, Bool.or_eq_true] at h
      refine ⟨fun hn => ?_, ?_⟩
      · cases n₁ <;> cases n₂ <;> simp_all
      · rcases h.2 with h' | h'
        · exact .inl (HeapType.eq_of_beq h')
        · exact .inr (defFunc_sound h')

theorem subTypes_sound {ts us : List ValType} (h : subTypes ts us = true) : ResultSub ts us := by
  induction ts generalizing us with
  | nil => cases us <;> simp_all [subTypes, ResultSub]
  | cons t ts ih =>
    cases us with
    | nil => simp [subTypes] at h
    | cons u us =>
      simp only [subTypes, Bool.and_eq_true] at h
      exact .cons (subType_sound h.1) (ih h.2)

theorem matchType_sound {a b : OpType} (h : matchType a b = true) : a.Matches b := by
  cases a with
  | bot => trivial
  | refBot =>
    cases b with
    | bot => simp [matchType] at h
    | refBot => trivial
    | val t =>
      cases t with
      | num _ => simp [matchType] at h
      | ref _ => trivial
  | val t =>
    cases b with
    | val u => exact subType_sound h
    | _ => simp [matchType] at h

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
  | cons t ts ih => exact .cons t.matches_refl ih

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

/-- The context the next instruction after `es` is typed in (`SeqT.snoc`). -/
abbrev Next (C : Context) (es : List Instr) : Context := C.addSets (es.flatMap Instr.sets)

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
    {es : List Instr} (hi : InstrT (Next C es) i st) (h : apply st s = some s')
    {ins : List OpType} (ht : Typed C es ins s) :
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
