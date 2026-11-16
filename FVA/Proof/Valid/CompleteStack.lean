import FVA.Proof.Valid.Validator
import FVA.Proof.Valid.Seq

namespace FVA.Wasm.Valid

open FVA.Wasm Check ValidatorProof

namespace CompletenessProof

/-- The algorithm's principal stack can instantiate to the declarative stack. -/
def Conforms (s : Stack) (ts : List OpType) : Prop :=
  ∃ actual, Fits s actual ∧ Matches actual ts

theorem matches_snoc {as bs : List OpType} {a b : OpType}
    (h : Matches (as ++ [a]) (bs ++ [b])) : Matches as bs ∧ a.Matches b := by
  have hr := matches_reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at hr
  cases hr with
  | cons hab h => exact ⟨by simpa using matches_reverse h, hab⟩

theorem conforms_mono {s : Stack} {as bs : List OpType}
    (h : Conforms s as) (hm : Matches as bs) : Conforms s bs := by
  obtain ⟨actual, hf, ha⟩ := h
  exact ⟨actual, hf, ha.trans hm⟩

theorem conforms_start (ts : List OpType) : Conforms ⟨ts.reverse, false⟩ ts :=
  ⟨ts, ⟨[], .inr rfl, by simp⟩, matches_refl ts⟩

theorem conforms_reset (ts : List OpType) : Conforms ⟨[], true⟩ ts :=
  ⟨ts, ⟨ts, .inl rfl, by simp⟩, matches_refl ts⟩

theorem conforms_pop {s : Stack} {ts : List OpType} {t : OpType}
    (h : Conforms s (ts ++ [t])) :
    ∃ a rest, pop s = some (a, rest) ∧ a.Matches t ∧ Conforms rest ts := by
  obtain ⟨actual, ⟨pre, hu, rfl⟩, hm⟩ := h
  rcases s with ⟨ss, u⟩
  cases ss with
  | nil =>
    cases u with
    | false =>
      rcases hu with hu | rfl
      · cases hu
      · have hl := (show Matches [] (ts ++ [t]) from by simpa using hm).length_eq
        simp at hl
    | true => exact ⟨.bot, ⟨[], true⟩, rfl, trivial, conforms_reset ts⟩
  | cons a as =>
    have hm' : Matches ((pre ++ as.reverse) ++ [a]) (ts ++ [t]) := by
      simpa [List.reverse_cons, List.append_assoc] using hm
    obtain ⟨hrest, ha⟩ := matches_snoc hm'
    exact ⟨a, ⟨as, u⟩, rfl, ha, pre ++ as.reverse, ⟨pre, hu, rfl⟩, hrest⟩

theorem defFunc_complete {d : DefType} : defFunc (.def_ d) (.abs .func) = true := rfl

theorem subType_complete {t u : ValType} (h : t.Sub u) : subType t u = true := by
  cases t with
  | num a =>
    cases u with
    | num b =>
      simp only [ValType.Sub] at h
      simp [subType, h]
    | ref _ => exact h.elim
  | ref r =>
    cases u with
    | num _ => exact h.elim
    | ref r' =>
      rcases r with ⟨n₁, h₁⟩
      rcases r' with ⟨n₂, h₂⟩
      obtain ⟨hn, hh⟩ := h
      simp only [subType, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨by cases n₁ <;> cases n₂ <;> simp_all, ?_⟩
      rcases hh with he | ⟨d, hd, hf⟩
      · simp only at he
        subst he
        exact .inl (HeapType.beq_refl _)
      · simp only at hd hf
        subst hd hf
        exact .inr rfl

theorem subTypes_complete {ts us : List ValType} (h : ResultSub ts us) : subTypes ts us = true := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [subTypes, subType_complete h, ih]

theorem matchType_complete {a b : OpType} (h : a.Matches b) : matchType a b = true := by
  cases a with
  | bot => rfl
  | refBot =>
    cases b with
    | bot => exact h.elim
    | refBot => rfl
    | val u =>
      cases u with
      | num _ => exact h.elim
      | ref _ => rfl
  | val t =>
    cases b with
    | val u => exact subType_complete h
    | _ => exact h.elim

theorem matchTypeList_complete {as bs : List OpType} (h : Matches as bs) :
    matchTypeList as bs = true := by
  induction h with
  | nil => rfl
  | cons h h' ih => simp [matchTypeList, matchType_complete h, ih]

/-- Keep the popped principal operands, not merely their widened expected types. -/
theorem pops_complete {s : Stack} {pre abstract wanted : List OpType}
    (h : Conforms s (pre ++ abstract.reverse)) (hm : Matches abstract wanted) :
    ∃ actual rest, pops wanted s = some (actual, rest) ∧
      Matches actual abstract ∧ Conforms rest pre := by
  induction hm generalizing s with
  | nil => exact ⟨[], s, rfl, .nil, by simpa using h⟩
  | @cons a b as bs hab hm ih =>
    have hc : Conforms s ((pre ++ as.reverse) ++ [a]) := by
      simpa [List.reverse_cons, List.append_assoc] using h
    obtain ⟨v, rest, hp, hva, hc⟩ := conforms_pop hc
    obtain ⟨actual, out, hs, ha, ho⟩ := ih hc
    refine ⟨v :: actual, out, ?_, .cons hva ha, ho⟩
    simp [pops, hp, matchType_complete (hva.trans hab), hs]

theorem conforms_push {s : Stack} {pre as bs : List OpType}
    (h : Conforms s pre) (hm : Matches as bs) : Conforms (push as s) (pre ++ bs) := by
  obtain ⟨actual, ⟨missing, hu, rfl⟩, ha⟩ := h
  refine ⟨(missing ++ s.types.reverse) ++ as, ⟨missing, hu, ?_⟩, matches_append ha hm⟩
  simp [push, List.reverse_append, List.append_assoc]

theorem apply_complete {s : Stack} {pre : List OpType} {st : StackType}
    (h : Conforms s (pre ++ st.ins)) :
    ∃ out, apply st s = some out ∧ Conforms out (pre ++ st.outs) := by
  obtain ⟨actual, rest, hp, _, hr⟩ := pops_complete
    (abstract := st.ins.reverse) (by simpa using h) (matches_refl _)
  exact ⟨push st.outs rest, by simp [apply, hp], conforms_push hr (matches_refl _)⟩

theorem conforms_empty {s : Stack} (h : Conforms s []) : s.types = [] := by
  obtain ⟨actual, ⟨pre, hu, rfl⟩, hm⟩ := h
  have hl := hm.length_eq
  simp only [List.length_append, List.length_reverse, List.length_nil] at hl
  exact List.length_eq_zero_iff.mp (by omega)

theorem finish_complete {s : Stack} {ts : List ValType} (h : Conforms s (ops ts)) :
    finish ts s = true := by
  obtain ⟨actual, rest, hp, _, hr⟩ := pops_complete
    (pre := []) (abstract := (ops ts).reverse) (by simpa using h) (matches_refl _)
  simp [finish, hp, conforms_empty hr]

end CompletenessProof
end FVA.Wasm.Valid
