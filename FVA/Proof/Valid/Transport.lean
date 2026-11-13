import FVA.Proof.Valid.Sequence
import FVA.Proof.Valid.Entails

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

end FVA.Wasm.Valid

namespace FVA.Wasm.Exec.Store.Extends

open FVA.Wasm

theorem refl (s : Store) : s.Extends s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ x hx => ⟨x, hx, rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl, rfl, Nat.le_refl _⟩
  · exact fun _ x hx => ⟨x, hx, rfl, Nat.le_refl _⟩
  · exact fun _ x hx => ⟨x, hx, rfl, Or.inr rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl, Or.inl rfl⟩
  · exact fun _ x hx => ⟨x, hx, Or.inl rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl⟩

theorem funcs_length {s s' : Store} (h : s.Extends s') : s.funcs.length ≤ s'.funcs.length := by
  by_contra hn
  have hi : s'.funcs.length < s.funcs.length := Nat.lt_of_not_ge hn
  obtain ⟨fi, hf, _⟩ := h.1 _ _ (List.getElem?_eq_getElem hi)
  simp only [List.getElem?_eq_none (Nat.le_refl _)] at hf
  cases hf

theorem exns_length {s s' : Store} (h : s.Extends s') : s.exns.length ≤ s'.exns.length := by
  by_contra hn
  have hi : s'.exns.length < s.exns.length := Nat.lt_of_not_ge hn
  obtain ⟨e, he, _⟩ := h.2.2.2.2.2.2.2 _ _ (List.getElem?_eq_getElem hi)
  simp only [List.getElem?_eq_none (Nat.le_refl _)] at he
  cases he

theorem funcs_get {s s' : Store} (h : s.Extends s') {a : Nat} {fi : FuncInst}
    (hf : s.funcs[a]? = some fi) : s'.funcs[a]? = some fi := by
  obtain ⟨fi', hf', he⟩ := h.1 a fi hf
  exact he ▸ hf'

theorem value {s s' : Store} (h : s.Extends s') {v : Val} {t : ValType}
    (hv : v.HasType s t) : v.HasType s' t := by
  cases v <;> cases t <;> try (cases ‹NumType› <;> exact hv)
  all_goals try exact hv
  case ref.num r n => cases r <;> cases hv
  case ref.ref r rt =>
    cases r with
    | null => exact hv
    | func a =>
      obtain ⟨fi, hf, hs⟩ := hv
      exact ⟨fi, h.funcs_get hf, hs⟩
    | extern a => exact hv
    | exn a => exact ⟨Nat.lt_of_lt_of_le hv.1 h.exns_length, hv.2⟩

theorem _root_.FVA.Wasm.Exec.Val.HasType.sub {s : Store} {v : Val} {t₁ t₂ : ValType}
    (hv : v.HasType s t₁) (h : t₁.Sub t₂) : v.HasType s t₂ := by
  cases t₁ with
  | num n₁ => cases t₂ with
    | num n₂ => cases h; exact hv
    | ref _ => exact h.elim
  | ref r₁ => cases t₂ with
    | num _ => exact h.elim
    | ref r₂ =>
      obtain ⟨hn, hh⟩ := h
      rcases r₁ with ⟨n₁, h₁⟩
      rcases r₂ with ⟨n₂, h₂⟩
      cases v with
      | ref r =>
        cases r with
        | null => exact hn hv
        | func a =>
          obtain ⟨fi, hf, hs⟩ := hv
          exact ⟨fi, hf, ValType.Sub.trans hs ⟨hn, hh⟩⟩
        | extern a =>
          simp only [Val.HasType] at hv ⊢
          rcases hh with he | ⟨d, hd, _⟩
          · simp only at he; rw [← he]; exact hv
          · simp only at hd; rw [hd] at hv; cases hv
        | exn a =>
          obtain ⟨ha, hx⟩ := hv
          refine ⟨ha, ?_⟩
          rcases hh with he | ⟨d, hd, _⟩
          · simp only at he hx ⊢; rw [← he]; exact hx
          · simp only at hd; rw [hd] at hx; cases hx
      | _ => exact hv.elim

/-- A non-null reference typed at a nullable type has the non-null one too. -/
theorem _root_.FVA.Wasm.Exec.Val.HasType.nonNull {s : Store} {r : Ref} {h : HeapType}
    (hr : r ≠ .null) (hv : Val.HasType s (.ref r) (.ref ⟨true, h⟩)) :
    Val.HasType s (.ref r) (.ref ⟨false, h⟩) := by
  cases r with
  | null => exact absurd rfl hr
  | func a =>
    obtain ⟨fi, hf, _, hh⟩ := hv
    exact ⟨fi, hf, id, hh⟩
  | extern a => exact hv
  | exn a => exact hv

theorem _root_.FVA.Wasm.Exec.Val.HasType.globalSub {s : Store} {v : Val} {g₁ g₂ : GlobalType}
    (hv : v.HasType s g₁.val) (h : g₁.Sub g₂) : v.HasType s g₂.val := by
  rcases g₂ with ⟨_ | _, t⟩
  · exact hv.sub h.2
  · exact h.2 ▸ hv

theorem values {s s' : Store} (h : s.Extends s') {vs : List Val} {ts : List ValType}
    (hv : List.Forall₂ (Val.HasType s) vs ts) : List.Forall₂ (Val.HasType s') vs ts := by
  induction hv with
  | nil => exact .nil
  | cons hv hs ih => exact .cons (h.value hv) ih

end FVA.Wasm.Exec.Store.Extends
