import FVA.Proof.Valid.Store

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

theorem lookup_lt {α : Type} {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) :
    i < xs.length := (List.getElem?_eq_some_iff.mp h).1

theorem lookup_append {α : Type} {xs ys : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : (xs ++ ys)[i]? = some x := by
  rw [List.getElem?_append_left (lookup_lt h)]
  exact h

theorem rel_filterMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (f : α → Option γ) (g : β → Option δ)
    (hf : ∀ a b, R a b → match f a, g b with
      | none, none => True
      | some c, some d => S c d
      | _, _ => False) : List.Forall₂ S (xs.filterMap f) (ys.filterMap g) := by
  induction h with
  | nil => exact .nil
  | @cons a b xs ys hab h ih =>
    have hh := hf a b hab
    cases ha : f a <;> cases hb : g b <;> simp [ha, hb] at hh
    · simpa [List.filterMap_cons, ha, hb] using ih
    · simpa [List.filterMap_cons, ha, hb] using List.Forall₂.cons hh ih

theorem filterMap_getD {α β : Type} (f : α → Option β) (d : β) (xs : List α)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) :
    xs.filterMap f = xs.map (fun x => (f x).getD d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    simp only [List.filterMap_cons, hy, Option.getD_some, List.map_cons]
    congr 1
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem rel_imp_mem {α β : Type} {R S : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    (∀ x ∈ xs, ∀ y ∈ ys, R x y → S x y) → List.Forall₂ S xs ys := by
  induction h with
  | nil => intro _; exact .nil
  | cons hab h ih =>
    intro step
    refine .cons (step _ (by simp) _ (by simp) hab) (ih ?_)
    intro x hx y hy hxy
    exact step x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy

/-- Fresh addresses follow the occupied prefix of a store index space. -/
def fresh (base count : Nat) : List Nat := (List.range count).map (base + ·)

theorem fresh_lookup {α β : Type} (xs : List α) (ys : List β) (f : β → α) :
    List.Forall₂ (fun a y => (xs ++ ys.map f)[a]? = some (f y))
      (fresh xs.length ys.length) ys := by
  apply List.forall₂_of_length_eq_of_get
  · simp [fresh]
  · intro i hi hj
    simp only [fresh, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [List.getElem?_append_right (by omega)]
    simp [List.getElem?_map, List.getElem?_eq_getElem hj]

theorem fresh_binding {α β γ : Type} (xs : List α) (ys : List β) (f : β → α) (type : α → γ) :
    List.Forall₂ (fun a t => ∃ v, (xs ++ ys.map f)[a]? = some v ∧ type v = t)
      (fresh xs.length ys.length) (ys.map (fun y => type (f y))) := by
  apply List.forall₂_map_right_iff.mpr
  exact (fresh_lookup xs ys f).imp (fun a y h => ⟨f y, h, rfl⟩)

theorem binding_append {α β : Type} {xs tail : List α} {addrs : List Nat} {ts : List β}
    {R : α → β → Prop} (h : List.Forall₂ (fun a t => ∃ v, xs[a]? = some v ∧ R v t) addrs ts) :
    List.Forall₂ (fun a t => ∃ v, (xs ++ tail)[a]? = some v ∧ R v t) addrs ts := by
  apply h.imp
  rintro a t ⟨v, hv, ht⟩
  exact ⟨v, lookup_append hv, ht⟩

theorem extends_append {α : Type} {R : α → α → Prop} (xs ys : List α)
    (h : ∀ x, R x x) : ListExtends R xs (xs ++ ys) :=
  fun _ x hx => ⟨x, lookup_append hx, h x⟩

theorem alloc_extends (s : Store) (m : Module) (imports : List ExternVal) (gvals : List Val)
    (erefs : List (List Ref)) : s.Extends (allocModule s m imports gvals erefs).1 := by
  refine ⟨extends_append _ _ (fun _ => rfl),
    extends_append _ _ (fun _ => ⟨rfl, rfl, Nat.le_refl _⟩),
    extends_append _ _ (fun _ => ⟨rfl, Nat.le_refl _⟩),
    extends_append _ _ (fun _ => ⟨rfl, .inr rfl⟩),
    extends_append _ _ (fun _ => ⟨rfl, .inl rfl⟩),
    extends_append _ _ (fun _ => .inl rfl)⟩

theorem seq_member {C : Context} {es : List Instr} {st : StackType} (h : SeqT C es st) :
    ∀ i ∈ es, ∃ st, InstrT C i st := by
  induction h using SeqT.rec (motive_1 := fun _ _ _ _ => True) with
  | nil => simp
  | snoc hs hm hi ih _ =>
    intro i hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ih i hm
    · simp only [List.mem_singleton] at hm
      subst i
      exact ⟨_, hi⟩
  | sub hs hm ih => exact ih
  | _ => trivial

theorem refFunc_bound {C : Context} {e : Expr} {ts : List ValType} (he : ExprT C e ts)
    {x : Nat} (hx : x ∈ Expr.refFuncs e) : x < C.funcs.length := by
  obtain ⟨out, hs, _⟩ := he
  obtain ⟨i, hi, heq⟩ := List.mem_filterMap.mp hx
  cases i with
  | refFunc y =>
    cases heq
    obtain ⟨st, ht⟩ := seq_member hs (.refFunc x) hi
    cases ht with
    | refFunc hf hr => exact lookup_lt hf
  | _ => cases heq

end FVA.Wasm.Valid.InitProof
