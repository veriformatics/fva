import FVA.Spec.Valid.Module

/-!
# Closed types of a 2.0-profile module

A module of the 2.0 profile (`Module.inP2`, `ModuleValid.profile` until U28c) has one-member type
groups of 2.0 function types, so closure is the identity on it: each defined type expands to its
source function type, and every annotation closes to itself.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

theorem map_eq_self {α : Type} {f : α → α} : ∀ {l : List α}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, h x (by simp), map_eq_self fun y hy => h y (by simp [hy])]

/-- The structures of the mutual type family have no definitional eta. -/
theorem _root_.FVA.Wasm.RefType.eta (t : RefType) : (⟨t.null, t.heap⟩ : RefType) = t := by
  cases t; rfl

theorem _root_.FVA.Wasm.HeapType.eq_abs_of_inP2 {h : HeapType} (hh : h.inP2 = true) :
    ∃ a, h = .abs a := by
  cases h with
  | abs a => exact ⟨a, rfl⟩
  | _ => simp [HeapType.inP2] at hh

@[simp] theorem closeHeap_abs (dts : List DefType) (a : AbsHeapType) :
    closeHeap dts (.abs a) = .abs a := rfl

/-- A substitution fixing the abstract heap types fixes every 2.0 value type. -/
theorem _root_.FVA.Wasm.ValType.mapHeap_of_inP2 {σ : HeapType → HeapType}
    (hσ : ∀ a, σ (.abs a) = .abs a) {t : ValType} (ht : t.inP2 = true) : t.mapHeap σ = t := by
  cases t with
  | num _ => rfl
  | ref r =>
    rcases r with ⟨n, h⟩
    simp only [ValType.inP2, Bool.and_eq_true] at ht
    obtain ⟨a, rfl⟩ := HeapType.eq_abs_of_inP2 ht.2
    simp only [ValType.mapHeap, hσ]

/-- A function type of the 2.0 profile. -/
def _root_.FVA.Wasm.FuncType.InP2 (f : FuncType) : Prop :=
  (∀ t ∈ f.params, t.inP2 = true) ∧ ∀ t ∈ f.results, t.inP2 = true

theorem _root_.FVA.Wasm.FuncType.mapHeap_of_inP2 {σ : HeapType → HeapType}
    (hσ : ∀ a, σ (.abs a) = .abs a) {f : FuncType} (hf : f.InP2) : f.mapHeap σ = f := by
  rcases f with ⟨ps, rs⟩
  simp only [FuncType.mapHeap]
  rw [map_eq_self fun t ht => ValType.mapHeap_of_inP2 hσ (hf.1 t ht),
    map_eq_self fun t ht => ValType.mapHeap_of_inP2 hσ (hf.2 t ht)]

/-- `Module.inP2`, field by field. -/
structure ModuleInP2 (m : Module) : Prop where
  types : ∀ g ∈ m.types, ∃ f, g = [f] ∧ f.InP2
  noTags : m.tags = []
  imports : ∀ im ∈ m.imports, match im.desc with
    | .table tt => ValType.inP2 (.ref tt.elem) = true
    | .global gt => gt.val.inP2 = true
    | .tag _ => False
    | _ => True
  tables : ∀ t ∈ m.tables, ∃ a, t.type.elem = ⟨true, .abs a⟩ ∧ (HeapType.abs a).inP2 = true ∧
    t.init = [.refNull (.abs a)]
  globals : ∀ g ∈ m.globals, g.type.val.inP2 = true
  elems : ∀ e ∈ m.elems, e.type.heap.inP2 = true

theorem _root_.FVA.Wasm.Module.inP2_spec {m : Module} (h : m.inP2 = true) : ModuleInP2 m := by
  simp only [Module.inP2, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htypes, htags⟩, himports⟩, htables⟩, -⟩, hglobals⟩, helems⟩, -⟩, -⟩ := h
  refine ⟨?_, htags, ?_, ?_, fun g hg => (hglobals g hg).1, fun e he => (helems e he).1.1.1⟩
  · intro g hg
    have hg := htypes g hg
    rcases g with _ | ⟨f, _ | ⟨_, _⟩⟩
    · simp at hg
    · simp only [Bool.and_eq_true, List.all_eq_true] at hg
      exact ⟨f, rfl, hg.1, hg.2⟩
    · simp at hg
  · intro im him
    have hi := himports im him
    split <;> simp_all
  · intro t ht
    obtain ⟨hr, hi⟩ := htables t ht
    rcases hte : t.type.elem with ⟨n, h⟩
    simp only [hte, ValType.inP2, Bool.and_eq_true] at hr hi
    split at hi
    · simp only [beq_iff_eq] at hi
      subst_vars
      exact ⟨_, by rw [hr.1], hr.2, ‹_›⟩
    · simp at hi

theorem _root_.FVA.Wasm.ValType.Sub.refl (t : ValType) : t.Sub t := by
  cases t with
  | num _ => exact rfl
  | ref _ => exact ⟨id, .inl rfl⟩

theorem _root_.FVA.Wasm.GlobalType.Sub.refl (g : GlobalType) : g.Sub g := by
  rcases g with ⟨_ | _, t⟩
  · exact ⟨rfl, ValType.Sub.refl t⟩
  · exact ⟨rfl, rfl⟩

theorem foldl_append_map {β γ : Type} {F : List β → γ → List β} {G : γ → β} {P : γ → Prop}
    (hF : ∀ acc g, P g → F acc g = acc ++ [G g]) :
    ∀ (gs : List γ) (acc : List β), (∀ g ∈ gs, P g) → gs.foldl F acc = acc ++ gs.map G
  | [], acc, _ => by simp
  | g :: gs, acc, h => by
    rw [List.foldl_cons, hF acc g (h g (by simp)),
      foldl_append_map hF gs _ fun x hx => h x (by simp [hx])]
    simp

/-- One-member groups of 2.0 function types roll to themselves. -/
theorem defTypes_of_inP2 {m : Module} (h : ∀ g ∈ m.types, ∃ f, g = [f] ∧ f.InP2) :
    m.defTypes = m.types.map fun g => ⟨g, 0⟩ := by
  unfold Module.defTypes
  rw [foldl_append_map (G := fun g => ⟨g, 0⟩) (P := fun g => ∃ f, g = [f] ∧ f.InP2) ?_ _ _ h]
  · simp
  · rintro acc g ⟨f, rfl, hf⟩
    simp only [List.length_singleton, List.range_one, List.map_cons, List.map_nil]
    rw [FuncType.mapHeap_of_inP2 (fun _ => rfl) hf]

theorem expand_singleton {f : FuncType} (hf : f.InP2) : DefType.expand ⟨[f], 0⟩ = some f := by
  simp only [DefType.expand, List.getElem?_cons_zero, Option.map_some]
  rw [FuncType.mapHeap_of_inP2 (fun _ => rfl) hf]

/-- The defined types of a 2.0-profile module expand to its function types. -/
theorem forall₂_defTypes {m : Module} (h : ∀ g ∈ m.types, ∃ f, g = [f] ∧ f.InP2) :
    List.Forall₂ (fun dt ft => dt.expand = some ft) m.defTypes m.typeList := by
  rw [defTypes_of_inP2 h, Module.typeList]
  suffices ∀ gs : List RecType, (∀ g ∈ gs, ∃ f, g = [f] ∧ f.InP2) →
      List.Forall₂ (fun (dt : DefType) (ft : FuncType) => dt.expand = some ft)
        (gs.map fun g => ⟨g, 0⟩) gs.flatten from
    this _ h
  intro gs hgs
  induction gs with
  | nil => exact .nil
  | cons g gs ih =>
    obtain ⟨f, rfl, hf⟩ := hgs g (by simp)
    exact .cons (expand_singleton hf) (ih fun g' hg' => hgs g' (by simp [hg']))

end FVA.Wasm.Valid
