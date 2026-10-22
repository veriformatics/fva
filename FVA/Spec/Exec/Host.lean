import FVA.Spec.Claims

/-!
# Valid host functions (reviewed spec)

What WebAssembly 2.0 requires of a host function (§4.4.10 + appendix "Soundness", store
extension): on every well-typed call it has at least one outcome, and every outcome is
divergence, or a trap or a result of the ascribed types in a store that extends the old one
(nothing removed, functions unchanged, sizes never shrink, immutable globals unchanged, segments
unchanged or dropped). `ValidHost H` states this for every host function of every store; a
behavioral contract (what a host such as an allocator does) is a separate hypothesis on `H`, and
never removes executions. Representation note: a table's `min` tracks its size here (growth
updates it), so a table extends another with the same element type and maximum.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- Table instance extension: same element type and maximum, no fewer elements. -/
def TableInst.Extends (t₁ t₂ : TableInst) : Prop :=
  t₂.type.elem = t₁.type.elem ∧ t₂.type.limits.max = t₁.type.limits.max ∧
    t₁.elem.length ≤ t₂.elem.length

/-- Memory instance extension: same maximum, no fewer pages. -/
def MemInst.Extends (m₁ m₂ : MemInst) : Prop :=
  m₂.max = m₁.max ∧ m₁.pages ≤ m₂.pages

/-- Global instance extension: same type; an immutable value unchanged. -/
def GlobalInst.Extends (g₁ g₂ : GlobalInst) : Prop :=
  g₂.type = g₁.type ∧ (g₁.type.mutability = .var ∨ g₂.value = g₁.value)

/-- Element instance extension: unchanged or dropped. -/
def ElemInst.Extends (e₁ e₂ : ElemInst) : Prop :=
  e₂.type = e₁.type ∧ (e₂.elem = e₁.elem ∨ e₂.elem = [])

/-- Data instance extension: unchanged or dropped. -/
def DataInst.Extends (d₁ d₂ : DataInst) : Prop :=
  d₂.data = d₁.data ∨ d₂.data = []

/-- `xs₂` keeps every entry of `xs₁` extended by `R`, possibly with more after them. -/
def ListExtends {α : Type} (R : α → α → Prop) (xs₁ xs₂ : List α) : Prop :=
  ∀ (i : Nat) (x : α), xs₁[i]? = some x → ∃ y, xs₂[i]? = some y ∧ R x y

/-- Store extension `S₁ ⪯ S₂` (appendix "Soundness"). -/
def Store.Extends (s₁ s₂ : Store) : Prop :=
  ListExtends (· = ·) s₁.funcs s₂.funcs ∧ ListExtends TableInst.Extends s₁.tables s₂.tables ∧
  ListExtends MemInst.Extends s₁.mems s₂.mems ∧
  ListExtends GlobalInst.Extends s₁.globals s₂.globals ∧
  ListExtends ElemInst.Extends s₁.elems s₂.elems ∧ ListExtends DataInst.Extends s₁.datas s₂.datas

/-- A host outcome allowed for a call with result types `ts` from store `s`. -/
def HostOutcome.Allowed (s : Store) (ts : List ValType) : HostOutcome → Prop
  | .returned s' vs => Store.Extends s s' ∧ List.Forall₂ (Val.HasType s') vs ts
  | .trapped s' => Store.Extends s s'
  | .diverged => True

/-- Every host function, called with arguments of its parameter types, has an outcome, and only
allowed ones. -/
def ValidHost (H : HostSem) : Prop :=
  ∀ (s : Store) (a : Nat) (ft : FuncType) (id : Nat) (args : List Val),
    s.funcs[a]? = some (FuncInst.host ft id) →
    List.Forall₂ (Val.HasType s) args ft.params →
      (∃ o, H id s args o) ∧ ∀ o, H id s args o → o.Allowed s ft.results

end FVA.Wasm.Exec
