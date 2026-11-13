import FVA.Spec.Syntax

/-!
# Closed types (reviewed spec)

Wasm 3.0 SpecTec `859d3232` `1.2` (rolling, unrolling, substitution) and `4.4` `$alloctypes` for
profile P′'s recursive groups of final function types without supertypes. A source type names a
defined type by type index (`idx`); closure replaces each index by its defined type (`def_`), and
inside a recursive group the group's own members by their position (`rec_`, `$rollrt`). A closed
defined type is its rolled group + a projection, so two defined types are the same type exactly
when they are equal terms. A substitution never enters a `def_`: its contents are closed already
(SpecTec drops `REC` substitutions under a rectype), so every substitution here acts on the heap
type of each reference alone.
-/

namespace FVA.Wasm

/-- `σ` on the heap type of a value type's reference. -/
def ValType.mapHeap (σ : HeapType → HeapType) : ValType → ValType
  | .num t => .num t
  | .ref t => .ref ⟨t.null, σ t.heap⟩

/-- `σ` on the heap type of every reference in a function type. -/
def FuncType.mapHeap (σ : HeapType → HeapType) (f : FuncType) : FuncType :=
  ⟨f.params.map (·.mapHeap σ), f.results.map (·.mapHeap σ)⟩

/-- Closure under the defined types `dts` (`$subst_all_*`): `idx y` ↦ `def_ dts[y]`; an index
past `dts` stays (only an invalid module has one). -/
def closeHeap (dts : List DefType) : HeapType → HeapType
  | .idx y => (dts[y]?.map .def_).getD (.idx y)
  | ht => ht

/-- A module's defined types (`$alloctypes`): the group `g` at type index `x` (the number of
earlier types) rolled — its own indices `x … x+|g|-1` ↦ `rec_ 0 … rec_ (|g|-1)` (`$rollrt`) —
and closed under the earlier ones; one defined type per member (`$rolldt`). -/
def Module.defTypes (m : Module) : List DefType :=
  m.types.foldl (fun dts g =>
    let roll : HeapType → HeapType
      | .idx y => if dts.length ≤ y ∧ y < dts.length + g.length then .rec_ (y - dts.length)
        else closeHeap dts (.idx y)
      | ht => ht
    dts ++ (List.range g.length).map fun i => ⟨g.map (·.mapHeap roll), i⟩) []

/-- P′ subtyping of closed value types (3.0 `2.2` without GC): a number type is below itself; a
reference type below another when nullability does not grow and the heap type is the same or a
defined type below `func` (every P′ defined type is a function type). -/
def ValType.Sub : ValType → ValType → Prop
  | .num a, .num b => a = b
  | .ref t₁, .ref t₂ => (t₁.null = true → t₂.null = true) ∧
      (t₁.heap = t₂.heap ∨ ∃ d, t₁.heap = .def_ d ∧ t₂.heap = .abs .func)
  | _, _ => False

/-- Global type matching (3.0 `Globaltype_sub`): the same mutability; an immutable global's value
type below the expected one, a mutable global's equal (subtyping both ways). -/
def GlobalType.Sub (g₁ g₂ : GlobalType) : Prop :=
  g₁.mutability = g₂.mutability ∧ match g₂.mutability with
    | .var => g₁.val = g₂.val
    | .const => g₁.val.Sub g₂.val

/-- A defined type's function type (`$unrolldt` + `Expand`): its member, each `rec_ j` ↦ the
group's `j`-th defined type; `none` for a projection outside the group. -/
def DefType.expand (d : DefType) : Option FuncType :=
  d.group[d.idx]?.map (·.mapHeap fun | .rec_ j => .def_ ⟨d.group, j⟩ | ht => ht)

end FVA.Wasm
