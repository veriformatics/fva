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
type of each reference alone. Source annotations are validated by their own domain (`*.Src`:
abstract or a type index in range, never a closed form); closed types by the well-formedness
domains (`*.Closed`, 3.0 `Reftype_ok {} ⊢ rt` restricted to P′: a closed type names no source
index, `rec_ i` names a member of the enclosing group, a nested defined type is closed in its own
scope).
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

/-- `idx y` ↦ the closed reference type `def_ dts[y]` under `dts`. -/
def RefType.close (dts : List DefType) (t : RefType) : RefType := ⟨t.null, closeHeap dts t.heap⟩

/-- A table type with its element type closed under `dts`. -/
def TableType.close (dts : List DefType) (tt : TableType) : TableType :=
  { tt with elem := tt.elem.close dts }

/-- A global type with its value type closed under `dts`. -/
def GlobalType.close (dts : List DefType) (gt : GlobalType) : GlobalType :=
  ⟨gt.mutability, gt.val.mapHeap (closeHeap dts)⟩

/-- A source heap type naming one of the first `k` defined types (3.0 `Heaptype_ok`,
`Typeuse_ok/typeidx`): abstract, or a type index below `k`; source positions hold no closed form. -/
def HeapType.Src (k : Nat) : HeapType → Prop
  | .abs _ => True
  | .idx y => y < k
  | _ => False

/-- A source value type naming one of the first `k` defined types (`Valtype_ok`). -/
def ValType.Src (k : Nat) : ValType → Prop
  | .num _ => True
  | .ref t => t.heap.Src k

/-- A source function type naming one of the first `k` defined types (`Comptype_ok/func`). -/
def FuncType.Src (k : Nat) (f : FuncType) : Prop :=
  (∀ t ∈ f.params, t.Src k) ∧ ∀ t ∈ f.results, t.Src k

instance HeapType.decSrc (k : Nat) : (h : HeapType) → Decidable (h.Src k)
  | .abs _ => isTrue trivial
  | .idx y => inferInstanceAs (Decidable (y < k))
  | .def_ _ => isFalse id
  | .rec_ _ => isFalse id

instance ValType.decSrc (k : Nat) : (t : ValType) → Decidable (t.Src k)
  | .num _ => isTrue trivial
  | .ref t => HeapType.decSrc k t.heap

/-- Sequentially valid recursive groups (3.0 `Types_ok`, `Type_ok`, `Rectype_ok` with no declared
supertypes): the group at offset `x` names earlier types or members of its own group. -/
def TypesSeq : List RecType → Nat → Prop
  | [], _ => True
  | g :: gs, x => (∀ f ∈ g, f.Src (x + g.length)) ∧ TypesSeq gs (x + g.length)

mutual
/-- A heap type closed under a binder of `n` group members. -/
def HeapType.Closed (n : Nat) : HeapType → Prop
  | .abs _ => True
  | .idx _ => False
  | .def_ d => DefType.Closed d
  | .rec_ i => i < n
  termination_by structural h => h
/-- A reference type closed under `n` group members. -/
def RefType.Closed (n : Nat) : RefType → Prop
  | ⟨_, h⟩ => HeapType.Closed n h
  termination_by structural t => t
/-- A value type closed under `n` group members. -/
def ValType.Closed (n : Nat) : ValType → Prop
  | .num _ => True
  | .ref t => RefType.Closed n t
  termination_by structural t => t
/-- Value types closed under `n` group members. -/
def ValType.ClosedAll (n : Nat) : List ValType → Prop
  | [] => True
  | t :: ts => ValType.Closed n t ∧ ValType.ClosedAll n ts
  termination_by structural ts => ts
/-- A function type closed under `n` group members. -/
def FuncType.Closed (n : Nat) : FuncType → Prop
  | ⟨ps, rs⟩ => ValType.ClosedAll n ps ∧ ValType.ClosedAll n rs
  termination_by structural f => f
/-- Function types closed under `n` group members. -/
def FuncType.ClosedAll (n : Nat) : List FuncType → Prop
  | [] => True
  | f :: fs => FuncType.Closed n f ∧ FuncType.ClosedAll n fs
  termination_by structural fs => fs
/-- A closed well-formed defined type: its group closed under its own binder, its projection in
bounds. -/
def DefType.Closed : DefType → Prop
  | ⟨g, i⟩ => FuncType.ClosedAll g.length g ∧ i < g.length
  termination_by structural d => d
end

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
