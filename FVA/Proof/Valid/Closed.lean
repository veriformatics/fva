import FVA.Spec.Exec.Instantiate

/-!
# Closed types (contract U28b T6, U28a A2)

The well-formedness domains of closed types: a closed type names no source index; inside a rolled
group, `rec_ i` names a member (`i` below the group's size, the binder `n`); a nested defined type
is closed in its own scope (its group under its own binder, its projection in bounds). Closure
(`Module.defTypes`) establishes them from sequentially valid source groups (each index names an
earlier type or a member of its own group), unrolling (`DefType.expand`) keeps them, and
instantiation enters only closed types into the store and the instance (`allocModule_closed`)
when the source annotations name existing types. The identities consumers use: closure is the
identity on closed terms, and a singleton group whose member names no group member expands to that
member. U28c's validator supplies the source premises (`Module.SourceOK`).
-/

namespace FVA.Wasm

open Exec

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

theorem ValType.closedAll_iff {n : Nat} : ∀ {ts : List ValType},
    ValType.ClosedAll n ts ↔ ∀ t ∈ ts, t.Closed n
  | [] => by simp [ValType.ClosedAll]
  | t :: ts => by simp [ValType.ClosedAll, ValType.closedAll_iff]

theorem FuncType.closedAll_iff {n : Nat} : ∀ {fs : List FuncType},
    FuncType.ClosedAll n fs ↔ ∀ f ∈ fs, f.Closed n
  | [] => by simp [FuncType.ClosedAll]
  | f :: fs => by simp [FuncType.ClosedAll, FuncType.closedAll_iff]

theorem FuncType.closed_iff {n : Nat} {f : FuncType} :
    f.Closed n ↔ (∀ t ∈ f.params, t.Closed n) ∧ ∀ t ∈ f.results, t.Closed n := by
  rcases f with ⟨ps, rs⟩
  simp only [FuncType.Closed, ValType.closedAll_iff]

theorem DefType.closed_iff {d : DefType} :
    d.Closed ↔ (∀ f ∈ d.group, f.Closed d.group.length) ∧ d.idx < d.group.length := by
  rcases d with ⟨g, i⟩
  simp only [DefType.Closed, FuncType.closedAll_iff]

/-! ## Substitution on the top-level heap types -/

theorem map_eq_self' {α : Type} {f : α → α} : ∀ {l : List α}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, h x (by simp), map_eq_self' fun y hy => h y (by simp [hy])]

/-- `σ` maps every heap type closed under `n` to one closed under `m`. -/
def HeapMap (n m : Nat) (σ : HeapType → HeapType) : Prop :=
  ∀ h, HeapType.Closed n h → HeapType.Closed m (σ h)

theorem ValType.closed_mapHeap {n m : Nat} {σ : HeapType → HeapType} (hσ : HeapMap n m σ)
    {t : ValType} (ht : t.Closed n) : (t.mapHeap σ).Closed m := by
  cases t with
  | num _ => trivial
  | ref r =>
    rcases r with ⟨b, h⟩
    exact hσ h ht

theorem FuncType.closed_mapHeap {n m : Nat} {σ : HeapType → HeapType} (hσ : HeapMap n m σ)
    {f : FuncType} (hf : f.Closed n) : (f.mapHeap σ).Closed m := by
  rw [FuncType.closed_iff] at hf ⊢
  simp only [FuncType.mapHeap, List.mem_map]
  exact ⟨by rintro _ ⟨t, ht, rfl⟩; exact ValType.closed_mapHeap hσ (hf.1 t ht),
    by rintro _ ⟨t, ht, rfl⟩; exact ValType.closed_mapHeap hσ (hf.2 t ht)⟩

/-- A substitution acting on `rec_` alone fixes every heap type closed under no binder. -/
theorem ValType.mapHeap_closed_zero {σ : HeapType → HeapType}
    (hσ : ∀ h, (∀ i, h ≠ .rec_ i) → σ h = h) {t : ValType} (ht : t.Closed 0) : t.mapHeap σ = t := by
  cases t with
  | num _ => rfl
  | ref r =>
    rcases r with ⟨b, h⟩
    have hh : ∀ i, h ≠ .rec_ i := by
      rintro i rfl
      exact absurd ht (by simp [ValType.Closed, RefType.Closed, HeapType.Closed])
    simp only [ValType.mapHeap, hσ h hh]

theorem FuncType.mapHeap_closed_zero {σ : HeapType → HeapType}
    (hσ : ∀ h, (∀ i, h ≠ .rec_ i) → σ h = h) {f : FuncType} (hf : f.Closed 0) :
    f.mapHeap σ = f := by
  rcases f with ⟨ps, rs⟩
  rw [FuncType.closed_iff] at hf
  simp only [FuncType.mapHeap, FuncType.mk.injEq]
  exact ⟨map_eq_self' fun t ht => ValType.mapHeap_closed_zero hσ (hf.1 t ht),
    map_eq_self' fun t ht => ValType.mapHeap_closed_zero hσ (hf.2 t ht)⟩

/-! ## Unrolling -/

/-- `$unrolldt`'s substitution for group `g`: `rec_ j` ↦ the group's `j`-th defined type. -/
def unrollHeap (g : List FuncType) : HeapType → HeapType
  | .rec_ j => .def_ ⟨g, j⟩
  | ht => ht

theorem expand_eq (d : DefType) :
    d.expand = d.group[d.idx]?.map (·.mapHeap (unrollHeap d.group)) := by
  unfold DefType.expand unrollHeap
  rfl

/-- Unrolling keeps closed well-formed types: a closed defined type expands, to a function type
closed under no binder. -/
theorem DefType.expand_closed {d : DefType} (hd : d.Closed) :
    ∃ f, d.expand = some f ∧ f.Closed 0 := by
  rw [DefType.closed_iff] at hd
  obtain ⟨hg, hi⟩ := hd
  refine ⟨(d.group[d.idx]'hi).mapHeap (unrollHeap d.group), ?_, ?_⟩
  · rw [expand_eq, List.getElem?_eq_getElem hi]
    rfl
  · refine FuncType.closed_mapHeap (n := d.group.length) ?_ (hg _ (List.getElem_mem hi))
    intro h hh
    cases h with
    | abs _ => trivial
    | idx _ => exact hh
    | def_ e => exact hh
    | rec_ j =>
      show DefType.Closed ⟨d.group, j⟩
      exact DefType.closed_iff.mpr ⟨hg, hh⟩

/-- A singleton group whose member names no group member expands to that member. -/
theorem DefType.expand_singleton {f : FuncType} (hf : f.Closed 0) :
    DefType.expand ⟨[f], 0⟩ = some f := by
  rw [expand_eq]
  simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq]
  exact FuncType.mapHeap_closed_zero (fun h hh => by cases h <;> simp_all [unrollHeap]) hf

/-- The negative API case of A2: a singleton group naming member 1 is no closed type. -/
theorem not_closed_rec_out_of_group :
    ¬ DefType.Closed ⟨[⟨[.ref ⟨true, .rec_ 1⟩], []⟩], 0⟩ := by
  simp [DefType.Closed, FuncType.ClosedAll, FuncType.Closed, ValType.ClosedAll, ValType.Closed,
    RefType.Closed, HeapType.Closed]

/-! ## Closure -/

/-- A source heap type naming one of the first `k` types: abstract or an index below `k`. -/
def HeapType.Src (k : Nat) : HeapType → Prop
  | .abs _ => True
  | .idx y => y < k
  | _ => False

/-- A source value type naming one of the first `k` types. -/
def ValType.Src (k : Nat) : ValType → Prop
  | .num _ => True
  | .ref t => t.heap.Src k

/-- A source function type naming one of the first `k` types. -/
def FuncType.Src (k : Nat) (f : FuncType) : Prop :=
  (∀ t ∈ f.params, t.Src k) ∧ ∀ t ∈ f.results, t.Src k

theorem ValType.closed_mapHeap_src {k n : Nat} {σ : HeapType → HeapType}
    (hσ : ∀ h, h.Src k → (σ h).Closed n) {t : ValType} (ht : t.Src k) :
    (t.mapHeap σ).Closed n := by
  cases t with
  | num _ => trivial
  | ref r =>
    rcases r with ⟨b, h⟩
    exact hσ h ht

theorem FuncType.closed_mapHeap_src {k n : Nat} {σ : HeapType → HeapType}
    (hσ : ∀ h, h.Src k → (σ h).Closed n) {f : FuncType} (hf : f.Src k) :
    (f.mapHeap σ).Closed n := by
  rw [FuncType.closed_iff]
  simp only [FuncType.mapHeap, List.mem_map]
  exact ⟨by rintro _ ⟨t, ht, rfl⟩; exact ValType.closed_mapHeap_src hσ (hf.1 t ht),
    by rintro _ ⟨t, ht, rfl⟩; exact ValType.closed_mapHeap_src hσ (hf.2 t ht)⟩

/-- Closure is the identity on every closed heap type (it replaces source indices alone). -/
theorem closeHeap_closed {dts : List DefType} {n : Nat} {h : HeapType} (hh : h.Closed n) :
    closeHeap dts h = h := by
  cases h with
  | idx _ => exact absurd hh (by simp [HeapType.Closed])
  | _ => rfl

/-- Closure under closed defined types closes every source heap type naming one of them. -/
theorem closed_closeHeap {dts : List DefType} (hd : ∀ d ∈ dts, d.Closed) {n : Nat}
    {h : HeapType} (hh : h.Src dts.length) : (closeHeap dts h).Closed n := by
  cases h with
  | abs _ => trivial
  | idx y =>
    simp only [HeapType.Src] at hh
    simp only [closeHeap, List.getElem?_eq_getElem hh, Option.map_some, Option.getD_some,
      HeapType.Closed]
    exact hd _ (List.getElem_mem hh)
  | _ => exact absurd hh (by simp [HeapType.Src])

theorem ValType.closed_close {dts : List DefType} (hd : ∀ d ∈ dts, d.Closed) {n : Nat}
    {t : ValType} (ht : t.Src dts.length) : (t.mapHeap (closeHeap dts)).Closed n :=
  ValType.closed_mapHeap_src (fun _ hh => closed_closeHeap hd hh) ht

/-- The roll of group `g` at offset `|dts|` (`Module.defTypes`' substitution). -/
def rollHeap (dts : List DefType) (n : Nat) : HeapType → HeapType
  | .idx y => if dts.length ≤ y ∧ y < dts.length + n then .rec_ (y - dts.length)
    else closeHeap dts (.idx y)
  | ht => ht

/-- Rolling a group of `n` members at offset `|dts|` closes each source heap type naming an
earlier type or a member under the group's binder. -/
theorem closed_rollHeap {dts : List DefType} (hd : ∀ d ∈ dts, d.Closed) {n : Nat}
    {h : HeapType} (hh : h.Src (dts.length + n)) : (rollHeap dts n h).Closed n := by
  cases h with
  | abs _ => trivial
  | idx y =>
    simp only [HeapType.Src] at hh
    simp only [rollHeap]
    split
    · rename_i hy
      simp only [HeapType.Closed]
      omega
    · rename_i hy
      exact closed_closeHeap hd (by simp only [HeapType.Src]; omega)
  | _ => exact absurd hh (by simp [HeapType.Src])

/-- Sequentially valid source groups (SpecTec `2.4`): each group's types name earlier types or
members of the group. -/
def TypesSeq : List RecType → Nat → Prop
  | [], _ => True
  | g :: gs, x => (∀ f ∈ g, f.Src (x + g.length)) ∧ TypesSeq gs (x + g.length)

theorem defTypes_step_eq (dts : List DefType) (g : RecType) :
    (let roll : HeapType → HeapType
      | .idx y => if dts.length ≤ y ∧ y < dts.length + g.length then .rec_ (y - dts.length)
        else closeHeap dts (.idx y)
      | ht => ht
     dts ++ (List.range g.length).map fun i => (⟨g.map (·.mapHeap roll), i⟩ : DefType)) =
    dts ++ (List.range g.length).map fun i => ⟨g.map (·.mapHeap (rollHeap dts g.length)), i⟩ := by
  rfl

/-- Closure establishes the domains: from sequentially valid groups, every defined type of the
module is closed and well-formed. -/
theorem defTypes_closed {m : Module} (hm : TypesSeq m.types 0) : ∀ d ∈ m.defTypes, d.Closed := by
  unfold Module.defTypes
  suffices ∀ (gs : List RecType) (dts : List DefType), (∀ d ∈ dts, d.Closed) →
      TypesSeq gs dts.length → ∀ d ∈ gs.foldl (fun dts g =>
        let roll : HeapType → HeapType
          | .idx y => if dts.length ≤ y ∧ y < dts.length + g.length then .rec_ (y - dts.length)
            else closeHeap dts (.idx y)
          | ht => ht
        dts ++ (List.range g.length).map fun i => ⟨g.map (·.mapHeap roll), i⟩) dts, d.Closed from
    this m.types [] (by simp) hm
  intro gs
  induction gs with
  | nil => intro dts hd _; simpa using hd
  | cons g gs ih =>
    intro dts hd hs
    obtain ⟨hg, hgs⟩ := hs
    rw [List.foldl_cons, defTypes_step_eq]
    refine ih _ ?_ (by simpa using hgs)
    intro d hd'
    rcases List.mem_append.mp hd' with hd' | hd'
    · exact hd d hd'
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd'
      rw [List.mem_range] at hi
      refine DefType.closed_iff.mpr ⟨?_, by simpa using hi⟩
      simp only [List.length_map, List.mem_map]
      rintro _ ⟨f, hf, rfl⟩
      exact FuncType.closed_mapHeap_src (fun _ hh => closed_rollHeap hd hh) (hg f hf)

/-! ## Entry points -/

/-- The source premises of closed instantiation (U28c's validator supplies them): sequentially
valid groups; every tag and function names an existing type; every table, global and element
annotation names existing types. -/
structure Module.SourceOK (m : Module) : Prop where
  types : TypesSeq m.types 0
  tags : ∀ t ∈ m.tags, t.type < m.defTypes.length
  funcs : ∀ f ∈ m.funcs, f.type < m.defTypes.length
  tables : ∀ t ∈ m.tables, t.type.elem.heap.Src m.defTypes.length
  globals : ∀ g ∈ m.globals, g.type.val.Src m.defTypes.length
  elems : ∀ e ∈ m.elems, e.type.heap.Src m.defTypes.length

/-- Every type a store holds is closed: tag + function types closed well-formed defined types,
table, global and element types closed under no binder. -/
structure Exec.Store.TypesClosed (s : Store) : Prop where
  tags : ∀ t ∈ s.tags, t.type.Closed
  funcs : ∀ fi ∈ s.funcs, fi.type.Closed
  tables : ∀ ti ∈ s.tables, ti.type.elem.heap.Closed 0
  globals : ∀ gi ∈ s.globals, gi.type.val.Closed 0
  elems : ∀ ei ∈ s.elems, ei.type.heap.Closed 0

theorem getD_closed {dts : List DefType} (hd : ∀ d ∈ dts, d.Closed) {x : Nat}
    (hx : x < dts.length) : (dts[x]?.getD ⟨[], 0⟩).Closed := by
  rw [List.getElem?_eq_getElem hx, Option.getD_some]
  exact hd _ (List.getElem_mem hx)

/-- Instantiation enters closed types alone: from a store whose types are closed and a module
meeting the source premises, the store after `allocModule` holds closed types and the instance's
defined types are closed. -/
theorem allocModule_closed {s : Store} {m : Module} {imports : List ExternVal}
    {gvals : List Val} {trefs : List Ref} {erefs : List (List Ref)} (hs : s.TypesClosed)
    (hm : m.SourceOK) :
    (allocModule s m imports gvals trefs erefs).1.TypesClosed ∧
      ∀ d ∈ (allocModule s m imports gvals trefs erefs).2.types, d.Closed := by
  have hd := defTypes_closed hm.types
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hd⟩
  · intro t ht
    simp only [allocModule, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨tg, htg, rfl⟩
    · exact hs.tags t ht
    · exact getD_closed hd (hm.tags tg htg)
  · intro fi hfi
    simp only [allocModule, List.mem_append, List.mem_map] at hfi
    rcases hfi with hfi | ⟨fn, hfn, rfl⟩
    · exact hs.funcs fi hfi
    · exact getD_closed hd (hm.funcs fn hfn)
  · intro ti hti
    simp only [allocModule, List.mem_append, List.mem_map] at hti
    rcases hti with hti | ⟨⟨t, r⟩, htr, rfl⟩
    · exact hs.tables ti hti
    · exact closed_closeHeap hd (hm.tables t (List.of_mem_zip htr).1)
  · intro gi hgi
    simp only [allocModule, List.mem_append, List.mem_map] at hgi
    rcases hgi with hgi | ⟨⟨g, v⟩, hgv, rfl⟩
    · exact hs.globals gi hgi
    · exact ValType.closed_close hd (hm.globals g (List.of_mem_zip hgv).1)
  · intro ei hei
    simp only [allocModule, List.mem_append, List.mem_map] at hei
    rcases hei with hei | ⟨⟨e, rs⟩, hers, rfl⟩
    · exact hs.elems ei hei
    · exact closed_closeHeap hd (hm.elems e (List.of_mem_zip hers).1)

end FVA.Wasm
