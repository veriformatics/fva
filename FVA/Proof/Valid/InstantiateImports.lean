import FVA.Proof.Valid.InstantiateLists
import FVA.Proof.Valid.Closed

/-!
# Imports and allocation against the module context (contract U28c V5)

Each index space of the allocated instance matches the module context: imports by
`ImportsMatch` (functions and tags by defined type, tables by closed element type, globals by
global type matching), definitions by `allocModule`'s closed types.
-/

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

theorem _root_.FVA.Wasm.GlobalType.Sub.refl (g : GlobalType) : g.Sub g := by
  rcases g with ⟨_ | _, t⟩
  · exact ⟨rfl, ValType.Sub.refl t⟩
  · exact ⟨rfl, rfl⟩

theorem import_tags {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a dt => ∃ ti, s.tags[a]? = some ti ∧ ti.type = dt)
      (ExternVal.tags imports) (importTags m.defTypes m.imports) := by
  unfold ExternVal.tags importTags
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  obtain ⟨ti, ht, hx⟩ := hm
  simp only [hx]
  exact ⟨ti, ht, rfl⟩

theorem import_funcs {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a dt => ∃ fi, s.funcs[a]? = some fi ∧ fi.type = dt)
      (ExternVal.funcs imports) (importFuncs m.defTypes m.imports) := by
  unfold ExternVal.funcs importFuncs
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  obtain ⟨fi, hf, hx⟩ := hm
  simp only [hx]
  exact ⟨fi, hf, rfl⟩

theorem import_tables {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a tt => ∃ ti, s.tables[a]? = some ti ∧ ti.type.elem = tt.elem)
      (ExternVal.tables imports) (importTables m.defTypes m.imports) := by
  unfold ExternVal.tables importTables
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  obtain ⟨ti, ht, -, he⟩ := hm
  exact ⟨ti, ht, he⟩

theorem import_mems {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a (_ : Limits) => ∃ mi, s.mems[a]? = some mi)
      (ExternVal.mems imports) (importMems m.imports) := by
  unfold ExternVal.mems importMems
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  obtain ⟨mi, hm, _⟩ := hm
  exact ⟨mi, hm⟩

theorem import_globals {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a gt => ∃ gi, s.globals[a]? = some gi ∧ gi.type.Sub gt)
      (ExternVal.globals imports) (importGlobals m.defTypes m.imports) := by
  unfold ExternVal.globals importGlobals
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial

/-- A valid module's functions and tags name existing defined types. -/
theorem defTypes_getD {m : Module} {x : Nat} {dt : DefType} (h : m.defTypes[x]? = some dt) :
    m.defTypes[x]?.getD ⟨[], 0⟩ = dt := by
  rw [h, Option.getD_some]

theorem func_type {m : Module} (hv : ModuleValid m) {fn : Func} (hfn : fn ∈ m.funcs) :
    ∃ dt, m.defTypes[fn.type]? = some dt := by
  obtain ⟨dt, hdt, -⟩ := hv.funcs fn hfn
  exact ⟨dt, hdt⟩

theorem tag_type {m : Module} (hv : ModuleValid m) {t : Tag} (ht : t ∈ m.tags) :
    ∃ dt, m.defTypes[t.type]? = some dt := by
  obtain ⟨ts, hts⟩ := hv.tags t ht
  simp only [Context.typeAt, Option.bind_eq_some_iff] at hts
  obtain ⟨dt, hdt, -⟩ := hts
  exact ⟨dt, hdt⟩

/-- Contract U28c T1: a valid module meets the source premises of closed instantiation. -/
theorem _root_.FVA.Wasm.Valid.ModuleValid.sourceOK {m : Module} (hv : ModuleValid m) :
    m.SourceOK where
  types := hv.types
  tags t ht := by
    obtain ⟨dt, hdt⟩ := tag_type hv ht
    exact lookup_lt hdt
  funcs f hf := by
    obtain ⟨dt, hdt⟩ := func_type hv hf
    exact lookup_lt hdt
  tables t ht := (hv.tables t ht).2.1
  globals g hg := by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
    exact (hv.globals k g hk).1
  elems e he := (hv.elems e he).1

/-- Contract U28c V6: every type a valid store holds is closed. -/
theorem _root_.FVA.Wasm.Valid.StoreOK.typesClosed {s : Store} (h : StoreOK s) :
    s.TypesClosed where
  tags t ht := (h.tags t ht).1
  funcs fi hfi := by
    have hok := h.funcs fi hfi
    cases fi with
    | wasm dt inst code => exact hok.1
    | host dt id => exact hok
  tables ti hti := by
    have hc := (h.tables ti hti).2.1
    generalize ti.type.elem = r at hc ⊢
    cases r
    exact hc
  globals gi hgi := (h.globals gi hgi).1
  elems ei hei := by
    have hc := (h.elems ei hei).1
    generalize ei.type = r at hc ⊢
    cases r
    exact hc

theorem map_zip_left {α β γ : Type} (f : α → γ) (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : (xs.zip ys).map (fun p => f p.1) = xs.map f := by
  change (xs.zip ys).map (f ∘ Prod.fst) = xs.map f
  rw [← List.map_map, List.map_fst_zip (Nat.le_of_eq h)]

theorem alloc_tags {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) :
    List.Forall₂ (fun a dt => ∃ ti,
      (allocModule s m imports gvals trefs erefs).1.tags[a]? = some ti ∧ ti.type = dt)
      (allocModule s m imports gvals trefs erefs).2.tags (moduleContext m).tags := by
  let build (t : Tag) : TagInst := { type := m.defTypes[t.type]?.getD ⟨[], 0⟩ }
  have hi := binding_append (tail := m.tags.map build) (import_tags hm)
  have hf := fresh_binding s.tags m.tags build TagInst.type
  have hmap : m.tags.filterMap (fun t => m.defTypes[t.type]?) =
      m.tags.map (fun t => (build t).type) :=
    filterMap_getD _ _ _ fun t ht => tag_type hv ht
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build, hmap] using both

theorem alloc_funcs {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) :
    List.Forall₂ (fun a dt => ∃ fi,
      (allocModule s m imports gvals trefs erefs).1.funcs[a]? = some fi ∧ fi.type = dt)
      (allocModule s m imports gvals trefs erefs).2.funcs (moduleContext m).funcs := by
  let inst := (allocModule s m imports gvals trefs erefs).2
  let build (fn : Func) := FuncInst.wasm (m.defTypes[fn.type]?.getD ⟨[], 0⟩) inst fn
  have hi := binding_append (tail := m.funcs.map build) (import_funcs hm)
  have hf := fresh_binding s.funcs m.funcs build FuncInst.type
  have hmap : m.funcs.filterMap (fun f => m.defTypes[f.type]?) =
      m.funcs.map (fun f => (build f).type) :=
    filterMap_getD _ _ _ fun f hf => func_type hv hf
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build, inst, hmap] using both

theorem alloc_tables {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) (ht : m.tables.length = trefs.length) :
    List.Forall₂ (fun a tt => ∃ ti,
      (allocModule s m imports gvals trefs erefs).1.tables[a]? = some ti ∧ ti.type.elem = tt.elem)
      (allocModule s m imports gvals trefs erefs).2.tables (moduleContext m).tables := by
  let closeRef (t : RefType) : RefType := ⟨t.null, closeHeap m.defTypes t.heap⟩
  let build (p : Table × Ref) : TableInst :=
    ⟨{ p.1.type with elem := closeRef p.1.type.elem }, List.replicate p.1.type.limits.min p.2⟩
  have hi := binding_append (tail := (m.tables.zip trefs).map build) (import_tables hm)
  have hf := fresh_binding s.tables (m.tables.zip trefs) build (fun ti => ti.type.elem)
  have hlen : (m.tables.zip trefs).length = m.tables.length := by simp [ht]
  have hmap : (m.tables.zip trefs).map (fun p => (build p).type.elem) =
      m.tables.map (fun t => (t.type.close m.defTypes).elem) := by
    rw [← map_zip_left (fun t : Table => (t.type.close m.defTypes).elem) _ _ ht]
    rfl
  rw [hlen, hmap] at hf
  have hf' : List.Forall₂ (fun a tt => ∃ ti,
      (s.tables ++ (m.tables.zip trefs).map build)[a]? = some ti ∧ ti.type.elem = TableType.elem tt)
      (fresh s.tables.length m.tables.length) (m.tables.map (·.type.close m.defTypes)) :=
    List.forall₂_map_right_iff.2 (List.forall₂_map_right_iff.1 hf)
  have both := List.rel_append hi hf'
  simpa only [allocModule, moduleContext, fresh, build, closeRef] using both

theorem alloc_mems {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) :
    List.Forall₂ (fun a (_ : Limits) => ∃ mi,
      (allocModule s m imports gvals trefs erefs).1.mems[a]? = some mi)
      (allocModule s m imports gvals trefs erefs).2.mems (moduleContext m).mems := by
  let build (lim : Limits) : MemInst := ⟨lim.min, lim.max, fun _ => 0⟩
  have hi : List.Forall₂ (fun a (_ : Limits) => ∃ mi,
      (s.mems ++ m.mems.map build)[a]? = some mi)
      (ExternVal.mems imports) (importMems m.imports) :=
    (import_mems hm).imp fun a lim ⟨mi, hmi⟩ => ⟨mi, lookup_append hmi⟩
  have hf : List.Forall₂ (fun a (_ : Limits) => ∃ mi,
      (s.mems ++ m.mems.map build)[a]? = some mi)
      (fresh s.mems.length m.mems.length) m.mems :=
    (fresh_lookup s.mems m.mems build).imp (fun a lim h => ⟨build lim, h⟩)
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build] using both

theorem alloc_globals_eq (s : Store) (m : Module) (imports : List ExternVal) (gvals : List Val)
    (trefs : List Ref) (erefs : List (List Ref)) :
    (allocModule s m imports gvals trefs erefs).1.globals = s.globals ++
      (m.globals.zip gvals).map fun p => (⟨p.1.type.close m.defTypes, p.2⟩ : GlobalInst) := rfl

theorem alloc_inst_globals (s : Store) (m : Module) (imports : List ExternVal) (gvals : List Val)
    (trefs : List Ref) (erefs : List (List Ref)) :
    (allocModule s m imports gvals trefs erefs).2.globals =
      ExternVal.globals imports ++ fresh s.globals.length m.globals.length := rfl

/-- The `k`-th allocated global holds the `k`-th initializer value under its closed type. -/
theorem alloc_global_lookup {s : Store} {m : Module} {imports : List ExternVal}
    (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref))
    (hg : m.globals.length = gvals.length) :
    List.Forall₂ (fun a (p : Global × Val) =>
      (allocModule s m imports gvals trefs erefs).1.globals[a]? =
        some ⟨p.1.type.close m.defTypes, p.2⟩)
      (fresh s.globals.length m.globals.length) (m.globals.zip gvals) := by
  rw [alloc_globals_eq]
  have h := fresh_lookup s.globals (m.globals.zip gvals)
    (fun p => (⟨p.1.type.close m.defTypes, p.2⟩ : GlobalInst))
  have hlen : (m.globals.zip gvals).length = m.globals.length := by simp [hg]
  rwa [hlen] at h

theorem alloc_globals {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) (hg : m.globals.length = gvals.length) :
    List.Forall₂ (fun a gt => ∃ gi,
      (allocModule s m imports gvals trefs erefs).1.globals[a]? = some gi ∧ gi.type.Sub gt)
      (allocModule s m imports gvals trefs erefs).2.globals (moduleContext m).globals := by
  have hi := binding_append
    (tail := (m.globals.zip gvals).map fun p =>
      (⟨p.1.type.close m.defTypes, p.2⟩ : GlobalInst)) (import_globals hm)
  rw [← alloc_globals_eq s m imports gvals trefs erefs] at hi
  have hf : List.Forall₂ (fun a gt => ∃ gi,
      (allocModule s m imports gvals trefs erefs).1.globals[a]? = some gi ∧ gi.type.Sub gt)
      (fresh s.globals.length m.globals.length) (m.globals.map (·.type.close m.defTypes)) := by
    have h := alloc_global_lookup (s := s) (imports := imports) gvals trefs erefs hg
    rw [← map_zip_left (fun g : Global => g.type.close m.defTypes) _ _ hg]
    apply List.forall₂_map_right_iff.mpr
    exact h.imp fun a p hp => ⟨_, hp, GlobalType.Sub.refl _⟩
  rw [alloc_inst_globals]
  exact List.rel_append hi hf

theorem alloc_elems {s : Store} {m : Module} {imports : List ExternVal}
    (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref))
    (he : m.elems.length = erefs.length) :
    List.Forall₂ (fun a rt => ∃ ei,
      (allocModule s m imports gvals trefs erefs).1.elems[a]? = some ei ∧ ei.type = rt)
      (allocModule s m imports gvals trefs erefs).2.elems (moduleContext m).elems := by
  let build (p : Elem × List Ref) : ElemInst := ⟨p.1.type.close m.defTypes, p.2⟩
  have hf := fresh_binding s.elems (m.elems.zip erefs) build ElemInst.type
  have hlen : (m.elems.zip erefs).length = m.elems.length := by simp [he]
  have hmap : (m.elems.zip erefs).map (fun p => (build p).type) =
      m.elems.map (·.type.close m.defTypes) :=
    map_zip_left (fun e : Elem => e.type.close m.defTypes) _ _ he
  rw [hlen, hmap] at hf
  simpa only [allocModule, moduleContext, fresh, build, RefType.close] using hf

end FVA.Wasm.Valid.InitProof
