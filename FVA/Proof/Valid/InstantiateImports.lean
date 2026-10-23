import FVA.Proof.Valid.InstantiateLists

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

theorem import_funcs {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a ft => ∃ fi, s.funcs[a]? = some fi ∧ fi.type = ft)
      (ExternVal.funcs imports) (importFuncs { types := m.types } m.imports) := by
  unfold ExternVal.funcs importFuncs
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  rename_i a x
  obtain ⟨fi, ft, hf, ht, he⟩ := hm
  simp only [ht]
  exact ⟨fi, hf, he⟩

theorem import_tables {s : Store} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a tt => ∃ ti, s.tables[a]? = some ti ∧ ti.type.elem = tt.elem)
      (ExternVal.tables imports) (importTables m.imports) := by
  unfold ExternVal.tables importTables
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  obtain ⟨ti, ht, _, he⟩ := hm
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
    List.Forall₂ (fun a gt => ∃ gi, s.globals[a]? = some gi ∧ gi.type = gt)
      (ExternVal.globals imports) (importGlobals m.imports) := by
  unfold ExternVal.globals importGlobals
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial

theorem funcTypes_map {m : Module} (h : ModuleValid m) :
    m.funcs.filterMap (fun f => m.types[f.type]?) =
      m.funcs.map (fun f => (m.types[f.type]?).getD ⟨[], []⟩) := by
  apply filterMap_getD
  intro f hf
  exact ⟨_, List.getElem?_eq_getElem (h.funcTypes f hf)⟩

theorem alloc_funcs {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val)
    (erefs : List (List Ref)) :
    List.Forall₂ (fun a ft => ∃ fi,
      (allocModule s m imports gvals erefs).1.funcs[a]? = some fi ∧ fi.type = ft)
      (allocModule s m imports gvals erefs).2.funcs (moduleContext m).funcs := by
  let inst := (allocModule s m imports gvals erefs).2
  let build (fn : Func) := FuncInst.wasm (m.types[fn.type]?.getD ⟨[], []⟩) inst fn
  have hi := binding_append (tail := m.funcs.map build) (import_funcs hm)
  have hf := fresh_binding s.funcs m.funcs build FuncInst.type
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build, inst, FuncInst.type, funcTypes_map hv]
    using both

theorem alloc_tables {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) (gvals : List Val) (erefs : List (List Ref)) :
    List.Forall₂ (fun a tt => ∃ ti,
      (allocModule s m imports gvals erefs).1.tables[a]? = some ti ∧ ti.type.elem = tt.elem)
      (allocModule s m imports gvals erefs).2.tables (moduleContext m).tables := by
  let build (tt : TableType) : TableInst :=
    ⟨tt, List.replicate tt.limits.min (.null tt.elem)⟩
  have hi := binding_append (tail := m.tables.map build) (import_tables hm)
  have hf : List.Forall₂ (fun a tt => ∃ ti,
      (s.tables ++ m.tables.map build)[a]? = some ti ∧ ti.type.elem = tt.elem)
      (fresh s.tables.length m.tables.length) m.tables :=
    (fresh_lookup s.tables m.tables build).imp (fun a tt h => ⟨build tt, h, rfl⟩)
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build] using both

theorem alloc_mems {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) (gvals : List Val) (erefs : List (List Ref)) :
    List.Forall₂ (fun a (_ : Limits) => ∃ mi,
      (allocModule s m imports gvals erefs).1.mems[a]? = some mi)
      (allocModule s m imports gvals erefs).2.mems (moduleContext m).mems := by
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

theorem map_zip_left {α β γ : Type} (f : α → γ) (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : (xs.zip ys).map (fun p => f p.1) = xs.map f := by
  change (xs.zip ys).map (f ∘ Prod.fst) = xs.map f
  rw [← List.map_map, List.map_fst_zip (Nat.le_of_eq h)]

theorem alloc_globals {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) (gvals : List Val) (erefs : List (List Ref))
    (hg : m.globals.length = gvals.length) :
    List.Forall₂ (fun a gt => ∃ gi,
      (allocModule s m imports gvals erefs).1.globals[a]? = some gi ∧ gi.type = gt)
      (allocModule s m imports gvals erefs).2.globals (moduleContext m).globals := by
  let build (p : Global × Val) : GlobalInst := ⟨p.1.type, p.2⟩
  have hi := binding_append (tail := (m.globals.zip gvals).map build) (import_globals hm)
  have hf := fresh_binding s.globals (m.globals.zip gvals) build GlobalInst.type
  have hlen : (m.globals.zip gvals).length = m.globals.length := by simp [hg]
  have hmap : (m.globals.zip gvals).map (fun p => (build p).type) =
      m.globals.map (·.type) := map_zip_left (fun g : Global => g.type) _ _ hg
  rw [hlen, hmap] at hf
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build] using both

theorem alloc_elems (s : Store) (m : Module) (imports : List ExternVal)
    (gvals : List Val) (erefs : List (List Ref)) (he : m.elems.length = erefs.length) :
    List.Forall₂ (fun a rt => ∃ ei,
      (allocModule s m imports gvals erefs).1.elems[a]? = some ei ∧ ei.type = rt)
      (allocModule s m imports gvals erefs).2.elems (moduleContext m).elems := by
  let build (p : Elem × List Ref) : ElemInst := ⟨p.1.type, p.2⟩
  have hf := fresh_binding s.elems (m.elems.zip erefs) build ElemInst.type
  have hlen : (m.elems.zip erefs).length = m.elems.length := by simp [he]
  have hmap : (m.elems.zip erefs).map (fun p => (build p).type) =
      m.elems.map (·.type) := map_zip_left (fun e : Elem => e.type) _ _ he
  rw [hlen, hmap] at hf
  simpa only [allocModule, moduleContext, fresh, build] using hf

end FVA.Wasm.Valid.InitProof
