import FVA.Proof.Valid.InstantiateLists
import FVA.Proof.Valid.Profile

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

/-- Each import paired with its match and its 2.0-profile shape. -/
theorem imports_profile {s : Store} {m : Module} {imports : List ExternVal} (hv : ModuleValid m)
    (h : ImportsMatch s m imports) :
    List.Forall₂ (fun ev im => ev.Matches s m.defTypes im.desc ∧ match im.desc with
      | .table tt => ValType.inP2 (.ref tt.elem) = true
      | .global gt => gt.val.inP2 = true
      | .tag _ => False
      | _ => True) imports m.imports :=
  rel_imp_mem h fun _ _ im him hm => ⟨hm, (Module.inP2_spec hv.profile).imports im him⟩

theorem import_funcs {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a ft => ∃ fi, s.funcs[a]? = some fi ∧ fi.type.expand = some ft)
      (ExternVal.funcs imports) (importFuncs { types := m.typeList } m.imports) := by
  unfold ExternVal.funcs importFuncs
  apply rel_filterMap h
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try trivial
  rename_i a x
  obtain ⟨fi, hf, hx⟩ := hm
  obtain ⟨ft, hft, he⟩ :=
    forall₂_lookup_left (forall₂_defTypes (Module.inP2_spec hv.profile).types) hx
  simp only [hft]
  exact ⟨fi, hf, he⟩

theorem import_tables {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a tt => ∃ ti, s.tables[a]? = some ti ∧ ti.type.elem = tt.elem)
      (ExternVal.tables imports) (importTables m.imports) := by
  unfold ExternVal.tables importTables
  apply rel_filterMap (imports_profile hv h)
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try simp_all
  rename_i a tt
  obtain ⟨⟨ti, ht, _, he⟩, hp⟩ := hm
  simp only [ValType.inP2, Bool.and_eq_true] at hp
  obtain ⟨b, hb⟩ := HeapType.eq_abs_of_inP2 hp.2
  refine ⟨ti, ht, ?_⟩
  rw [he, hb, closeHeap_abs, ← hb, RefType.eta]

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
    (hv : ModuleValid m) (h : ImportsMatch s m imports) :
    List.Forall₂ (fun a gt => ∃ gi, s.globals[a]? = some gi ∧ gi.type.Sub gt)
      (ExternVal.globals imports) (importGlobals m.imports) := by
  unfold ExternVal.globals importGlobals
  apply rel_filterMap (imports_profile hv h)
  intro ev im hm
  rcases im with ⟨mod, name, desc⟩
  cases ev <;> cases desc <;> simp only [ExternVal.Matches] at hm <;> try simp_all
  rename_i a gt
  obtain ⟨⟨gi, hg, hsub⟩, hp⟩ := hm
  rw [ValType.mapHeap_of_inP2 (fun _ => rfl) hp] at hsub
  exact ⟨gi, hg, hsub⟩

theorem funcTypes_map {m : Module} (h : ModuleValid m) :
    m.funcs.filterMap (fun f => m.typeList[f.type]?) =
      m.funcs.map (fun f => (m.typeList[f.type]?).getD ⟨[], []⟩) := by
  apply filterMap_getD
  intro f hf
  exact ⟨_, List.getElem?_eq_getElem (h.funcTypes f hf)⟩

theorem map_zip_left {α β γ : Type} (f : α → γ) (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : (xs.zip ys).map (fun p => f p.1) = xs.map f := by
  change (xs.zip ys).map (f ∘ Prod.fst) = xs.map f
  rw [← List.map_map, List.map_fst_zip (Nat.le_of_eq h)]

theorem alloc_funcs {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) :
    List.Forall₂ (fun a ft => ∃ fi,
      (allocModule s m imports gvals trefs erefs).1.funcs[a]? = some fi ∧
        fi.type.expand = some ft)
      (allocModule s m imports gvals trefs erefs).2.funcs (moduleContext m).funcs := by
  let inst := (allocModule s m imports gvals trefs erefs).2
  let build (fn : Func) := FuncInst.wasm (m.defTypes[fn.type]?.getD ⟨[], 0⟩) inst fn
  have hi := binding_append (tail := m.funcs.map build) (import_funcs hv hm)
  have hf : List.Forall₂ (fun a ft => ∃ fi,
      (s.funcs ++ m.funcs.map build)[a]? = some fi ∧ fi.type.expand = some ft)
      (fresh s.funcs.length m.funcs.length)
      (m.funcs.map fun fn => (m.typeList[fn.type]?).getD ⟨[], []⟩) := by
    apply List.forall₂_map_right_iff.mpr
    apply rel_imp_mem (fresh_lookup s.funcs m.funcs build)
    intro a _ fn hfn hl
    obtain ⟨dt, hdt, he⟩ := forall₂_lookup_right
      (forall₂_defTypes (Module.inP2_spec hv.profile).types)
      (List.getElem?_eq_getElem (hv.funcTypes fn hfn))
    refine ⟨build fn, hl, ?_⟩
    simp only [build, FuncInst.type, hdt, Option.getD_some, he,
      List.getElem?_eq_getElem (hv.funcTypes fn hfn)]
  have both := List.rel_append hi hf
  simpa only [allocModule, moduleContext, fresh, build, inst, funcTypes_map hv] using both

theorem alloc_tables {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) (ht : m.tables.length = trefs.length) :
    List.Forall₂ (fun a tt => ∃ ti,
      (allocModule s m imports gvals trefs erefs).1.tables[a]? = some ti ∧ ti.type.elem = tt.elem)
      (allocModule s m imports gvals trefs erefs).2.tables (moduleContext m).tables := by
  let closeRef (t : RefType) : RefType := ⟨t.null, closeHeap m.defTypes t.heap⟩
  let build (p : Table × Ref) : TableInst :=
    ⟨{ p.1.type with elem := closeRef p.1.type.elem }, List.replicate p.1.type.limits.min p.2⟩
  have hi := binding_append (tail := (m.tables.zip trefs).map build) (import_tables hv hm)
  have hf := fresh_binding s.tables (m.tables.zip trefs) build (fun ti => ti.type.elem)
  have hlen : (m.tables.zip trefs).length = m.tables.length := by simp [ht]
  have hmap : (m.tables.zip trefs).map (fun p => (build p).type.elem) =
      m.tables.map (·.type.elem) := by
    rw [← map_zip_left (fun t : Table => t.type.elem) _ _ ht]
    apply List.map_congr_left
    intro p hp
    obtain ⟨a, he, -, -⟩ := (Module.inP2_spec hv.profile).tables p.1 (List.of_mem_zip hp).1
    simp only [build, closeRef, he, closeHeap_abs]
  rw [hlen, hmap] at hf
  have hf' : List.Forall₂ (fun a tt => ∃ ti,
      (s.tables ++ (m.tables.zip trefs).map build)[a]? = some ti ∧ ti.type.elem = TableType.elem tt)
      (fresh s.tables.length m.tables.length) (m.tables.map (·.type)) :=
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

theorem alloc_globals {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) (hg : m.globals.length = gvals.length) :
    List.Forall₂ (fun a gt => ∃ gi,
      (allocModule s m imports gvals trefs erefs).1.globals[a]? = some gi ∧ gi.type.Sub gt)
      (allocModule s m imports gvals trefs erefs).2.globals (moduleContext m).globals := by
  let build (p : Global × Val) : GlobalInst :=
    ⟨⟨p.1.type.mutability, p.1.type.val.mapHeap (closeHeap m.defTypes)⟩, p.2⟩
  have hi := binding_append (tail := (m.globals.zip gvals).map build) (import_globals hv hm)
  have hf := fresh_binding s.globals (m.globals.zip gvals) build GlobalInst.type
  have hlen : (m.globals.zip gvals).length = m.globals.length := by simp [hg]
  have hmap : (m.globals.zip gvals).map (fun p => (build p).type) = m.globals.map (·.type) := by
    rw [← map_zip_left (fun g : Global => g.type) _ _ hg]
    apply List.map_congr_left
    intro p hp
    simp only [build]
    rw [ValType.mapHeap_of_inP2 (fun _ => rfl)
      ((Module.inP2_spec hv.profile).globals p.1 (List.of_mem_zip hp).1)]
  rw [hlen, hmap] at hf
  have hf' : List.Forall₂ (fun a gt => ∃ gi,
      (s.globals ++ (m.globals.zip gvals).map build)[a]? = some gi ∧ gi.type.Sub gt)
      (fresh s.globals.length m.globals.length) (m.globals.map (·.type)) := by
    apply List.Forall₂.imp _ hf
    rintro a gt ⟨v, hv, rfl⟩
    exact ⟨v, hv, GlobalType.Sub.refl _⟩
  have both := List.rel_append hi hf'
  simpa only [allocModule, moduleContext, fresh, build] using both

theorem alloc_elems {s : Store} {m : Module} {imports : List ExternVal} (hv : ModuleValid m)
    (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref))
    (he : m.elems.length = erefs.length) :
    List.Forall₂ (fun a rt => ∃ ei,
      (allocModule s m imports gvals trefs erefs).1.elems[a]? = some ei ∧ ei.type = rt)
      (allocModule s m imports gvals trefs erefs).2.elems (moduleContext m).elems := by
  let build (p : Elem × List Ref) : ElemInst :=
    ⟨⟨p.1.type.nullable.null, closeHeap m.defTypes p.1.type.nullable.heap⟩, p.2⟩
  have hf := fresh_binding s.elems (m.elems.zip erefs) build ElemInst.type
  have hlen : (m.elems.zip erefs).length = m.elems.length := by simp [he]
  have hmap : (m.elems.zip erefs).map (fun p => (build p).type) =
      m.elems.map (·.type.nullable) := by
    rw [← map_zip_left (fun e : Elem => e.type.nullable) _ _ he]
    apply List.map_congr_left
    intro p hp
    obtain ⟨a, hb⟩ :=
      HeapType.eq_abs_of_inP2 ((Module.inP2_spec hv.profile).elems p.1 (List.of_mem_zip hp).1)
    simp only [build, RefType.nullable, hb, closeHeap_abs]
  rw [hlen, hmap] at hf
  simpa only [allocModule, moduleContext, fresh, build] using hf

end FVA.Wasm.Valid.InitProof
