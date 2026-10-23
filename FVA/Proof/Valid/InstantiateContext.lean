import FVA.Proof.Valid.InstantiateImports

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

theorem declaredRefs_bound {m : Module} (hv : ModuleValid m) {x : Nat}
    (hx : x ∈ declaredRefs m) : x < (moduleContext m).funcs.length := by
  simp only [declaredRefs, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (⟨g, hg, hx⟩ | ⟨e, he, hx⟩) | hx
  · exact refFunc_bound (hv.globals g hg).1 hx
  · rcases hx with hx | hx
    · obtain ⟨ex, hex, hx⟩ := hx
      exact refFunc_bound ((hv.elems e he).1 ex hex).1 hx
    · have hm := (hv.elems e he).2
      cases heq : e.mode with
      | passive | declarative => simp [heq] at hx
      | active table off =>
        simp only [heq, ElemMode.Ok] at hm hx
        exact refFunc_bound hm.2.1 hx
  · obtain ⟨ex, hex, hx⟩ := List.mem_filterMap.mp hx
    have he := hv.exports ex hex
    cases hd : ex.desc <;> simp only [hd, ExportDesc.Ok] at hx he
    all_goals try cases hx
    exact he

theorem address_bound {β : Type} {R : Nat → β → Prop} {addrs : List Nat} {ts : List β}
    {n i : Nat} (h : List.Forall₂ R addrs ts) (hb : ∀ a t, R a t → a < n)
    (hi : i < ts.length) : (addrs[i]?.getD 0) < n := by
  obtain ⟨a, ha, ht⟩ := forall₂_lookup_right h (List.getElem?_eq_getElem hi)
  simpa [ha] using hb a _ ht

theorem alloc_exports {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val)
    (erefs : List (List Ref)) (hg : m.globals.length = gvals.length) :
    ∀ ex ∈ (allocModule s m imports gvals erefs).2.exports,
      ExternValT (allocModule s m imports gvals erefs).1 ex.value := by
  intro ex hex
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hex
  have hv' := hv.exports e he
  cases hd : e.desc with
  | func x =>
    have hb := address_bound (alloc_funcs hv hm gvals erefs)
      (fun _ _ ⟨fi, hfi, _⟩ => lookup_lt hfi) (by simpa [hd, ExportDesc.Ok] using hv')
    simpa only [allocModule, hd, ExternValT] using hb
  | table x =>
    have hb := address_bound (alloc_tables hm gvals erefs)
      (fun _ _ ⟨ti, hti, _⟩ => lookup_lt hti) (by simpa [hd, ExportDesc.Ok] using hv')
    simpa only [allocModule, hd, ExternValT] using hb
  | mem x =>
    have hb := address_bound (alloc_mems hm gvals erefs)
      (fun _ _ ⟨mi, hmi⟩ => lookup_lt hmi) (by simpa [hd, ExportDesc.Ok] using hv')
    simpa only [allocModule, hd, ExternValT] using hb
  | global x =>
    have hb := address_bound (alloc_globals hm gvals erefs hg)
      (fun _ _ ⟨gi, hgi, _⟩ => lookup_lt hgi) (by simpa [hd, ExportDesc.Ok] using hv')
    simpa only [allocModule, hd, ExternValT] using hb

/-- Allocation metadata supplies an instance context before initializer values are proved
well typed; imported table and memory minima use their actual current sizes. -/
theorem alloc_instance {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (gvals : List Val)
    (erefs : List (List Ref)) (hg : m.globals.length = gvals.length)
    (he : m.elems.length = erefs.length) :
    ∃ C, ModuleInstT (allocModule s m imports gvals erefs).1
      (allocModule s m imports gvals erefs).2 C ∧ (moduleContext m).Entails C := by
  let s₁ := (allocModule s m imports gvals erefs).1
  let inst := (allocModule s m imports gvals erefs).2
  have hfuncs := alloc_funcs hv hm gvals erefs
  have hglobals := alloc_globals hm gvals erefs hg
  have helems := alloc_elems s m imports gvals erefs he
  obtain ⟨tables, ht, hshape⟩ := forall₂_exists_right
    (S := fun a tt => ∃ ti, s₁.tables[a]? = some ti ∧ ti.type = tt)
    (T := fun tt tt' : TableType => tt'.elem = tt.elem)
    (alloc_tables hm gvals erefs) (by
      rintro a tt ⟨ti, hti, he⟩
      exact ⟨ti.type, ⟨ti, hti, rfl⟩, he⟩)
  obtain ⟨mems, hm', _⟩ := forall₂_exists_right
    (S := fun a lim => ∃ mi, s₁.mems[a]? = some mi ∧ (⟨mi.pages, mi.max⟩ : Limits) = lim)
    (T := fun _ _ : Limits => True)
    (alloc_mems hm gvals erefs) (by
      rintro a lim ⟨mi, hmi⟩
      exact ⟨⟨mi.pages, mi.max⟩, ⟨mi, hmi, rfl⟩, trivial⟩)
  let C : Context := { moduleContext m with
    tables := tables
    mems := mems
    refs := List.range inst.funcs.length }
  have hmem_len : (moduleContext m).mems.length = mems.length :=
    (alloc_mems hm gvals erefs).length_eq.symm.trans hm'.length_eq
  refine ⟨C, ?_, ?_⟩
  · refine ⟨rfl, hfuncs, ht, hm', hglobals, helems, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · constructor
      · simp [C, allocModule, moduleContext]
      · intro a ha
        change a ∈ fresh s.datas.length m.datas.length at ha
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        have hbound := List.mem_range.mp hi
        change s.datas.length + i < (s.datas ++ m.datas.map (fun d => (⟨d.init⟩ : DataInst))).length
        simp only [List.length_append, List.length_map]
        omega
    · exact alloc_exports hv hm gvals erefs hg
    · simpa [C, inst, allocModule, List.map_map, Function.comp_def] using hv.exportNames
  · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, Nat.le_refl _, fun _ => rfl,
      rfl, rfl, ?_⟩
    · intro x tt hx
      exact forall₂_lookup_left hshape hx
    · intro x lim hx
      have hbound : x < mems.length := hmem_len ▸ lookup_lt hx
      exact ⟨_, List.getElem?_eq_getElem hbound⟩
    · intro x hx
      apply List.mem_range.mpr
      have hbound := declaredRefs_bound hv hx
      simpa only [← hfuncs.length_eq] using hbound

end FVA.Wasm.Valid.InitProof
