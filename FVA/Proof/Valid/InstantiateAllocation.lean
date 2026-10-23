import FVA.Proof.Valid.InstantiateContext
import FVA.Proof.Valid.InstantiateConst

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

theorem alloc_values {H : HostSem} {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (hs : StoreOK s)
    (gvals : List Val) (erefs : List (List Ref))
    (hg : List.Forall₂ (fun g v => Steps H
      ⟨(allocModule s m imports gvals erefs).1,
        ⟨[], (allocModule s m imports gvals erefs).2⟩, g.init.map .plain⟩
      ⟨(allocModule s m imports gvals erefs).1,
        ⟨[], (allocModule s m imports gvals erefs).2⟩, [v.instr]⟩) m.globals gvals)
    (he : List.Forall₂ (fun e rs => List.Forall₂ (fun ex r => Steps H
      ⟨(allocModule s m imports gvals erefs).1,
        ⟨[], (allocModule s m imports gvals erefs).2⟩, ex.map .plain⟩
      ⟨(allocModule s m imports gvals erefs).1,
        ⟨[], (allocModule s m imports gvals erefs).2⟩, [(Val.ref r).instr]⟩) e.init rs)
      m.elems erefs) :
    List.Forall₂ (fun g v => Val.HasType (allocModule s m imports gvals erefs).1 v g.type.val)
      m.globals gvals ∧
    List.Forall₂ (fun e rs => ∀ r ∈ rs,
      Val.HasType (allocModule s m imports gvals erefs).1 (.ref r) (.ref e.type))
      m.elems erefs := by
  let s₁ := (allocModule s m imports gvals erefs).1
  let inst := (allocModule s m imports gvals erefs).2
  let C : Context := { moduleContext m with globals := importGlobals m.imports }
  have hfuncs : ∀ (x : Nat) (ft : FuncType), C.funcs[x]? = some ft →
      ∃ a, inst.funcs[x]? = some a ∧ a < s₁.funcs.length := by
    intro x ft hx
    obtain ⟨a, ha, fi, hfi, _⟩ := forall₂_lookup_right (alloc_funcs hv hm gvals erefs) hx
    exact ⟨a, ha, lookup_lt hfi⟩
  have hglobals : ∀ (x : Nat) (gt : GlobalType), C.globals[x]? = some gt →
      ∃ (a : Nat) (gi : GlobalInst), inst.globals[x]? = some a ∧ s₁.globals[a]? = some gi ∧
        gi.value.HasType s₁ gt.val := by
    intro x gt hx
    obtain ⟨a, ha, gi, hgi, htype⟩ := forall₂_lookup_right (import_globals hm) hx
    refine ⟨a, gi, lookup_append ha, lookup_append hgi, ?_⟩
    have ht := (alloc_extends s m imports gvals erefs).value
      (hs.globals gi (List.mem_of_getElem? hgi))
    simpa [htype] using ht
  constructor
  · apply rel_imp_mem hg
    intro g hgin v _ hsteps
    exact constant_value hfuncs hglobals (hv.globals g hgin).1 (hv.globals g hgin).2 hsteps
  · apply rel_imp_mem he
    intro e hein rs _ hsteps r hr
    have htyped : List.Forall₂ (fun _ r => Val.HasType s₁ (.ref r) (.ref e.type)) e.init rs := by
      apply rel_imp_mem hsteps
      intro ex hex r _ hstep
      have hc := (hv.elems e hein).1 ex hex
      exact constant_value hfuncs hglobals hc.1 hc.2 hstep
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, _, ht⟩ := forall₂_lookup_right htyped hi
    exact ht

/-- Fresh store entries are checked against their initializer values. Existing entries move
through the proven extension; function typing uses allocation metadata, not recursive StoreOK. -/
theorem alloc_store {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (hs : StoreOK s)
    (gvals : List Val) (erefs : List (List Ref))
    (hg : List.Forall₂ (fun g v =>
      Val.HasType (allocModule s m imports gvals erefs).1 v g.type.val) m.globals gvals)
    (he : List.Forall₂ (fun e rs => ∀ r ∈ rs,
      Val.HasType (allocModule s m imports gvals erefs).1 (.ref r) (.ref e.type)) m.elems erefs) :
    StoreOK (allocModule s m imports gvals erefs).1 := by
  let s₁ := (allocModule s m imports gvals erefs).1
  let inst := (allocModule s m imports gvals erefs).2
  have hext := alloc_extends s m imports gvals erefs
  obtain ⟨C, hinst, hctx⟩ := alloc_instance hv hm gvals erefs hg.length_eq he.length_eq
  constructor
  · intro fi hfi
    change fi ∈ s.funcs ++ m.funcs.map _ at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · exact (hs.funcs fi hfi).extends hext
    · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hfi
      obtain ⟨ft, hft, hbody⟩ := hv.funcs fn hfn
      have hcode := FuncT.transport (C := moduleContext m) ⟨hft, hbody⟩ hctx
      have htype : m.types[fn.type]? = some ft := hft
      refine ⟨C, hinst, ?_⟩
      simpa [htype] using hcode
  · intro ti hti
    change ti ∈ s.tables ++ m.tables.map _ at hti
    rcases List.mem_append.mp hti with hti | hti
    · obtain ⟨ht, hlen, hvals⟩ := hs.tables ti hti
      exact ⟨ht, hlen, fun r hr => hext.value (hvals r hr)⟩
    · obtain ⟨tt, htt, rfl⟩ := List.mem_map.mp hti
      refine ⟨hv.tables tt htt, List.length_replicate, ?_⟩
      intro r hr
      have hr' : r = Ref.null tt.elem := (List.mem_replicate.mp hr).2
      simp [hr', Val.HasType]
  · intro mi hmi
    change mi ∈ s.mems ++ m.mems.map _ at hmi
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact hs.mems mi hmi
    · obtain ⟨lim, hlim, rfl⟩ := List.mem_map.mp hmi
      exact hv.mems lim hlim
  · intro gi hgi
    change gi ∈ s.globals ++ (m.globals.zip gvals).map _ at hgi
    rcases List.mem_append.mp hgi with hgi | hgi
    · exact hext.value (hs.globals gi hgi)
    · obtain ⟨⟨g, v⟩, hpair, rfl⟩ := List.mem_map.mp hgi
      exact List.forall₂_zip hg hpair
  · intro ei hei r hr
    change ei ∈ s.elems ++ (m.elems.zip erefs).map _ at hei
    rcases List.mem_append.mp hei with hei | hei
    · exact hext.value (hs.elems ei hei r hr)
    · obtain ⟨⟨e, rs⟩, hpair, rfl⟩ := List.mem_map.mp hei
      exact List.forall₂_zip he hpair r hr

end FVA.Wasm.Valid.InitProof
