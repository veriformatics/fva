import FVA.Proof.Valid.InstantiateContext
import FVA.Proof.Valid.InstantiateConst

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

/-- A relation holding at every common index of two equally long lists holds pointwise. -/
theorem forall₂_of_lookup {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (hl : xs.length = ys.length)
    (h : ∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → R x y) :
    List.Forall₂ R xs ys := by
  apply List.forall₂_of_length_eq_of_get hl
  intro i h₁ h₂
  exact h i _ _ (List.getElem?_eq_getElem h₁) (List.getElem?_eq_getElem h₂)

/-- The globals a constant initializer under `globalContext m k` reads hold values of their
types once the first `k` defined globals' values are typed (R1 = B: the `k`-th initializer sees
the imported globals and the earlier defined ones; validity of the allocated store is not an
assumption). -/
theorem prefix_globals {s : Store} {m : Module} {imports : List ExternVal} (hs : StoreOK s)
    (hm : ImportsMatch s m imports) (gvals : List Val) (trefs : List Ref)
    (erefs : List (List Ref)) (hg : m.globals.length = gvals.length) {k : Nat}
    (hk : ∀ (j : Nat) (g : Global) (v : Val), j < k → m.globals[j]? = some g →
      gvals[j]? = some v →
      Val.HasType (allocModule s m imports gvals trefs erefs).1 v (g.type.close m.defTypes).val) :
    ∀ (x : Nat) (gt : GlobalType), (globalContext m k).globals[x]? = some gt →
      ∃ (a : Nat) (gi : GlobalInst), (allocModule s m imports gvals trefs erefs).2.globals[x]? =
        some a ∧ (allocModule s m imports gvals trefs erefs).1.globals[a]? = some gi ∧
        gi.value.HasType (allocModule s m imports gvals trefs erefs).1 gt.val := by
  intro x gt hx
  have himp := import_globals hm
  have hext := alloc_extends s m imports gvals trefs erefs
  change (importGlobals m.defTypes m.imports ++
    (m.globals.take k).map (·.type.close m.defTypes))[x]? = some gt at hx
  rw [alloc_inst_globals]
  by_cases hlt : x < (importGlobals m.defTypes m.imports).length
  · rw [List.getElem?_append_left hlt] at hx
    obtain ⟨a, ha, gi, hgi, hsub⟩ := forall₂_lookup_right himp hx
    refine ⟨a, gi, lookup_append ha, ?_, ?_⟩
    · rw [alloc_globals_eq]
      exact lookup_append hgi
    · exact (hext.value (hs.globals gi (List.mem_of_getElem? hgi)).2).globalSub hsub
  · have hle := Nat.le_of_not_lt hlt
    obtain ⟨j, rfl⟩ : ∃ j, x = (importGlobals m.defTypes m.imports).length + j :=
      ⟨_, (Nat.add_sub_cancel' hle).symm⟩
    rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_take] at hx
    split at hx
    · rename_i hjk
      obtain ⟨g, hgj, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hjlen : j < gvals.length := hg ▸ lookup_lt hgj
      have hv := List.getElem?_eq_getElem hjlen
      have hz : (m.globals.zip gvals)[j]? = some (g, gvals[j]) :=
        List.getElem?_zip_eq_some.mpr ⟨hgj, hv⟩
      obtain ⟨a, ha, hga⟩ :=
        forall₂_lookup_right
          (alloc_global_lookup (s := s) (imports := imports) gvals trefs erefs hg) hz
      refine ⟨a, _, ?_, hga, hk j g _ hjk hgj hv⟩
      rw [List.getElem?_append_right (by rw [himp.length_eq]; omega), himp.length_eq,
        Nat.add_sub_cancel_left]
      exact ha
    · cases hx

theorem alloc_values {H : HostSem} {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (hs : StoreOK s)
    (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref))
    (hg : List.Forall₂ (fun g v => Steps H
      ⟨(allocModule s m imports gvals trefs erefs).1,
        ⟨[], (allocModule s m imports gvals trefs erefs).2⟩, g.init.map .plain⟩
      ⟨(allocModule s m imports gvals trefs erefs).1,
        ⟨[], (allocModule s m imports gvals trefs erefs).2⟩, [v.instr]⟩) m.globals gvals)
    (ht : List.Forall₂ (fun t r => Steps H
      ⟨(allocModule s m imports gvals trefs erefs).1,
        ⟨[], (allocModule s m imports gvals trefs erefs).2⟩, t.init.map .plain⟩
      ⟨(allocModule s m imports gvals trefs erefs).1,
        ⟨[], (allocModule s m imports gvals trefs erefs).2⟩, [(Val.ref r).instr]⟩) m.tables trefs)
    (he : List.Forall₂ (fun e rs => List.Forall₂ (fun ex r => Steps H
      ⟨(allocModule s m imports gvals trefs erefs).1,
        ⟨[], (allocModule s m imports gvals trefs erefs).2⟩, ex.map .plain⟩
      ⟨(allocModule s m imports gvals trefs erefs).1,
        ⟨[], (allocModule s m imports gvals trefs erefs).2⟩, [(Val.ref r).instr]⟩) e.init rs)
      m.elems erefs) :
    List.Forall₂ (fun g v => Val.HasType (allocModule s m imports gvals trefs erefs).1 v
      (g.type.close m.defTypes).val) m.globals gvals ∧
    List.Forall₂ (fun t r => Val.HasType (allocModule s m imports gvals trefs erefs).1 (.ref r)
      (.ref (t.type.elem.close m.defTypes))) m.tables trefs ∧
    List.Forall₂ (fun e rs => ∀ r ∈ rs, Val.HasType (allocModule s m imports gvals trefs erefs).1
      (.ref r) (.ref (e.type.close m.defTypes))) m.elems erefs := by
  have hlen := hg.length_eq
  have hfuncs : ∀ (x : Nat) (dt : DefType), (moduleContext m).funcs[x]? = some dt →
      ∃ a fi, (allocModule s m imports gvals trefs erefs).2.funcs[x]? = some a ∧
        (allocModule s m imports gvals trefs erefs).1.funcs[a]? = some fi ∧ fi.type = dt := by
    intro x dt hx
    obtain ⟨a, ha, fi, hfi, hdt⟩ := forall₂_lookup_right (alloc_funcs hv hm gvals trefs erefs) hx
    exact ⟨a, fi, ha, hfi, hdt⟩
  have hpre : ∀ (k j : Nat) (g : Global) (v : Val), j < k → m.globals[j]? = some g →
      gvals[j]? = some v →
      Val.HasType (allocModule s m imports gvals trefs erefs).1 v
        (g.type.close m.defTypes).val := by
    intro k
    induction k with
    | zero => intro j g v hj; omega
    | succ k ih =>
      intro j g v hj hgj hvj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih j g v hj hgj hvj
      · obtain ⟨-, hexpr, hconst⟩ := hv.globals j g hgj
        obtain ⟨v', hv', hst⟩ := forall₂_lookup_left hg hgj
        have hvv : v' = v := Option.some.inj (hv'.symm.trans hvj)
        subst hvv
        exact constant_value (C := globalContext m j) hfuncs
          (prefix_globals hs hm gvals trefs erefs hlen ih) hexpr hconst hst
  have hall : ∀ (x : Nat) (gt : GlobalType), (moduleContext m).globals[x]? = some gt →
      ∃ (a : Nat) (gi : GlobalInst), (allocModule s m imports gvals trefs erefs).2.globals[x]? =
        some a ∧ (allocModule s m imports gvals trefs erefs).1.globals[a]? = some gi ∧
        gi.value.HasType (allocModule s m imports gvals trefs erefs).1 gt.val := by
    intro x gt hx
    apply prefix_globals hs hm gvals trefs erefs hlen (k := m.globals.length)
      (fun j g v _ => hpre (j + 1) j g v (Nat.lt_succ_self j))
    show (importGlobals m.defTypes m.imports ++
      (m.globals.take m.globals.length).map (·.type.close m.defTypes))[x]? = some gt
    rw [List.take_length]
    exact hx
  refine ⟨?_, ?_, ?_⟩
  · exact forall₂_of_lookup hlen fun j g v hgj hvj =>
      hpre (j + 1) j g v (Nat.lt_succ_self j) hgj hvj
  · apply rel_imp_mem ht
    intro t htin r _ hsteps
    obtain ⟨-, -, hte, htc⟩ := hv.tables t htin
    exact constant_value (C := globalContext m 0) hfuncs
      (prefix_globals hs hm gvals trefs erefs hlen (k := 0) (fun j _ _ hj => absurd hj
        (Nat.not_lt_zero j))) hte htc hsteps
  · apply rel_imp_mem he
    intro e hein rs _ hsteps r hr
    have htyped : List.Forall₂ (fun _ r => Val.HasType (allocModule s m imports gvals trefs erefs).1
        (.ref r) (.ref (e.type.close m.defTypes))) e.init rs := by
      apply rel_imp_mem hsteps
      intro ex hex r _ hstep
      have hc := (hv.elems e hein).2.1 ex hex
      exact constant_value hfuncs hall hc.1 hc.2 hstep
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, _, ht⟩ := forall₂_lookup_right htyped hi
    exact ht

/-- Fresh store entries are checked against their initializer values. Existing entries move
through the proven extension; function typing uses allocation metadata, not recursive StoreOK. -/
theorem alloc_store {s : Store} {m : Module} {imports : List ExternVal}
    (hv : ModuleValid m) (hm : ImportsMatch s m imports) (hs : StoreOK s)
    (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref))
    (hg : List.Forall₂ (fun g v => Val.HasType (allocModule s m imports gvals trefs erefs).1 v
      (g.type.close m.defTypes).val) m.globals gvals)
    (ht : List.Forall₂ (fun t r => Val.HasType (allocModule s m imports gvals trefs erefs).1
      (.ref r) (.ref (t.type.elem.close m.defTypes))) m.tables trefs)
    (he : List.Forall₂ (fun e rs => ∀ r ∈ rs,
      Val.HasType (allocModule s m imports gvals trefs erefs).1
        (.ref r) (.ref (e.type.close m.defTypes))) m.elems erefs) :
    StoreOK (allocModule s m imports gvals trefs erefs).1 := by
  have hd := defTypes_closed hv.types
  have hext := alloc_extends s m imports gvals trefs erefs
  obtain ⟨C, hinst, hctx⟩ :=
    alloc_instance hv hm gvals trefs erefs hg.length_eq ht.length_eq he.length_eq
  constructor
  · intro ti hti
    change ti ∈ s.tags ++ m.tags.map _ at hti
    rcases List.mem_append.mp hti with hti | hti
    · exact hs.tags ti hti
    · obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hti
      obtain ⟨ts, hts⟩ := hv.tags t htm
      simp only [Context.typeAt, Option.bind_eq_some_iff] at hts
      obtain ⟨dt, hdt, hexp⟩ := hts
      change m.defTypes[t.type]? = some dt at hdt
      refine ⟨?_, ts, ?_⟩
      · rw [defTypes_getD hdt]
        exact hd dt (List.mem_of_getElem? hdt)
      · rw [defTypes_getD hdt]
        exact hexp
  · intro fi hfi
    change fi ∈ s.funcs ++ m.funcs.map _ at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · exact (hs.funcs fi hfi).extends hext
    · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hfi
      obtain ⟨dt, hft⟩ := hv.funcs fn hfn
      have hdt : m.defTypes[fn.type]? = some dt := hft.1
      have hcode := FuncT.transport hft hctx (fun _ hx => by simp [moduleContext] at hx)
      refine ⟨?_, C, hinst, ?_⟩
      · rw [defTypes_getD hdt]
        exact hd dt (List.mem_of_getElem? hdt)
      · rw [defTypes_getD hdt]
        exact hcode
  · intro ti hti
    change ti ∈ s.tables ++ (m.tables.zip trefs).map _ at hti
    rcases List.mem_append.mp hti with hti | hti
    · obtain ⟨htt, hcl, hlen, hvals⟩ := hs.tables ti hti
      exact ⟨htt, hcl, hlen, fun r hr => hext.value (hvals r hr)⟩
    · obtain ⟨⟨tt, r₀⟩, hpair, rfl⟩ := List.mem_map.mp hti
      have htt := (List.of_mem_zip hpair).1
      obtain ⟨hok, hsrc, -, -⟩ := hv.tables tt htt
      refine ⟨hok, closed_closeHeap hd hsrc, List.length_replicate, ?_⟩
      intro r hr
      rw [(List.mem_replicate.mp hr).2]
      exact List.forall₂_zip ht hpair
  · intro mi hmi
    change mi ∈ s.mems ++ m.mems.map _ at hmi
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact hs.mems mi hmi
    · obtain ⟨lim, hlim, rfl⟩ := List.mem_map.mp hmi
      exact hv.mems lim hlim
  · intro gi hgi
    change gi ∈ s.globals ++ (m.globals.zip gvals).map _ at hgi
    rcases List.mem_append.mp hgi with hgi | hgi
    · exact ⟨(hs.globals gi hgi).1, hext.value (hs.globals gi hgi).2⟩
    · obtain ⟨⟨g, v⟩, hpair, rfl⟩ := List.mem_map.mp hgi
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.of_mem_zip hpair).1
      exact ⟨ValType.closed_close hd (hv.globals k g hk).1, List.forall₂_zip hg hpair⟩
  · intro ei hei
    change ei ∈ s.elems ++ (m.elems.zip erefs).map _ at hei
    rcases List.mem_append.mp hei with hei | hei
    · exact ⟨(hs.elems ei hei).1, fun r hr => hext.value ((hs.elems ei hei).2 r hr)⟩
    · obtain ⟨⟨e, rs⟩, hpair, rfl⟩ := List.mem_map.mp hei
      exact ⟨closed_closeHeap hd (hv.elems e (List.of_mem_zip hpair).1).1,
        List.forall₂_zip he hpair⟩
  · intro e hx
    obtain ⟨ti, ts, hti, hts, hfs⟩ := hs.exns e hx
    exact ⟨ti, ts, lookup_append hti, hts, hext.values hfs⟩

end FVA.Wasm.Valid.InitProof
