import FVA.Proof.Valid.InstantiateContext
import FVA.Proof.Valid.InstantiateConst

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

/-- The initializer of a 2.0-profile table is a typed constant `ref.null` of its element
type. -/
theorem table_init {m : Module} (hv : ModuleValid m) {t : Table} (ht : t ∈ m.tables)
    (C : Context) : ExprT C t.init [.ref t.type.elem] ∧ ConstExpr C t.init := by
  obtain ⟨a, he, -, hi⟩ := (Module.inP2_spec hv.profile).tables t ht
  rw [hi, he]
  exact ⟨⟨_, SeqT.single .refNull, Matches.refl _⟩, by simp [ConstExpr, ConstInstr]⟩

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
    List.Forall₂ (fun g v => Val.HasType (allocModule s m imports gvals trefs erefs).1 v g.type.val)
      m.globals gvals ∧
    List.Forall₂ (fun t r =>
      Val.HasType (allocModule s m imports gvals trefs erefs).1 (.ref r) (.ref t.type.elem))
      m.tables trefs ∧
    List.Forall₂ (fun e rs => ∀ r ∈ rs,
      Val.HasType (allocModule s m imports gvals trefs erefs).1 (.ref r) (.ref e.type.nullable))
      m.elems erefs := by
  let s₁ := (allocModule s m imports gvals trefs erefs).1
  let inst := (allocModule s m imports gvals trefs erefs).2
  let C : Context := { moduleContext m with globals := importGlobals m.imports }
  have hfuncs : ∀ (x : Nat) (ft : FuncType), C.funcs[x]? = some ft →
      ∃ a, inst.funcs[x]? = some a ∧ a < s₁.funcs.length := by
    intro x ft hx
    obtain ⟨a, ha, fi, hfi, _⟩ := forall₂_lookup_right (alloc_funcs hv hm gvals trefs erefs) hx
    exact ⟨a, ha, lookup_lt hfi⟩
  have hglobals : ∀ (x : Nat) (gt : GlobalType), C.globals[x]? = some gt →
      ∃ (a : Nat) (gi : GlobalInst), inst.globals[x]? = some a ∧ s₁.globals[a]? = some gi ∧
        gi.value.HasType s₁ gt.val := by
    intro x gt hx
    obtain ⟨a, ha, gi, hgi, htype⟩ := forall₂_lookup_right (import_globals hv hm) hx
    refine ⟨a, gi, lookup_append ha, lookup_append hgi, ?_⟩
    exact ((alloc_extends s m imports gvals trefs erefs).value
      (hs.globals gi (List.mem_of_getElem? hgi))).globalSub htype
  refine ⟨?_, ?_, ?_⟩
  · apply rel_imp_mem hg
    intro g hgin v _ hsteps
    exact constant_value hfuncs hglobals (hv.globals g hgin).1 (hv.globals g hgin).2 hsteps
  · apply rel_imp_mem ht
    intro t htin r _ hsteps
    obtain ⟨hte, htc⟩ := table_init hv htin C
    exact constant_value hfuncs hglobals hte htc hsteps
  · apply rel_imp_mem he
    intro e hein rs _ hsteps r hr
    have htyped :
        List.Forall₂ (fun _ r => Val.HasType s₁ (.ref r) (.ref e.type.nullable)) e.init rs := by
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
    (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref))
    (hg : List.Forall₂ (fun g v =>
      Val.HasType (allocModule s m imports gvals trefs erefs).1 v g.type.val) m.globals gvals)
    (ht : List.Forall₂ (fun t r =>
      Val.HasType (allocModule s m imports gvals trefs erefs).1 (.ref r) (.ref t.type.elem))
      m.tables trefs)
    (he : List.Forall₂ (fun e rs => ∀ r ∈ rs,
      Val.HasType (allocModule s m imports gvals trefs erefs).1 (.ref r) (.ref e.type.nullable))
      m.elems erefs) :
    StoreOK (allocModule s m imports gvals trefs erefs).1 := by
  let s₁ := (allocModule s m imports gvals trefs erefs).1
  let inst := (allocModule s m imports gvals trefs erefs).2
  have hP := Module.inP2_spec hv.profile
  have hext := alloc_extends s m imports gvals trefs erefs
  obtain ⟨C, hinst, hctx⟩ :=
    alloc_instance hv hm gvals trefs erefs hg.length_eq ht.length_eq he.length_eq
  constructor
  · intro fi hfi
    change fi ∈ s.funcs ++ m.funcs.map _ at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · exact (hs.funcs fi hfi).extends hext
    · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hfi
      obtain ⟨ft, hft, hdef, hbody⟩ := hv.funcs fn hfn
      have hcode := FuncT.transport (C := moduleContext m) ⟨hft, hdef, hbody⟩ hctx
      obtain ⟨dt, hdt, hexp⟩ := forall₂_lookup_right (forall₂_defTypes hP.types) hft
      refine ⟨C, ft, ?_, hinst, hcode⟩
      simpa only [FuncInst.type, hdt, Option.getD_some] using hexp
  · intro ti hti
    change ti ∈ s.tables ++ (m.tables.zip trefs).map _ at hti
    rcases List.mem_append.mp hti with hti | hti
    · obtain ⟨htt, hlen, hvals⟩ := hs.tables ti hti
      exact ⟨htt, hlen, fun r hr => hext.value (hvals r hr)⟩
    · obtain ⟨⟨tt, r₀⟩, hpair, rfl⟩ := List.mem_map.mp hti
      have htt := (List.of_mem_zip hpair).1
      obtain ⟨a, hea, -, -⟩ := hP.tables tt htt
      refine ⟨hv.tables tt htt, List.length_replicate, ?_⟩
      intro r hr
      rw [(List.mem_replicate.mp hr).2]
      have h₀ := List.forall₂_zip ht hpair
      simp only [hea] at h₀ ⊢
      exact h₀
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
      have hval := List.forall₂_zip hg hpair
      dsimp only
      rw [ValType.mapHeap_of_inP2 (σ := closeHeap m.defTypes) (fun _ => rfl)
        (hP.globals g (List.of_mem_zip hpair).1)]
      exact hval
  · intro ei hei r hr
    change ei ∈ s.elems ++ (m.elems.zip erefs).map _ at hei
    rcases List.mem_append.mp hei with hei | hei
    · exact hext.value (hs.elems ei hei r hr)
    · obtain ⟨⟨e, rs⟩, hpair, rfl⟩ := List.mem_map.mp hei
      obtain ⟨a, hb⟩ := HeapType.eq_abs_of_inP2 (hP.elems e (List.of_mem_zip hpair).1)
      have hval := List.forall₂_zip he hpair r hr
      simp only [RefType.nullable, hb, closeHeap_abs] at hval ⊢
      exact hval

end FVA.Wasm.Valid.InitProof
