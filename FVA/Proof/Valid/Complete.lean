import FVA.Proof.Valid.CompleteInstr

namespace FVA.Wasm.Valid

open FVA.Wasm Check ValidatorProof

namespace CompletenessProof

theorem constant_complete {C : Context} {i : Instr} (h : ConstInstr C i) :
    constant C i = true := by
  cases i <;> simp only [constant, ConstInstr] at h ⊢
  obtain ⟨t, ht⟩ := h
  simp [ht]

theorem constExpr_complete {C : Context} {e : Expr} {ts : List ValType}
    (ht : ExprT C e ts) (hc : ConstExpr C e) : constExpr C e ts = true := by
  simp only [constExpr, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun i hi => constant_complete (hc i hi), expr_complete ht⟩

theorem limits_complete {k : Nat} {l : Limits} (h : l.Ok k) : limits k l = true := by
  simp only [limits, Bool.and_eq_true, Nat.ble_eq]
  refine ⟨h.1, ?_⟩
  cases hx : l.max with
  | none => rfl
  | some mx => simpa [Nat.ble_eq] using h.2 mx hx

theorem typesSeq_complete {gs : List RecType} {x : Nat} (h : TypesSeq gs x) :
    typesSeq gs x = true := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := h
    simp only [typesSeq, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun f hf => ?_, ih hgs⟩
    obtain ⟨hp, hr⟩ := hg f hf
    exact ⟨fun t ht => valSrc_complete (hp t ht), fun t ht => valSrc_complete (hr t ht)⟩

theorem tagType_complete {C : Context} {x : Nat} (h : ∃ ts, C.typeAt x = some ⟨ts, []⟩) :
    tagType C x = true := by
  obtain ⟨ts, ht⟩ := h
  simp [tagType, ht]

theorem importDesc_complete {C : Context} {d : ImportDesc} (h : d.Ok C) :
    importDesc C d = true := by
  cases d with
  | func x =>
    obtain ⟨ft, ht⟩ := h
    simp [importDesc, ht]
  | table tt =>
    obtain ⟨hl, hs⟩ := h
    simp only [importDesc, Bool.and_eq_true]
    exact ⟨limits_complete hl, heapSrc_complete hs⟩
  | mem lim => exact limits_complete h
  | global gt => exact valSrc_complete h
  | tag x => exact tagType_complete h

theorem globals_complete {C : Context} {dts : List DefType} {gs : List Global}
    (h : ∀ k (g : Global), gs[k]? = some g →
      g.type.val.Src dts.length ∧
      ExprT { C with globals := C.globals ++ (gs.take k).map (·.type.close dts) } g.init
        [(g.type.close dts).val] ∧
      ConstExpr { C with globals := C.globals ++ (gs.take k).map (·.type.close dts) } g.init) :
    globals C dts gs = true := by
  induction gs generalizing C with
  | nil => rfl
  | cons g₀ gs ih =>
    obtain ⟨hsrc, he, hc⟩ := h 0 g₀ rfl
    simp only [List.take_zero, List.map_nil, List.append_nil] at he hc
    simp only [globals, Bool.and_eq_true]
    refine ⟨⟨valSrc_complete hsrc, constExpr_complete he hc⟩, ih fun k g hg => ?_⟩
    have := h (k + 1) g (by simpa using hg)
    simpa [List.take_succ_cons, List.append_assoc] using this

theorem func_complete {C : Context} {f : Func} {dt : DefType} (h : FuncT C f dt) :
    func C f = true := by
  obtain ⟨hdt, ft, he, hl, hb⟩ := h
  have ht : C.typeAt f.type = some ft := by simp [Context.typeAt, hdt, he]
  simp only [func, ht, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun l hl' => valSrc_complete (hl l hl'), expr_complete hb⟩

theorem elemMode_complete {C : Context} {t : RefType} {mode : ElemMode}
    (h : mode.Ok C t) : elemMode C t mode = true := by
  cases mode with
  | passive | declarative => rfl
  | active x off =>
    obtain ⟨⟨tt, ht, he⟩, htype, hc⟩ := h
    simp [elemMode, ht, subType_complete he, constExpr_complete htype hc]

theorem dataMode_complete {C : Context} {mode : DataMode} (h : mode.Ok C) :
    dataMode C mode = true := by
  cases mode with
  | passive => rfl
  | active x off =>
    obtain ⟨⟨lim, hl⟩, ht, hc⟩ := h
    simp [dataMode, hl, constExpr_complete ht hc]

theorem exportDesc_complete {C : Context} {d : ExportDesc} (h : d.Ok C) :
    exportDesc C d = true := by
  cases d <;> simpa [exportDesc, ExportDesc.Ok, Nat.blt_eq] using h

theorem distinct_complete {names : List String} (h : names.Nodup) : distinct names = true := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp h
    simp [distinct, hn, ih ht]

end CompletenessProof

/-- Every raw module satisfying the reviewed typing judgment is accepted. -/
theorem validate_complete {m : Module} (h : ModuleValid m) : validate m = true := by
  simp only [validate, Bool.and_eq_true, and_assoc, List.all_eq_true]
  refine ⟨CompletenessProof.typesSeq_complete h.types, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa [Nat.ble_eq] using h.oneMemory
  · intro im hi
    exact CompletenessProof.importDesc_complete (h.imports im hi)
  · intro t ht
    exact CompletenessProof.tagType_complete (h.tags t ht)
  · exact CompletenessProof.globals_complete h.globals
  · intro lim hm
    exact CompletenessProof.limits_complete (h.mems lim hm)
  · intro t ht
    obtain ⟨hl, hs, he, hc⟩ := h.tables t ht
    have h0 : globalContext m 0 =
        { moduleContext m with globals := importGlobals m.defTypes m.imports } := by
      simp [globalContext]
    rw [h0] at he hc
    exact ⟨CompletenessProof.limits_complete hl, CompletenessProof.heapSrc_complete hs,
      CompletenessProof.constExpr_complete he hc⟩
  · intro f hf
    obtain ⟨dt, ht⟩ := h.funcs f hf
    exact CompletenessProof.func_complete ht
  · intro e he
    obtain ⟨hs, hi, hm⟩ := h.elems e he
    exact ⟨CompletenessProof.heapSrc_complete hs,
      fun ex hx => CompletenessProof.constExpr_complete (hi ex hx).1 (hi ex hx).2,
      CompletenessProof.elemMode_complete hm⟩
  · intro d hd
    exact CompletenessProof.dataMode_complete (h.datas d hd)
  · intro e he
    simpa [Nat.blt_eq] using h.elemLengths e he
  · intro d hd
    simpa [Nat.blt_eq] using h.dataLengths d hd
  · cases hx : m.start with
    | none => rfl
    | some x => simp [h.start x hx]
  · intro ex hx
    exact CompletenessProof.exportDesc_complete (h.exports ex hx)
  · exact CompletenessProof.distinct_complete h.exportNames

/-- The algorithm decides the reviewed raw-module typing judgment exactly. -/
theorem validate_iff (m : Module) : validate m = true ↔ ModuleValid m :=
  ⟨validate_sound, validate_complete⟩

#print axioms validate_complete
#print axioms validate_iff

end FVA.Wasm.Valid
