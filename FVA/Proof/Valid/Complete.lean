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

theorem importDesc_complete {C : Context} {d : ImportDesc} (h : d.Ok C) :
    importDesc C d = true := by
  cases d with
  | func x => simpa [importDesc, ImportDesc.Ok, Nat.blt_eq] using h
  | table tt => exact limits_complete h
  | mem lim => exact limits_complete h
  | global gt => rfl

theorem func_complete {C : Context} {f : Func} {ft : FuncType} (h : FuncT C f ft) :
    func C f = true := by
  simpa only [func, h.1] using expr_complete h.2

theorem elemMode_complete {C : Context} {t : RefType} {mode : ElemMode}
    (h : mode.Ok C t) : elemMode C t mode = true := by
  cases mode with
  | passive | declarative => rfl
  | active x off =>
    obtain ⟨⟨tt, ht, he⟩, htype, hc⟩ := h
    simp [elemMode, ht, he, constExpr_complete htype hc]

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.ble_eq] using h.oneMemory
  · intro f hf
    simpa [Nat.blt_eq] using h.funcTypes f hf
  · intro im hi
    exact CompletenessProof.importDesc_complete (h.imports im hi)
  · intro f hf
    obtain ⟨ft, ht⟩ := h.funcs f hf
    exact CompletenessProof.func_complete ht
  · intro tt ht
    exact CompletenessProof.limits_complete (h.tables tt ht)
  · intro lim hm
    exact CompletenessProof.limits_complete (h.mems lim hm)
  · intro g hg
    exact CompletenessProof.constExpr_complete (h.globals g hg).1 (h.globals g hg).2
  · intro e he
    obtain ⟨hi, hm⟩ := h.elems e he
    exact ⟨fun ex hx => CompletenessProof.constExpr_complete (hi ex hx).1 (hi ex hx).2,
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
