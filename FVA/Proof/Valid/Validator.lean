import FVA.Proof.Valid.ValidatorInstr

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

theorem constant_sound {C : Context} {i : Instr} (h : constant C i = true) : ConstInstr C i := by
  cases i <;> simp only [constant, ConstInstr] at h ⊢ <;> try trivial
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

theorem constExpr_sound {C : Context} {e : Expr} {ts : List ValType}
    (h : constExpr C e ts = true) : ExprT C e ts ∧ ConstExpr C e := by
  simp only [constExpr, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨expr_sound h.2, fun i hi => constant_sound (h.1 i hi)⟩

theorem limits_sound {k : Nat} {l : Limits} (h : limits k l = true) : l.Ok k := by
  simp only [limits, Bool.and_eq_true, Nat.ble_eq] at h
  refine ⟨h.1, ?_⟩
  intro mx hx
  simpa [hx, Nat.ble_eq] using h.2

theorem importDesc_sound {C : Context} {d : ImportDesc} (h : importDesc C d = true) : d.Ok C := by
  cases d with
  | func x => simpa [importDesc, ImportDesc.Ok, Nat.blt_eq] using h
  | table tt => exact limits_sound h
  | mem lim => exact limits_sound h
  | global gt => trivial

theorem func_sound {C : Context} {f : Func} (h : func C f = true) : ∃ ft, FuncT C f ft := by
  simp only [func] at h
  split at h
  · cases h
  · rename_i ft hf
    simp only [Bool.and_eq_true] at h
    exact ⟨ft, hf, expr_sound h.2⟩

theorem elemMode_sound {C : Context} {t : RefType} {mode : ElemMode}
    (h : elemMode C t mode = true) : mode.Ok C t := by
  cases mode with
  | passive | declarative => trivial
  | active x off =>
    simp only [elemMode] at h
    split at h
    · cases h
    · rename_i tt ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨⟨tt, ht, h.1⟩, constExpr_sound h.2⟩

theorem dataMode_sound {C : Context} {mode : DataMode} (h : dataMode C mode = true) :
    mode.Ok C := by
  cases mode with
  | passive => trivial
  | active x off =>
    simp only [dataMode] at h
    split at h
    · cases h
    · exact ⟨⟨_, by assumption⟩, constExpr_sound h⟩

theorem exportDesc_sound {C : Context} {d : ExportDesc} (h : exportDesc C d = true) : d.Ok C := by
  cases d <;> simpa [exportDesc, ExportDesc.Ok, Nat.blt_eq] using h

theorem distinct_sound {names : List String} (h : distinct names = true) : names.Nodup := by
  induction names with
  | nil => exact List.nodup_nil
  | cons name names ih =>
    simp only [distinct, Bool.and_eq_true] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1, ih h.2⟩

end ValidatorProof

/-- Every accepted raw AST satisfies the reviewed module-validity judgment. -/
theorem validate_sound {m : Module} (h : validate m = true) : ModuleValid m := by
  simp only [validate, Bool.and_eq_true, and_assoc, List.all_eq_true] at h
  obtain ⟨hmemory, htypes, himports, hfuncs, htables, hmems, hglobals, helems, hdatas,
    helen, hdlen, hstart, hexports, hnames⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    simpa [Nat.blt_eq] using htypes f hf
  · intro im hi
    exact ValidatorProof.importDesc_sound (himports im hi)
  · intro f hf
    exact ValidatorProof.func_sound (hfuncs f hf)
  · intro tt ht
    exact ValidatorProof.limits_sound (htables tt ht)
  · intro lim hl
    exact ValidatorProof.limits_sound (hmems lim hl)
  · intro g hg
    exact ValidatorProof.constExpr_sound (hglobals g hg)
  · intro e he
    obtain ⟨hi, hm⟩ := helems e he
    exact ⟨fun ex hx => ValidatorProof.constExpr_sound (hi ex hx),
      ValidatorProof.elemMode_sound hm⟩
  · intro d hd
    exact ValidatorProof.dataMode_sound (hdatas d hd)
  · intro e he
    simpa [Nat.blt_eq] using helen e he
  · intro d hd
    simpa [Nat.blt_eq] using hdlen d hd
  · intro x hx
    simp only [hx] at hstart
    split at hstart
    · assumption
    · cases hstart
  · intro ex hx
    exact ValidatorProof.exportDesc_sound (hexports ex hx)
  · exact ValidatorProof.distinct_sound hnames
  · simpa [Nat.ble_eq] using hmemory

end FVA.Wasm.Valid
