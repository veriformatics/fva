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

theorem typesSeq_sound {gs : List RecType} {x : Nat} (h : typesSeq gs x = true) :
    TypesSeq gs x := by
  induction gs generalizing x with
  | nil => trivial
  | cons g gs ih =>
    simp only [typesSeq, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun f hf => ?_, ih h.2⟩
    obtain ⟨hp, hr⟩ := h.1 f hf
    exact ⟨fun t ht => valSrc_sound (hp t ht), fun t ht => valSrc_sound (hr t ht)⟩

theorem tagType_sound {C : Context} {x : Nat} (h : tagType C x = true) :
    ∃ ts, C.typeAt x = some ⟨ts, []⟩ := by
  simp only [tagType] at h
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

theorem importDesc_sound {C : Context} {d : ImportDesc} (h : importDesc C d = true) : d.Ok C := by
  cases d with
  | func x =>
    simp only [importDesc, Option.isSome_iff_exists] at h
    exact h
  | table tt =>
    simp only [importDesc, Bool.and_eq_true] at h
    exact ⟨limits_sound h.1, heapSrc_sound h.2⟩
  | mem lim => exact limits_sound h
  | global gt => exact valSrc_sound h
  | tag x => exact tagType_sound h

theorem globals_sound {C : Context} {dts : List DefType} {gs : List Global}
    (h : globals C dts gs = true) : ∀ k (g : Global), gs[k]? = some g →
      g.type.val.Src dts.length ∧
      ExprT { C with globals := C.globals ++ (gs.take k).map (·.type.close dts) } g.init
        [(g.type.close dts).val] ∧
      ConstExpr { C with globals := C.globals ++ (gs.take k).map (·.type.close dts) } g.init := by
  induction gs generalizing C with
  | nil => intro k g hg; simp at hg
  | cons g₀ gs ih =>
    simp only [globals, Bool.and_eq_true] at h
    obtain ⟨⟨hsrc, hc⟩, hrest⟩ := h
    intro k g hg
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      have := constExpr_sound hc
      simpa using ⟨valSrc_sound hsrc, this.1, this.2⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      have := ih hrest k g hg
      simpa [List.take_succ_cons, List.append_assoc] using this

theorem func_sound {C : Context} {f : Func} (h : func C f = true) : ∃ dt, FuncT C f dt := by
  simp only [func] at h
  split at h
  · cases h
  · rename_i ft hf
    simp only [Context.typeAt, Option.bind_eq_some_iff] at hf
    obtain ⟨dt, hdt, he⟩ := hf
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨dt, hdt, ft, he, fun l hl => valSrc_sound (h.1 l hl), expr_sound h.2⟩

theorem elemMode_sound {C : Context} {t : RefType} {mode : ElemMode}
    (h : elemMode C t mode = true) : mode.Ok C t := by
  cases mode with
  | passive | declarative => trivial
  | active x off =>
    simp only [elemMode] at h
    split at h
    · cases h
    · rename_i tt ht
      simp only [Bool.and_eq_true] at h
      exact ⟨⟨tt, ht, subType_sound h.1⟩, constExpr_sound h.2⟩

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
  obtain ⟨htypes, hmemory, himports, htags, hglobals, hmems, htables, hfuncs, helems, hdatas,
    helen, hdlen, hstart, hexports, hnames⟩ := h
  refine ⟨ValidatorProof.typesSeq_sound htypes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro im hi
    exact ValidatorProof.importDesc_sound (himports im hi)
  · intro t ht
    exact ValidatorProof.tagType_sound (htags t ht)
  · intro k g hg
    exact ValidatorProof.globals_sound hglobals k g hg
  · intro lim hl
    exact ValidatorProof.limits_sound (hmems lim hl)
  · intro t ht
    obtain ⟨hl, hs, hc⟩ := htables t ht
    have := ValidatorProof.constExpr_sound hc
    have h0 : globalContext m 0 =
        { moduleContext m with globals := importGlobals m.defTypes m.imports } := by
      simp [globalContext]
    rw [h0]
    exact ⟨ValidatorProof.limits_sound hl, ValidatorProof.heapSrc_sound hs, this.1, this.2⟩
  · intro f hf
    exact ValidatorProof.func_sound (hfuncs f hf)
  · intro e he
    obtain ⟨hs, hi, hm⟩ := helems e he
    exact ⟨ValidatorProof.heapSrc_sound hs, fun ex hx => ValidatorProof.constExpr_sound (hi ex hx),
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
