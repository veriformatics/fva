import FVA.Proof.Valid.InstantiateAllocation

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

theorem const_add_globals {C : Context} {i : Instr} {st : StackType}
    (hi : InstrT C i st) (hc : ConstInstr C i) (more : List GlobalType) :
    InstrT { C with globals := C.globals ++ more } i st := by
  cases hi <;> simp only [ConstInstr] at hc
  case iconst hn => exact .iconst hn
  case fconst hn => exact .fconst hn
  case refNull => exact .refNull
  case refFunc hf hr => exact .refFunc hf hr
  case globalGet hg => exact .globalGet (lookup_append hg)

theorem init_expr {m : Module} {e : Expr} {t : ValType}
    (he : ExprT { moduleContext m with globals := importGlobals m.imports } e [t])
    (hc : ConstExpr { moduleContext m with globals := importGlobals m.imports } e) :
    SeqT (moduleContext m) e ⟨[], [.val t]⟩ := by
  obtain ⟨i, rfl, hci, hi⟩ := const_singleton he hc
  simpa only [moduleContext] using
    SeqT.single (const_add_globals hi hci (m.globals.map (·.type)))

theorem runElem_typed {m : Module} (hv : ModuleValid m) {e : Elem} {i : Nat}
    (he : m.elems[i]? = some e) : SeqT (moduleContext m) (runElem i e) ⟨[], []⟩ := by
  have hmem := List.mem_of_getElem? he
  have hmode := (hv.elems e hmem).2
  have hlookup : (moduleContext m).elems[i]? = some e.type := by
    simp [moduleContext, List.getElem?_map, he]
  cases hm : e.mode with
  | passive => simp only [runElem, hm]; exact .nil
  | declarative => simp only [runElem, hm]; exact SeqT.single (.elemDrop hlookup)
  | active x off =>
    simp only [hm, ElemMode.Ok] at hmode
    obtain ⟨⟨tt, ht, htype⟩, hex, hconst⟩ := hmode
    have h₀ := init_expr hex hconst
    have h₁ := SeqT.snoc (t₀ := [i32]) h₀ List.Forall₂.nil
      (InstrT.iconst (w := .w32) (n := 0) (by decide))
    have h₂ := SeqT.snoc (t₀ := [i32, i32]) h₁ List.Forall₂.nil
      (InstrT.iconst (w := .w32) (hv.elemLengths e hmem))
    have h₃ := SeqT.snoc (t₀ := []) h₂ (Matches.refl [i32, i32, i32])
      (InstrT.tableInit ht hlookup htype)
    have h₄ := SeqT.snoc (t₀ := []) h₃ List.Forall₂.nil (InstrT.elemDrop hlookup)
    simpa [runElem, hm, List.append_assoc] using h₄

theorem runData_typed {m : Module} (hv : ModuleValid m) {d : Data} {i : Nat}
    (hd : m.datas[i]? = some d) : SeqT (moduleContext m) (runData i d) ⟨[], []⟩ := by
  have hmem := List.mem_of_getElem? hd
  have hmode := hv.datas d hmem
  have hidx : i < (moduleContext m).datas := lookup_lt hd
  cases hm : d.mode with
  | passive => simp only [runData, hm]; exact .nil
  | active x off =>
    simp only [hm, DataMode.Ok] at hmode
    obtain ⟨⟨lim, hl⟩, hex, hconst⟩ := hmode
    have hzero : 0 < (moduleContext m).mems.length :=
      Nat.lt_of_le_of_lt (Nat.zero_le x) (lookup_lt hl)
    have hm₀ := List.getElem?_eq_getElem hzero
    have h₀ := init_expr hex hconst
    have h₁ := SeqT.snoc (t₀ := [i32]) h₀ List.Forall₂.nil
      (InstrT.iconst (w := .w32) (n := 0) (by decide))
    have h₂ := SeqT.snoc (t₀ := [i32, i32]) h₁ List.Forall₂.nil
      (InstrT.iconst (w := .w32) (hv.dataLengths d hmem))
    have h₃ := SeqT.snoc (t₀ := []) h₂ (Matches.refl [i32, i32, i32])
      (InstrT.memoryInit hm₀ hidx)
    have h₄ := SeqT.snoc (t₀ := []) h₃ List.Forall₂.nil (InstrT.dataDrop hidx)
    simpa [runData, hm, List.append_assoc] using h₄

theorem flatMap_typed {α : Type} {C : Context} (xs : List α) (f : α → List Instr)
    (h : ∀ x ∈ xs, SeqT C (f x) ⟨[], []⟩) : SeqT C (xs.flatMap f) ⟨[], []⟩ := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    exact SeqT.append (h x (by simp)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem initCode_typed {m : Module} (hv : ModuleValid m) :
    SeqT (moduleContext m) (initCode m) ⟨[], []⟩ := by
  have he := flatMap_typed m.elems.zipIdx (fun p => runElem p.2 p.1) (by
    intro p hp
    exact runElem_typed hv (List.mem_zipIdx_iff_getElem?.mp hp))
  have hd := flatMap_typed m.datas.zipIdx (fun p => runData p.2 p.1) (by
    intro p hp
    exact runData_typed hv (List.mem_zipIdx_iff_getElem?.mp hp))
  apply SeqT.append (SeqT.append he hd)
  cases hstart : m.start with
  | none => exact .nil
  | some x => exact SeqT.single (InstrT.call (hv.start x hstart))

theorem empty_frame {s : Store} {inst : ModuleInst} {C : Context} (hi : ModuleInstT s inst C) :
    FrameT s ⟨[], inst⟩ C := by
  refine ⟨C, [], hi, .nil, ?_⟩
  have hn := hi.noLocals
  cases C
  simp_all

end FVA.Wasm.Valid.InitProof
