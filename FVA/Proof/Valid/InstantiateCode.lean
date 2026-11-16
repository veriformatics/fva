import FVA.Proof.Valid.InstantiateAllocation

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

/-- Sequencing in one context: a tail typed where the sequence starts is typed after it (the
prefix only adds initializations). -/
theorem seq_append_pure {C : Context} {xs ys : List Instr} {a b c : List OpType}
    (hx : SeqT C xs ⟨a, b⟩) (hy : SeqT C ys ⟨b, c⟩) : SeqT C (xs ++ ys) ⟨a, c⟩ :=
  hx.append (hy.transport (Context.Entails.to_addSets C _))

/-- An offset, then `i32.const 0`, `i32.const n` and a three-operand segment instruction. -/
theorem segment_typed {C : Context} {off : Expr} {n : Nat} {init fin : Instr}
    (hoff : ExprT C off [.num .i32]) (hn : n < 2 ^ 32)
    (hinit : InstrT C init ⟨[i32, i32, i32], []⟩) (hfin : InstrT C fin ⟨[], []⟩) :
    SeqT C (off ++ [.iconst .w32 0, .iconst .w32 n, init, fin]) ⟨[], []⟩ := by
  obtain ⟨out, hs, hm⟩ := hoff
  have h₀ : SeqT C off ⟨[], [i32]⟩ := .sub hs hm
  have c₀ : SeqT C [.iconst .w32 0] ⟨[i32], [i32, i32]⟩ := by
    exact (SeqT.single (C := C) (InstrT.iconst (w := .w32) (n := 0) (by decide))).frame [i32]
  have c₁ : SeqT C [.iconst .w32 n] ⟨[i32, i32], [i32, i32, i32]⟩ := by
    exact (SeqT.single (C := C) (InstrT.iconst (w := .w32) hn)).frame [i32, i32]
  have all := seq_append_pure (seq_append_pure (seq_append_pure (seq_append_pure h₀ c₀) c₁)
    (SeqT.single hinit)) (SeqT.single hfin)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using all

theorem runElem_typed {m : Module} (hv : ModuleValid m) {e : Elem} {i : Nat}
    (he : m.elems[i]? = some e) : SeqT (moduleContext m) (runElem i e) ⟨[], []⟩ := by
  have hmem := List.mem_of_getElem? he
  have hmode := (hv.elems e hmem).2.2
  have hlookup : (moduleContext m).elems[i]? = some (e.type.close m.defTypes) := by
    simp [moduleContext, List.getElem?_map, he]
  cases hm : e.mode with
  | passive => simp only [runElem, hm]; exact .nil
  | declarative => simp only [runElem, hm]; exact SeqT.single (.elemDrop hlookup)
  | active x off =>
    simp only [hm, ElemMode.Ok] at hmode
    obtain ⟨⟨tt, ht, htype⟩, hex, -⟩ := hmode
    simpa only [runElem, hm] using segment_typed hex (hv.elemLengths e hmem)
      (InstrT.tableInit ht hlookup htype) (InstrT.elemDrop hlookup)

theorem runData_typed {m : Module} (hv : ModuleValid m) {d : Data} {i : Nat}
    (hd : m.datas[i]? = some d) : SeqT (moduleContext m) (runData i d) ⟨[], []⟩ := by
  have hmem := List.mem_of_getElem? hd
  have hmode := hv.datas d hmem
  have hidx : i < (moduleContext m).datas := lookup_lt hd
  cases hm : d.mode with
  | passive => simp only [runData, hm]; exact .nil
  | active x off =>
    simp only [hm, DataMode.Ok] at hmode
    obtain ⟨⟨lim, hl⟩, hex, -⟩ := hmode
    have hzero : 0 < (moduleContext m).mems.length :=
      Nat.lt_of_le_of_lt (Nat.zero_le x) (lookup_lt hl)
    have hm₀ := List.getElem?_eq_getElem hzero
    simpa only [runData, hm] using segment_typed hex (hv.dataLengths d hmem)
      (InstrT.memoryInit hm₀ hidx) (InstrT.dataDrop hidx)

theorem flatMap_typed {α : Type} {C : Context} (xs : List α) (f : α → List Instr)
    (h : ∀ x ∈ xs, SeqT C (f x) ⟨[], []⟩) : SeqT C (xs.flatMap f) ⟨[], []⟩ := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    exact seq_append_pure (h x (by simp)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem initCode_typed {m : Module} (hv : ModuleValid m) :
    SeqT (moduleContext m) (initCode m) ⟨[], []⟩ := by
  have he := flatMap_typed m.elems.zipIdx (fun p => runElem p.2 p.1) (by
    intro p hp
    exact runElem_typed hv (List.mem_zipIdx_iff_getElem?.mp hp))
  have hd := flatMap_typed m.datas.zipIdx (fun p => runData p.2 p.1) (by
    intro p hp
    exact runData_typed hv (List.mem_zipIdx_iff_getElem?.mp hp))
  apply seq_append_pure (seq_append_pure he hd)
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
