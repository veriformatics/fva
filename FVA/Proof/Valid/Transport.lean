import FVA.Proof.Valid.Sequence

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- The observations of a context used by instruction typing; table/memory minima may grow. -/
structure Context.Entails (C D : Context) : Prop where
  types : C.types = D.types
  funcs : C.funcs = D.funcs
  tables : ∀ (x : Nat) (tt : TableType), C.tables[x]? = some tt →
    ∃ tt' : TableType, D.tables[x]? = some tt' ∧ tt'.elem = tt.elem
  mems : ∀ (x : Nat) (lim : Limits), C.mems[x]? = some lim →
    ∃ lim' : Limits, D.mems[x]? = some lim'
  globals : C.globals = D.globals
  elems : C.elems = D.elems
  datas : C.datas ≤ D.datas
  locals : ∀ x, localAt C.locals x = localAt D.locals x
  labels : C.labels = D.labels
  return_ : C.return_ = D.return_
  refs : ∀ x ∈ C.refs, x ∈ D.refs

namespace Context.Entails

theorem refl (C : Context) : C.Entails C :=
  ⟨rfl, rfl, fun _ tt h => ⟨tt, h, rfl⟩, fun _ lim h => ⟨lim, h⟩,
    rfl, rfl, Nat.le_refl _, fun _ => rfl, rfl, rfl, fun _ h => h⟩

theorem withLabel {C D : Context} (h : C.Entails D) (ts : List ValType) :
    (C.withLabel ts).Entails (D.withLabel ts) :=
  { h with labels := congrArg (ts :: ·) h.labels }

theorem withLocals {C D : Context} (h : C.Entails D) (ls : List (Nat × ValType)) :
    ({ C with locals := ls } : Context).Entails { D with locals := ls } :=
  { h with locals := fun _ => rfl }

theorem withControl {C D : Context} (h : C.Entails D) (ls : List (List ValType))
    (ret : Option (List ValType)) :
    ({ C with labels := ls, return_ := ret } : Context).Entails
      { D with labels := ls, return_ := ret } :=
  { h with labels := rfl, return_ := rfl }

theorem withReturn {C D : Context} (h : C.Entails D) (ret : Option (List ValType)) :
    ({ C with return_ := ret } : Context).Entails { D with return_ := ret } :=
  { h with return_ := rfl }

theorem blockType {C D : Context} (h : C.Entails D) (bt : BlockType) :
    C.blockType bt = D.blockType bt := by
  cases bt <;> simp only [Context.blockType, h.types]

end Context.Entails

theorem InstrT.transport {C : Context} {i : Instr} {st : StackType} (hi : InstrT C i st)
    {D : Context} (h : C.Entails D) : InstrT D i st := by
  induction hi using InstrT.rec
    (motive_2 := fun C es st _ => ∀ {D}, C.Entails D → SeqT D es st) generalizing D with
  | iconst hi => exact .iconst hi
  | fconst hi => exact .fconst hi
  | iunop hi => exact .iunop hi
  | ibinop => exact .ibinop
  | itestEqz => exact .itestEqz
  | irelop => exact .irelop
  | funop => exact .funop
  | fbinop => exact .fbinop
  | frelop => exact .frelop
  | cvtop => exact .cvtop
  | refNull => exact .refNull
  | refIsNull => exact .refIsNull
  | refFunc hf hr => exact .refFunc (by simpa only [← h.funcs] using hf) (h.refs _ hr)
  | drop => exact .drop
  | select hi => exact .select hi
  | selectT => exact .selectT
  | localGet hi => exact .localGet (by simpa only [← h.locals] using hi)
  | localSet hi => exact .localSet (by simpa only [← h.locals] using hi)
  | localTee hi => exact .localTee (by simpa only [← h.locals] using hi)
  | globalGet hi => exact .globalGet (by simpa only [← h.globals] using hi)
  | globalSet hi => exact .globalSet (by simpa only [← h.globals] using hi)
  | tableGet hi =>
    obtain ⟨tt, hx, he⟩ := h.tables _ _ hi
    simpa only [← he] using InstrT.tableGet hx
  | tableSet hi =>
    obtain ⟨tt, hx, he⟩ := h.tables _ _ hi
    simpa only [← he] using InstrT.tableSet hx
  | tableSize hi => obtain ⟨tt, hx, _⟩ := h.tables _ _ hi; exact .tableSize hx
  | tableGrow hi =>
    obtain ⟨tt, hx, he⟩ := h.tables _ _ hi
    simpa only [← he] using InstrT.tableGrow hx
  | tableFill hi =>
    obtain ⟨tt, hx, he⟩ := h.tables _ _ hi
    simpa only [← he] using InstrT.tableFill hx
  | tableCopy hx hy he =>
    obtain ⟨tx, hx', hex⟩ := h.tables _ _ hx
    obtain ⟨ty, hy', hey⟩ := h.tables _ _ hy
    exact .tableCopy hx' hy' (hex.trans (he.trans hey.symm))
  | tableInit hx hy he =>
    obtain ⟨tt, hx', het⟩ := h.tables _ _ hx
    exact .tableInit hx' (by simpa only [← h.elems] using hy) (het.trans he)
  | elemDrop hi => exact .elemDrop (by simpa only [← h.elems] using hi)
  | load hm ha => obtain ⟨lim, hm'⟩ := h.mems _ _ hm; exact .load hm' ha
  | loadPacked hm hl ha =>
    obtain ⟨lim, hm'⟩ := h.mems _ _ hm
    exact .loadPacked hm' hl ha
  | store hm ha => obtain ⟨lim, hm'⟩ := h.mems _ _ hm; exact .store hm' ha
  | storePacked hm hl ha =>
    obtain ⟨lim, hm'⟩ := h.mems _ _ hm
    exact .storePacked hm' hl ha
  | memorySize hm => obtain ⟨lim, hm'⟩ := h.mems _ _ hm; exact .memorySize hm'
  | memoryGrow hm => obtain ⟨lim, hm'⟩ := h.mems _ _ hm; exact .memoryGrow hm'
  | memoryFill hm => obtain ⟨lim, hm'⟩ := h.mems _ _ hm; exact .memoryFill hm'
  | memoryCopy hm => obtain ⟨lim, hm'⟩ := h.mems _ _ hm; exact .memoryCopy hm'
  | memoryInit hm hd =>
    obtain ⟨lim, hm'⟩ := h.mems _ _ hm
    exact .memoryInit hm' (Nat.lt_of_lt_of_le hd h.datas)
  | dataDrop hd => exact .dataDrop (Nat.lt_of_lt_of_le hd h.datas)
  | nop => exact .nop
  | unreachable => exact .unreachable
  | block hb hs ih =>
    exact .block (by simpa only [← h.blockType] using hb) (ih (h.withLabel _))
  | loop hb hs ih =>
    exact .loop (by simpa only [← h.blockType] using hb) (ih (h.withLabel _))
  | if_ hb h₁ h₂ ih₁ ih₂ =>
    exact .if_ (by simpa only [← h.blockType] using hb)
      (ih₁ (h.withLabel _)) (ih₂ (h.withLabel _))
  | br hi => exact .br (by simpa only [← h.labels] using hi)
  | brIf hi => exact .brIf (by simpa only [← h.labels] using hi)
  | brTable hi => exact .brTable (by simpa only [← h.labels] using hi)
  | return_ hi => exact .return_ (by simpa only [← h.return_] using hi)
  | call hi => exact .call (by simpa only [← h.funcs] using hi)
  | callIndirect ht he hy =>
    obtain ⟨tt, ht', he'⟩ := h.tables _ _ ht
    exact .callIndirect ht' (he'.trans he) (by simpa only [← h.types] using hy)
  | nil => exact .nil
  | snoc hs hm hi ihs ihi =>
    rename_i D h
    exact .snoc (ihs h) hm (ihi h)
  | sub hs hm ih =>
    rename_i D h
    exact .sub (ih h) hm

theorem SeqT.transport {C : Context} {es : List Instr} {st : StackType} (hs : SeqT C es st)
    {D : Context} (h : C.Entails D) : SeqT D es st := by
  obtain ⟨a, b⟩ := st
  induction es using List.reverseRecOn generalizing b with
  | nil => exact SeqT.nil_iff.mpr (SeqT.nil_iff.mp hs)
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hs, hm, he⟩ := SeqT.snoc_iff.mp hs
    exact .sub (.snoc (ih _ hs) hm (he.transport h)) hout

end FVA.Wasm.Valid

namespace FVA.Wasm.Exec.Store.Extends

open FVA.Wasm

theorem refl (s : Store) : s.Extends s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ x hx => ⟨x, hx, rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl, rfl, Nat.le_refl _⟩
  · exact fun _ x hx => ⟨x, hx, rfl, Nat.le_refl _⟩
  · exact fun _ x hx => ⟨x, hx, rfl, Or.inr rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl, Or.inl rfl⟩
  · exact fun _ x hx => ⟨x, hx, Or.inl rfl⟩

theorem funcs_length {s s' : Store} (h : s.Extends s') : s.funcs.length ≤ s'.funcs.length := by
  by_contra hn
  have hi : s'.funcs.length < s.funcs.length := Nat.lt_of_not_ge hn
  obtain ⟨fi, hf, _⟩ := h.1 _ _ (List.getElem?_eq_getElem hi)
  simp only [List.getElem?_eq_none (Nat.le_refl _)] at hf
  cases hf

theorem value {s s' : Store} (h : s.Extends s') {v : Val} {t : ValType}
    (hv : v.HasType s t) : v.HasType s' t := by
  cases v <;> cases t <;> try (cases ‹NumType› <;> exact hv)
  all_goals try exact hv
  case ref.num r n => cases r <;> cases hv
  case ref.ref r rt =>
    cases r <;> cases rt <;> try exact hv
    exact Nat.lt_of_lt_of_le hv h.funcs_length

theorem values {s s' : Store} (h : s.Extends s') {vs : List Val} {ts : List ValType}
    (hv : List.Forall₂ (Val.HasType s) vs ts) : List.Forall₂ (Val.HasType s') vs ts := by
  induction hv with
  | nil => exact .nil
  | cons hv hs ih => exact .cons (h.value hv) ih

end FVA.Wasm.Exec.Store.Extends
