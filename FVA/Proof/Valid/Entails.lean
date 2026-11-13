import FVA.Spec.Valid.Instr

/-!
# Context transport for instruction typing (contract U28c T2)

`C.Entails D`: what typing reads of `C` holds in `D` — the same types, functions, tags, globals,
element types, labels and return type; tables and memories present with the same element types
(their minima may grow); at least the data segments and declared references; each local of `C`
in `D` with the same type, readable in `D` wherever it is readable in `C` (initialization only
grows: `sets`, or a run's flag). Typing transports along it, which gives both monotonicity in
local initialization and the store-growth transport of preservation.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

/-- The observations of a context used by instruction typing; table/memory minima may grow,
locals may only become initialized. -/
structure Context.Entails (C D : Context) : Prop where
  types : C.types = D.types
  funcs : C.funcs = D.funcs
  tags : C.tags = D.tags
  tables : ∀ (x : Nat) (tt : TableType), C.tables[x]? = some tt →
    ∃ tt' : TableType, D.tables[x]? = some tt' ∧ tt'.elem = tt.elem
  mems : ∀ (x : Nat) (lim : Limits), C.mems[x]? = some lim →
    ∃ lim' : Limits, D.mems[x]? = some lim'
  globals : C.globals = D.globals
  elems : C.elems = D.elems
  datas : C.datas ≤ D.datas
  locals : ∀ x lt, localAt C.locals x = some lt → ∃ lt', localAt D.locals x = some lt' ∧
    lt'.type = lt.type ∧
      (lt.set = true ∨ x ∈ C.sets ∨ C.dead = true → lt'.set = true ∨ x ∈ D.sets ∨ D.dead = true)
  labels : C.labels = D.labels
  return_ : C.return_ = D.return_
  refs : ∀ x ∈ C.refs, x ∈ D.refs
  dead : C.dead = true → D.dead = true

namespace Context.Entails

theorem refl (C : Context) : C.Entails C :=
  ⟨rfl, rfl, rfl, fun _ tt h => ⟨tt, h, rfl⟩, fun _ lim h => ⟨lim, h⟩, rfl, rfl,
    Nat.le_refl _, fun _ lt h => ⟨lt, h, rfl, id⟩, rfl, rfl, fun _ h => h, id⟩

theorem trans {C D E : Context} (h₁ : C.Entails D) (h₂ : D.Entails E) : C.Entails E := by
  refine ⟨h₁.types.trans h₂.types, h₁.funcs.trans h₂.funcs, h₁.tags.trans h₂.tags, ?_, ?_,
    h₁.globals.trans h₂.globals, h₁.elems.trans h₂.elems, Nat.le_trans h₁.datas h₂.datas, ?_,
    h₁.labels.trans h₂.labels, h₁.return_.trans h₂.return_, fun x hx => h₂.refs x (h₁.refs x hx),
    fun hd => h₂.dead (h₁.dead hd)⟩
  · intro x tt h
    obtain ⟨tt₁, h₁', he₁⟩ := h₁.tables x tt h
    obtain ⟨tt₂, h₂', he₂⟩ := h₂.tables x tt₁ h₁'
    exact ⟨tt₂, h₂', he₂.trans he₁⟩
  · intro x lim h
    obtain ⟨lim₁, h₁'⟩ := h₁.mems x lim h
    exact h₂.mems x lim₁ h₁'
  · intro x lt h
    obtain ⟨lt₁, h₁', ht₁, hr₁⟩ := h₁.locals x lt h
    obtain ⟨lt₂, h₂', ht₂, hr₂⟩ := h₂.locals x lt₁ h₁'
    exact ⟨lt₂, h₂', ht₂.trans ht₁, fun hr => hr₂ (hr₁ hr)⟩

theorem withLabel {C D : Context} (h : C.Entails D) (ts : List ValType) :
    (C.withLabel ts).Entails (D.withLabel ts) :=
  { h with labels := congrArg (ts :: ·) h.labels }

theorem addSets_mono {C D : Context} (h : C.Entails D) {xs ys : List Nat}
    (hs : ∀ x ∈ xs, x ∈ ys) : (C.addSets xs).Entails (D.addSets ys) := by
  refine { h with locals := ?_ }
  intro x lt hx
  obtain ⟨lt', hx', ht, hr⟩ := h.locals x lt hx
  refine ⟨lt', hx', ht, ?_⟩
  simp only [Context.addSets, List.mem_append, List.mem_reverse]
  rintro (hs' | (hs' | hs') | hs')
  · rcases hr (.inl hs') with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl (.inr h'))
    · exact .inr (.inr h')
  · exact .inr (.inl (.inl (hs x hs')))
  · rcases hr (.inr (.inl hs')) with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl (.inr h'))
    · exact .inr (.inr h')
  · rcases hr (.inr (.inr hs')) with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl (.inr h'))
    · exact .inr (.inr h')

theorem addSets {C D : Context} (h : C.Entails D) (xs : List Nat) :
    (C.addSets xs).Entails (D.addSets xs) :=
  h.addSets_mono fun _ hx => hx

theorem withControl {C D : Context} (h : C.Entails D) (ls : List (List ValType))
    (ret : Option (List ValType)) :
    ({ C with labels := ls, return_ := ret } : Context).Entails
      { D with labels := ls, return_ := ret } :=
  { h with labels := rfl, return_ := rfl }

theorem withReturn {C D : Context} (h : C.Entails D) (ret : Option (List ValType)) :
    ({ C with return_ := ret } : Context).Entails { D with return_ := ret } :=
  { h with return_ := rfl }

/-- A body's context: the same locals on both sides, `C`'s initializations included in `D`'s. -/
theorem withBody {C D : Context} (h : C.Entails D) (hs : ∀ x ∈ C.sets, x ∈ D.sets)
    (ls : List (Nat × LocalType)) (labels : List (List ValType)) (ret : Option (List ValType)) :
    ({ C with locals := ls, labels := labels, return_ := ret } : Context).Entails
      { D with locals := ls, labels := labels, return_ := ret } :=
  { h with
    locals := fun x lt hx => ⟨lt, hx, rfl, fun hr => by
      rcases hr with h' | h' | h'
      · exact .inl h'
      · exact .inr (.inl (hs x h'))
      · exact .inr (.inr (h.dead h'))⟩
    labels := rfl
    return_ := rfl }

theorem blockType {C D : Context} (h : C.Entails D) (bt : BlockType) :
    C.blockType bt = D.blockType bt := by
  cases bt <;> simp only [Context.blockType, Context.typeAt, Context.close, h.types]

theorem catchOK {C D : Context} (h : C.Entails D) {c : Catch} (hc : CatchOK C c) :
    CatchOK D c := by
  cases c <;> simpa only [CatchOK, Context.tagType, ← h.tags, ← h.labels] using hc

end Context.Entails

theorem Context.addSets_nil (C : Context) : C.addSets [] = C := rfl

theorem Context.Entails.addSets_nil (C : Context) : C.Entails (C.addSets []) :=
  Context.Entails.refl C

theorem Context.addSets_addSets (C : Context) (xs ys : List Nat) :
    (C.addSets xs).addSets ys = C.addSets (xs ++ ys) := by
  simp only [Context.addSets, List.reverse_append, List.append_assoc]

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
  | refNull hs =>
    simpa only [h.types] using InstrT.refNull (C := D) (by simpa only [← h.types] using hs)
  | refIsNull => exact .refIsNull
  | refFunc hf hr => exact .refFunc (by simpa only [← h.funcs] using hf) (h.refs _ hr)
  | refAsNonNull => exact .refAsNonNull
  | drop => exact .drop
  | select hi => exact .select hi
  | selectT hs =>
    simpa only [Context.close, h.types] using
      InstrT.selectT (C := D) (by simpa only [← h.types] using hs)
  | localGet hx hs =>
    obtain ⟨lt', hx', ht, hr⟩ := h.locals _ _ hx
    simpa only [ht] using InstrT.localGet hx' (hr hs)
  | localSet hx =>
    obtain ⟨lt', hx', ht, -⟩ := h.locals _ _ hx
    simpa only [ht] using InstrT.localSet hx'
  | localTee hx =>
    obtain ⟨lt', hx', ht, -⟩ := h.locals _ _ hx
    simpa only [ht] using InstrT.localTee hx'
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
    exact .tableCopy hx' hy' (by rw [hex, hey]; exact he)
  | tableInit hx hy he =>
    obtain ⟨tt, hx', het⟩ := h.tables _ _ hx
    exact .tableInit hx' (by simpa only [← h.elems] using hy) (by rw [het]; exact he)
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
  | brOnNull hl => exact .brOnNull (by simpa only [← h.labels] using hl)
  | brOnNonNull hl => exact .brOnNonNull (by simpa only [← h.labels] using hl)
  | return_ hi => exact .return_ (by simpa only [← h.return_] using hi)
  | call hi => exact .call (by simpa only [Context.funcType, ← h.funcs] using hi)
  | callIndirect ht he hy =>
    obtain ⟨tt, ht', he'⟩ := h.tables _ _ ht
    exact .callIndirect ht' (by rw [he']; exact he)
      (by simpa only [Context.typeAt, ← h.types] using hy)
  | callRef hy he => exact .callRef (by simpa only [← h.types] using hy) he
  | returnCall hf hr hs =>
    exact .returnCall (by simpa only [Context.funcType, ← h.funcs] using hf)
      (by simpa only [← h.return_] using hr) hs
  | returnCallIndirect ht he hy hr hs =>
    obtain ⟨tt, ht', he'⟩ := h.tables _ _ ht
    exact .returnCallIndirect ht' (by rw [he']; exact he)
      (by simpa only [Context.typeAt, ← h.types] using hy)
      (by simpa only [← h.return_] using hr) hs
  | returnCallRef hy he hr hs =>
    exact .returnCallRef (by simpa only [← h.types] using hy) he
      (by simpa only [← h.return_] using hr) hs
  | throw hx => exact .throw (by simpa only [Context.tagType, ← h.tags] using hx)
  | throwRef => exact .throwRef
  | tryTable hb hs hc ih =>
    exact .tryTable (by simpa only [← h.blockType] using hb) (ih (h.withLabel _))
      (fun c hc' => h.catchOK (hc c hc'))
  | nil => exact .nil
  | snoc hs hm hi ihs ihi =>
    rename_i D h
    exact .snoc (ihs h) hm (ihi (h.addSets _))
  | sub hs hm ih =>
    rename_i D h
    exact .sub (ih h) hm

theorem SeqT.transport {C : Context} {es : List Instr} {st : StackType} (hs : SeqT C es st)
    {D : Context} (h : C.Entails D) : SeqT D es st := by
  induction hs using SeqT.rec (motive_1 := fun _ _ _ _ => True) generalizing D <;> try trivial
  case nil => exact .nil
  case snoc hs hm hi ihs _ => exact .snoc (ihs h) hm (hi.transport (h.addSets _))
  case sub hs hm ih => exact .sub (ih h) hm

end FVA.Wasm.Valid
