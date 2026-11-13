import FVA.Proof.Valid.Transport

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem forall₂_lookup_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {i : Nat} {x : α} (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab h ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst x
              exact ⟨b, rfl, hab⟩
    | succ i => exact ih hx

theorem forall₂_lookup_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {i : Nat} {y : β} (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ R x y :=
  forall₂_lookup_left (List.Forall₂.flip h) hy

theorem forall₂_exists_right {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop}
    {T : β → γ → Prop} {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (step : ∀ x y, R x y → ∃ z, S x z ∧ T y z) :
    ∃ zs, List.Forall₂ S xs zs ∧ List.Forall₂ T ys zs := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons h hs ih =>
    obtain ⟨z, hs', ht'⟩ := step _ _ h
    obtain ⟨zs, hss, hts⟩ := ih
    exact ⟨z :: zs, .cons hs' hss, .cons ht' hts⟩

/-- A context's function types against an instance's defined types (`ModuleInstT.types`). -/
theorem forall₂_expand_getElem? {dts : List DefType} {fts : List FuncType}
    (h : List.Forall₂ (fun dt ft => dt.expand = some ft) dts fts) (x : Nat) :
    fts[x]? = dts[x]?.bind DefType.expand := by
  induction h generalizing x with
  | nil => simp
  | cons hd _ ih => cases x with
    | zero => simp [hd]
    | succ x => simpa using ih x

theorem listExtends_length {α : Type} {R : α → α → Prop} {xs ys : List α}
    (h : ListExtends R xs ys) : xs.length ≤ ys.length := by
  by_contra hn
  have hi : ys.length < xs.length := Nat.lt_of_not_ge hn
  obtain ⟨y, hy, _⟩ := h _ _ (List.getElem?_eq_getElem hi)
  simp only [List.getElem?_eq_none (Nat.le_refl _)] at hy
  cases hy

theorem ExternValT.extends {s s' : Store} (h : s.Extends s') {v : ExternVal}
    (hv : ExternValT s v) : ExternValT s' v := by
  cases v with
  | func a => exact Nat.lt_of_lt_of_le hv (listExtends_length h.1)
  | table a => exact Nat.lt_of_lt_of_le hv (listExtends_length h.2.1)
  | mem a => exact Nat.lt_of_lt_of_le hv (listExtends_length h.2.2.1)
  | global a => exact Nat.lt_of_lt_of_le hv (listExtends_length h.2.2.2.1)
  | tag a => exact Nat.lt_of_lt_of_le hv (listExtends_length h.2.2.2.2.2.2.1)

theorem ModuleInstT.extends {s s' : Store} {inst : ModuleInst} {C : Context}
    (hi : ModuleInstT s inst C) (h : s.Extends s') :
    ∃ D, ModuleInstT s' inst D ∧ C.Entails D := by
  obtain ⟨tts, htts, htts'⟩ := forall₂_exists_right (S := fun a tt =>
    ∃ ti, s'.tables[a]? = some ti ∧ ti.type = tt)
    (T := fun tt tt' : TableType => tt'.elem = tt.elem) hi.tables (by
      rintro a tt ⟨ti, hti, rfl⟩
      obtain ⟨ti', hti', he⟩ := h.2.1 _ _ hti
      exact ⟨ti'.type, ⟨ti', hti', rfl⟩, he.1⟩)
  obtain ⟨mls, hmls, hmls'⟩ := forall₂_exists_right (S := fun a lim =>
    ∃ mi, s'.mems[a]? = some mi ∧ (⟨mi.pages, mi.max⟩ : Limits) = lim)
    (T := fun _ _ : Limits => True) hi.mems (by
      rintro a lim ⟨mi, hmi, rfl⟩
      obtain ⟨mi', hmi', he⟩ := h.2.2.1 _ _ hmi
      exact ⟨⟨mi'.pages, mi'.max⟩, ⟨mi', hmi', rfl⟩, trivial⟩)
  let D : Context := { C with tables := tts, mems := mls }
  refine ⟨D, ?_, ?_⟩
  · refine ⟨hi.types, hi.typesOk, ?_, ?_, htts, hmls, ?_, ?_, ?_, ?_, hi.exportNames,
      hi.refs, hi.noLocals, hi.noSets, hi.noDead, hi.noLabels, hi.noReturn⟩
    · apply List.Forall₂.imp _ hi.tags
      rintro a dt ⟨ti, hti, rfl⟩
      obtain ⟨ti', hti', rfl⟩ := h.2.2.2.2.2.2.1 _ _ hti
      exact ⟨_, hti', rfl⟩
    · apply List.Forall₂.imp _ hi.funcs
      rintro a dt ⟨fi, hfi, hft⟩
      obtain ⟨fi', hfi', rfl⟩ := h.1 _ _ hfi
      exact ⟨_, hfi', hft⟩
    · apply List.Forall₂.imp _ hi.globals
      rintro a gt ⟨gi, hgi, hsub⟩
      obtain ⟨gi', hgi', he⟩ := h.2.2.2.1 _ _ hgi
      exact ⟨gi', hgi', he.1 ▸ hsub⟩
    · apply List.Forall₂.imp _ hi.elems
      rintro a rt ⟨ei, hei, rfl⟩
      obtain ⟨ei', hei', he⟩ := h.2.2.2.2.1 _ _ hei
      exact ⟨ei', hei', he.1⟩
    · exact ⟨hi.datas.1, fun a ha =>
        Nat.lt_of_lt_of_le (hi.datas.2 a ha) (listExtends_length h.2.2.2.2.2.1)⟩
    · exact fun ex hex => ExternValT.extends h (hi.exports ex hex)
  · refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, Nat.le_refl _,
      fun _ lt hx => ⟨lt, hx, rfl, id⟩, rfl, rfl, fun _ hx => hx, id⟩
    · intro x tt hx
      exact forall₂_lookup_left htts' hx
    · intro x lim hx
      obtain ⟨lim', hl, _⟩ := forall₂_lookup_left hmls' hx
      exact ⟨lim', hl⟩

theorem LocalOK.extends {s s' : Store} (h : s.Extends s') {ov : Option Val} {lt : LocalType}
    (hl : LocalOK s ov lt) : LocalOK s' ov lt := by
  cases ov with
  | none => exact hl
  | some v => exact ⟨hl.1, hl.2.1, h.value hl.2.2⟩

theorem FrameT.extends {s s' : Store} {f : Frame} {C : Context}
    (hf : FrameT s f C) (h : s.Extends s') : ∃ D, FrameT s' f D ∧ C.Entails D := by
  obtain ⟨C₀, lts, hi, hvs, rfl⟩ := hf
  obtain ⟨D₀, hi', he⟩ := hi.extends h
  refine ⟨{ D₀ with locals := lts.map (1, ·) },
    ⟨D₀, lts, hi', hvs.imp fun _ _ hl => hl.extends h, rfl⟩, ?_⟩
  have := he.withBody (by simp [hi.noSets]) (lts.map (1, ·)) C₀.labels C₀.return_
  have hC : ({ C₀ with locals := lts.map (1, ·), labels := C₀.labels, return_ := C₀.return_ } :
      Context) = { C₀ with locals := lts.map (1, ·) } := rfl
  have hD : ({ D₀ with locals := lts.map (1, ·), labels := C₀.labels, return_ := C₀.return_ } :
      Context) = { D₀ with locals := lts.map (1, ·) } := by
    rw [← he.labels, ← he.return_]
  rw [hC, hD] at this
  exact this

theorem FuncT.transport {C D : Context} {f : Func} {dt : DefType}
    (hf : FuncT C f dt) (h : C.Entails D) (hs : ∀ x ∈ C.sets, x ∈ D.sets) : FuncT D f dt := by
  obtain ⟨hdt, ft, he, hl, ts, hb, hm⟩ := hf
  refine ⟨by simpa only [← h.types] using hdt, ft, he, by simpa only [← h.types] using hl, ts,
    ?_, hm⟩
  have := hb.transport (h.withBody hs
    (ft.params.map (1, ⟨true, ·⟩) ++ f.locals.map fun l => (l.1, ⟨l.2.defaultable, C.close l.2⟩))
    [ft.results] (some ft.results))
  simpa only [Context.close, h.types] using this

theorem FuncInstOK.extends {s s' : Store} {fi : FuncInst}
    (hf : FuncInstOK s fi) (h : s.Extends s') : FuncInstOK s' fi := by
  cases fi with
  | host dt id => exact hf
  | wasm dt inst code =>
    obtain ⟨hdt, C, hi, hc⟩ := hf
    obtain ⟨D, hi', he⟩ := hi.extends h
    exact ⟨hdt, D, hi', hc.transport he (by simp [hi.noSets])⟩

theorem AInstrT.transport {s s' : Store} {C D : Context} {i : AInstr} {st : StackType}
    (hi : AInstrT s C i st) (he : s.Extends s') (hc : C.Entails D) : AInstrT s' D i st := by
  induction hi using AInstrT.rec
    (motive_2 := fun C es st _ => ∀ {s' D}, s.Extends s' → C.Entails D → ASeqT s' D es st)
    generalizing s' D with
  | plain hi => exact .plain (hi.transport hc)
  | refFuncAddr ha => exact .refFuncAddr (he.funcs_get ha)
  | refExternAddr => exact .refExternAddr
  | refNullAddr => exact .refNullAddr
  | refExnAddr ha => exact .refExnAddr (Nat.lt_of_lt_of_le ha he.exns_length)
  | trap => exact .trap
  | invoke hi hft => exact .invoke (he.funcs_get hi) hft
  | label hn hcont hb ih => exact .label hn (hcont.transport hc) (ih he (hc.withLabel _))
  | frame hn hf hb ih =>
    obtain ⟨D', hf', hc'⟩ := hf.extends he
    exact .frame hn hf' (ih he (hc'.withReturn _))
  | handler hcs hb ih => exact .handler (fun c h' => hc.catchOK (hcs c h')) (ih he hc)
  | returnInvoke hi hft hr hs =>
    exact .returnInvoke (he.funcs_get hi) hft (by simpa only [← hc.return_] using hr) hs
  | nil => exact .nil
  | snoc hs hm hi ihs ihi =>
    rename_i s' D he hc
    exact .snoc (ihs he hc) hm (ihi he (hc.after _))
  | sub hs hm ih =>
    rename_i s' D he hc
    exact .sub (ih he hc) hm

theorem ASeqT.transport {s s' : Store} {C D : Context} {es : List AInstr} {st : StackType}
    (hs : ASeqT s C es st) (he : s.Extends s') (hc : C.Entails D) : ASeqT s' D es st := by
  obtain ⟨a, b⟩ := st
  induction es using List.reverseRecOn generalizing b with
  | nil => exact ASeqT.nil_iff.mpr (ASeqT.nil_iff.mp hs)
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := ASeqT.snoc_iff.mp hs
    exact .sub (.snoc (ih _ hs) hm (hi.transport he (hc.after _))) hout

end FVA.Wasm.Valid
