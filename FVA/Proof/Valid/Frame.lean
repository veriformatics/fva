import FVA.Proof.Valid.Store

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- Frame typing inside a control fragment: labels and the return type belong to its context. -/
def FrameCtx (s : Store) (f : Frame) (C : Context) : Prop :=
  ∃ C₀ ls ret, FrameT s f C₀ ∧ C = { C₀ with labels := ls, return_ := ret }

theorem FrameT.ctx {s : Store} {f : Frame} {C : Context} (h : FrameT s f C) :
    FrameCtx s f C := ⟨C, C.labels, C.return_, h, by cases C; rfl⟩

theorem FrameT.noLabels {s : Store} {f : Frame} {C : Context} (h : FrameT s f C) :
    C.labels = [] := by
  obtain ⟨C₀, ts, hi, _, rfl⟩ := h
  exact hi.noLabels

theorem FrameT.noReturn {s : Store} {f : Frame} {C : Context} (h : FrameT s f C) :
    C.return_ = none := by
  obtain ⟨C₀, ts, hi, _, rfl⟩ := h
  exact hi.noReturn

theorem FrameT.noSets {s : Store} {f : Frame} {C : Context} (h : FrameT s f C) :
    C.sets = [] := by
  obtain ⟨C₀, ts, hi, _, rfl⟩ := h
  exact hi.noSets

namespace FrameCtx

theorem withLabel {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    (ts : List ValType) : FrameCtx s f (C.withLabel ts) := by
  obtain ⟨C₀, ls, ret, hf, rfl⟩ := h
  exact ⟨C₀, ts :: ls, ret, hf, rfl⟩

theorem withReturn {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    (ret : Option (List ValType)) : FrameCtx s f { C with return_ := ret } := by
  obtain ⟨C₀, ls, old, hf, rfl⟩ := h
  exact ⟨C₀, ls, ret, hf, rfl⟩

theorem extendStore {s s' : Store} {f : Frame} {C : Context} (hf : FrameCtx s f C)
    (h : s.Extends s') : ∃ D, FrameCtx s' f D ∧ C.Entails D := by
  obtain ⟨C₀, ls, ret, hf, rfl⟩ := hf
  obtain ⟨D₀, hf', he⟩ := hf.extends h
  exact ⟨{ D₀ with labels := ls, return_ := ret }, ⟨D₀, ls, ret, hf', rfl⟩,
    he.withControl ls ret⟩

theorem noSets {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C) : C.sets = [] := by
  obtain ⟨C₀, ls, ret, hf, rfl⟩ := h
  exact hf.noSets

theorem noDead {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C) : C.dead = false := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  exact hi.noDead

theorem types {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C) :
    C.types = f.inst.types := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  exact hi.types

/-- The runtime's block type has the context's arities (the runtime leaves a value type
unclosed: only lengths reach execution). -/
theorem blockType {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {bt : BlockType} {ft : FuncType} (hb : C.blockType bt = some ft) :
    ∃ ft', bt.expand f = some ft' ∧ ft'.params.length = ft.params.length ∧
      ft'.results.length = ft.results.length := by
  cases bt with
  | empty => cases hb; exact ⟨_, rfl, rfl, rfl⟩
  | val t =>
    simp only [Context.blockType] at hb
    split at hb
    · cases hb; exact ⟨_, rfl, rfl, rfl⟩
    · cases hb
  | idx x =>
    simp only [Context.blockType, Context.typeAt, h.types] at hb
    exact ⟨ft, hb, rfl, rfl⟩

theorem funcs {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {dt : DefType} (hx : C.funcs[x]? = some dt) :
    ∃ a fi, f.inst.funcs[x]? = some a ∧ s.funcs[a]? = some fi ∧ fi.type = dt := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, fi, hfi, hft⟩ := forall₂_lookup_right hi.funcs hx
  exact ⟨a, fi, ha, hfi, hft⟩

theorem funcType {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {ft : FuncType} (hx : C.funcType x = some ft) :
    ∃ a fi, f.inst.funcs[x]? = some a ∧ s.funcs[a]? = some fi ∧ fi.type.expand = some ft := by
  simp only [Context.funcType, Option.bind_eq_some_iff] at hx
  obtain ⟨dt, hdt, he⟩ := hx
  obtain ⟨a, fi, ha, hfi, rfl⟩ := h.funcs hdt
  exact ⟨a, fi, ha, hfi, he⟩

theorem tags {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {dt : DefType} (hx : C.tags[x]? = some dt) :
    ∃ a ti, f.inst.tags[x]? = some a ∧ s.tags[a]? = some ti ∧ ti.type = dt := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, ti, hti, htt⟩ := forall₂_lookup_right hi.tags hx
  exact ⟨a, ti, ha, hti, htt⟩

theorem tables {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {tt : TableType} (hx : C.tables[x]? = some tt) :
    ∃ a ti, f.inst.tables[x]? = some a ∧ s.tables[a]? = some ti ∧ ti.type = tt := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, ti, hti, htt⟩ := forall₂_lookup_right hi.tables hx
  exact ⟨a, ti, ha, hti, htt⟩

theorem mems {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {lim : Limits} (hx : C.mems[x]? = some lim) :
    ∃ a mi, f.inst.mems[x]? = some a ∧ s.mems[a]? = some mi ∧
      (⟨mi.pages, mi.max⟩ : Limits) = lim := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, mi, hmi, hml⟩ := forall₂_lookup_right hi.mems hx
  exact ⟨a, mi, ha, hmi, hml⟩

theorem globals {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {gt : GlobalType} (hx : C.globals[x]? = some gt) :
    ∃ a gi, f.inst.globals[x]? = some a ∧ s.globals[a]? = some gi ∧ gi.type.Sub gt := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, gi, hgi, hgt⟩ := forall₂_lookup_right hi.globals hx
  exact ⟨a, gi, ha, hgi, hgt⟩

theorem elems {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {rt : RefType} (hx : C.elems[x]? = some rt) :
    ∃ a ei, f.inst.elems[x]? = some a ∧ s.elems[a]? = some ei ∧ ei.type = rt := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, ei, hei, hrt⟩ := forall₂_lookup_right hi.elems hx
  exact ⟨a, ei, ha, hei, hrt⟩

theorem datas {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} (hx : x < C.datas) :
    ∃ a di, f.inst.datas[x]? = some a ∧ s.datas[a]? = some di := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  have hlen : x < f.inst.datas.length := by simpa only [← hi.datas.1] using hx
  have ha := List.getElem?_eq_getElem hlen
  have hbound := hi.datas.2 _ (List.mem_of_getElem? ha)
  exact ⟨_, _, ha, List.getElem?_eq_getElem hbound⟩

end FrameCtx

theorem localAt_singletons (lts : List LocalType) (x : Nat) :
    localAt (lts.map (1, ·)) x = lts[x]? := by
  induction lts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    cases x with
    | zero => rfl
    | succ x => simpa only [List.map_cons, localAt, Nat.not_lt_zero, Nat.add_lt_add_iff_right,
        Nat.lt_one_iff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        List.getElem?_cons_succ] using ih x

theorem FrameCtx.local {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {lt : LocalType} (hx : localAt C.locals x = some lt) :
    ∃ ov, f.locals[x]? = some ov ∧ LocalOK s ov lt := by
  obtain ⟨C₀, ls, ret, ⟨C₁, lts, hi, hvs, rfl⟩, rfl⟩ := h
  exact forall₂_lookup_right hvs ((localAt_singletons lts x).symm.trans hx)

/-- A readable local holds a value of its type (a frame context initializes by flags alone). -/
theorem FrameCtx.locals {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {lt : LocalType} (hx : localAt C.locals x = some lt)
    (hr : lt.set = true ∨ x ∈ C.sets ∨ C.dead = true) :
    ∃ v, f.locals[x]? = some (some v) ∧ v.HasType s lt.type := by
  obtain ⟨ov, hov, hl⟩ := h.local hx
  rw [h.noSets, h.noDead] at hr
  simp only [List.not_mem_nil, Bool.false_eq_true, or_false] at hr
  cases ov with
  | some v => exact ⟨v, hov, hl.2.2⟩
  | none => rw [hl.1] at hr; cases hr

end FVA.Wasm.Valid
