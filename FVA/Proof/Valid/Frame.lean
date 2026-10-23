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

theorem blockType {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    (bt : BlockType) : C.blockType bt = bt.expand f := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  cases bt <;> simp only [Context.blockType, BlockType.expand, hi.types]

theorem funcs {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {ft : FuncType} (hx : C.funcs[x]? = some ft) :
    ∃ a fi, f.inst.funcs[x]? = some a ∧ s.funcs[a]? = some fi ∧ fi.type = ft := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, _, rfl⟩, rfl⟩ := h
  obtain ⟨a, ha, fi, hfi, hft⟩ := forall₂_lookup_right hi.funcs hx
  exact ⟨a, fi, ha, hfi, hft⟩

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
    ∃ a gi, f.inst.globals[x]? = some a ∧ s.globals[a]? = some gi ∧ gi.type = gt := by
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

theorem localAt_singletons (ts : List ValType) (x : Nat) :
    localAt (ts.map (1, ·)) x = ts[x]? := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    cases x with
    | zero => rfl
    | succ x => simpa only [List.map_cons, localAt, Nat.not_lt_zero, Nat.add_lt_add_iff_right,
        Nat.lt_one_iff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        List.getElem?_cons_succ] using ih x

theorem FrameCtx.locals {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {t : ValType} (hx : localAt C.locals x = some t) :
    ∃ v, f.locals[x]? = some v ∧ v.HasType s t := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, hvs, rfl⟩, rfl⟩ := h
  exact forall₂_lookup_right hvs ((localAt_singletons ts x).symm.trans hx)

end FVA.Wasm.Valid
