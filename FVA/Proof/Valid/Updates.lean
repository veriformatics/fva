import FVA.Proof.Valid.Frame

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem listExtends_set {α : Type} {R : α → α → Prop} (hr : ∀ x, R x x)
    {xs : List α} {a : Nat} {x y : α} (hx : xs[a]? = some x) (hxy : R x y) :
    ListExtends R xs (xs.set a y) := by
  intro i z hz
  by_cases hi : a = i
  · subst i
    have hzx : z = x := Option.some.inj (hz.symm.trans hx)
    subst z
    exact ⟨y, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hx).1, hxy⟩
  · exact ⟨z, (List.getElem?_set_ne hi).trans hz, hr z⟩

theorem forall_set {α : Type} {P : α → Prop} {xs : List α} {a : Nat} {v : α}
    (h : ∀ x ∈ xs, P x) (hv : P v) : ∀ x ∈ xs.set a v, P x := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx
  · exact hv

private theorem table_extends_refl (t : TableInst) : t.Extends t := ⟨rfl, rfl, Nat.le_refl _⟩
private theorem mem_extends_refl (m : MemInst) : m.Extends m := ⟨rfl, Nat.le_refl _⟩
private theorem global_extends_refl (g : GlobalInst) : g.Extends g := ⟨rfl, Or.inr rfl⟩
private theorem elem_extends_refl (e : ElemInst) : e.Extends e := ⟨rfl, Or.inl rfl⟩
private theorem data_extends_refl (d : DataInst) : d.Extends d := Or.inl rfl

private theorem reassemble {s s' : Store} (he : s.Extends s') (htags : s'.tags = s.tags)
    (hexns : s'.exns = s.exns) (h : StoreOK s)
    (hf : ∀ fi ∈ s'.funcs, FuncInstOK s fi)
    (ht : ∀ ti ∈ s'.tables, ti.type.Ok ∧ (ValType.ref ti.type.elem).Closed 0 ∧
      ti.elem.length = ti.type.limits.min ∧
      ∀ r ∈ ti.elem, Val.HasType s (.ref r) (.ref ti.type.elem))
    (hm : ∀ mi ∈ s'.mems, memTypeOk ⟨mi.pages, mi.max⟩)
    (hg : ∀ gi ∈ s'.globals, gi.type.val.Closed 0 ∧ Val.HasType s gi.value gi.type.val)
    (hel : ∀ ei ∈ s'.elems, (ValType.ref ei.type).Closed 0 ∧
      ∀ r ∈ ei.elem, Val.HasType s (.ref r) (.ref ei.type)) :
    StoreOK s' := by
  refine ⟨by rw [htags]; exact h.tags, fun fi hfi => (hf fi hfi).extends he, ?_, hm,
    fun gi hgi => ⟨(hg gi hgi).1, he.value (hg gi hgi).2⟩,
    fun ei hei => ⟨(hel ei hei).1, fun r hr => he.value ((hel ei hei).2 r hr)⟩, ?_⟩
  · intro ti hti
    obtain ⟨hok, hcl, hlen, href⟩ := ht ti hti
    exact ⟨hok, hcl, hlen, fun r hr => he.value (href r hr)⟩
  · intro e hx
    rw [hexns] at hx
    obtain ⟨ti, ts, hti, hts, hfs⟩ := h.exns e hx
    exact ⟨ti, ts, by rw [htags]; exact hti, hts, he.values hfs⟩

theorem StoreOK.setMem {s : Store} (h : StoreOK s) {a : Nat} {m m' : MemInst}
    (ha : s.mems[a]? = some m) (he : m.Extends m') (hm : memTypeOk ⟨m'.pages, m'.max⟩) :
    s.Extends (s.setMem a m') ∧ StoreOK (s.setMem a m') := by
  have hr := Store.Extends.refl s
  have hs : s.Extends (s.setMem a m') :=
    ⟨hr.1, hr.2.1, listExtends_set mem_extends_refl ha he,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs rfl rfl h h.funcs h.tables (forall_set h.mems hm) h.globals h.elems⟩

theorem StoreOK.setTable {s : Store} (h : StoreOK s) {a : Nat} {t t' : TableInst}
    (ha : s.tables[a]? = some t) (he : t.Extends t')
    (ht : t'.type.Ok ∧ (ValType.ref t'.type.elem).Closed 0 ∧ t'.elem.length = t'.type.limits.min ∧
      ∀ r ∈ t'.elem, Val.HasType s (.ref r) (.ref t'.type.elem)) :
    s.Extends (s.setTable a t') ∧ StoreOK (s.setTable a t') := by
  have hr := Store.Extends.refl s
  have hs : s.Extends (s.setTable a t') :=
    ⟨hr.1, listExtends_set table_extends_refl ha he, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs rfl rfl h h.funcs (forall_set h.tables ht) h.mems h.globals h.elems⟩

theorem StoreOK.setGlobal {s : Store} (h : StoreOK s) {a : Nat} {g : GlobalInst} {v : Val}
    (ha : s.globals[a]? = some g) (hmut : g.type.mutability = .var)
    (hv : v.HasType s g.type.val) :
    s.Extends { s with globals := s.globals.set a { g with value := v } } ∧
      StoreOK { s with globals := s.globals.set a { g with value := v } } := by
  have hr := Store.Extends.refl s
  have hs : s.Extends { s with globals := s.globals.set a { g with value := v } } :=
    ⟨hr.1, hr.2.1, hr.2.2.1,
      listExtends_set global_extends_refl ha ⟨rfl, Or.inl hmut⟩,
      hr.2.2.2.2.1, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs rfl rfl h h.funcs h.tables h.mems
    (forall_set h.globals ⟨(h.globals g (List.mem_of_getElem? ha)).1, hv⟩) h.elems⟩

theorem StoreOK.dropElem {s : Store} (h : StoreOK s) {a : Nat} {e : ElemInst}
    (ha : s.elems[a]? = some e) :
    s.Extends { s with elems := s.elems.set a { e with elem := [] } } ∧
      StoreOK { s with elems := s.elems.set a { e with elem := [] } } := by
  have hr := Store.Extends.refl s
  have hs : s.Extends { s with elems := s.elems.set a { e with elem := [] } } :=
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      listExtends_set elem_extends_refl ha ⟨rfl, Or.inr rfl⟩, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs rfl rfl h h.funcs h.tables h.mems h.globals
    (forall_set h.elems ⟨(h.elems e (List.mem_of_getElem? ha)).1, by simp⟩)⟩

theorem StoreOK.dropData {s : Store} (h : StoreOK s) {a : Nat} {d : DataInst}
    (ha : s.datas[a]? = some d) :
    s.Extends { s with datas := s.datas.set a { data := [] } } ∧
      StoreOK { s with datas := s.datas.set a { data := [] } } := by
  have hr := Store.Extends.refl s
  have hs : s.Extends { s with datas := s.datas.set a { data := [] } } :=
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      listExtends_set data_extends_refl ha (Or.inr rfl), hr.2.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs rfl rfl h h.funcs h.tables h.mems h.globals h.elems⟩

theorem StoreOK.writeMem {s : Store} (h : StoreOK s) {a : Nat} {m : MemInst}
    (ha : s.mems[a]? = some m) (ea k v : Nat) :
    s.Extends (s.setMem a (m.write ea k v)) ∧ StoreOK (s.setMem a (m.write ea k v)) :=
  h.setMem ha ⟨rfl, Nat.le_refl _⟩ (h.mems m (List.mem_of_getElem? ha))

theorem StoreOK.writeTable {s : Store} (h : StoreOK s) {a : Nat} {t : TableInst}
    (ha : s.tables[a]? = some t) (i : Nat) {r : Ref}
    (hv : Val.HasType s (.ref r) (.ref t.type.elem)) :
    s.Extends (s.setTable a { t with elem := t.elem.set i r }) ∧
      StoreOK (s.setTable a { t with elem := t.elem.set i r }) := by
  obtain ⟨hok, hcl, hlen, href⟩ := h.tables _ (List.mem_of_getElem? ha)
  apply h.setTable ha
  · exact ⟨rfl, rfl, by simp⟩
  · exact ⟨hok, hcl, by simpa only [List.length_set] using hlen, forall_set href hv⟩

theorem StoreOK.growMem {s : Store} (h : StoreOK s) {a : Nat} {m m' : MemInst} {n : Nat}
    (ha : s.mems[a]? = some m) (hg : m.grow n = some m') :
    s.Extends (s.setMem a m') ∧ StoreOK (s.setMem a m') := by
  obtain ⟨hmin, hmax⟩ := h.mems _ (List.mem_of_getElem? ha)
  dsimp only [MemInst.grow] at hg
  split at hg
  · cases hg
  · rename_i hlim
    cases hg
    apply h.setMem ha
    · exact ⟨rfl, Nat.le_add_right _ _⟩
    · constructor
      · exact Nat.le_of_not_gt (fun hgt => hlim (Or.inl hgt))
      · intro mx hmx
        change m.max = some mx at hmx
        refine ⟨?_, (hmax mx hmx).2⟩
        by_contra hgt
        apply hlim
        right
        simp only [hmx, Option.any_some, decide_eq_true_eq]
        exact Nat.lt_of_not_ge hgt

theorem StoreOK.growTable {s : Store} (h : StoreOK s) {a : Nat} {t t' : TableInst}
    {n : Nat} {r : Ref} (ha : s.tables[a]? = some t) (hg : t.grow n r = some t')
    (hv : Val.HasType s (.ref r) (.ref t.type.elem)) :
    s.Extends (s.setTable a t') ∧ StoreOK (s.setTable a t') := by
  obtain ⟨⟨hmin, hmax⟩, hcl, hlen, href⟩ := h.tables _ (List.mem_of_getElem? ha)
  dsimp only [TableInst.grow] at hg
  split at hg
  · cases hg
  · rename_i hlim
    cases hg
    apply h.setTable ha
    · exact ⟨rfl, rfl, by simp⟩
    · refine ⟨⟨?_, ?_⟩, hcl, by simp, ?_⟩
      · have hlt : t.elem.length + n < 2 ^ 32 :=
          Nat.lt_of_not_ge (fun hge => hlim (Or.inl hge))
        change t.elem.length + n ≤ 2 ^ 32 - 1
        omega
      · intro mx hmx
        change t.type.limits.max = some mx at hmx
        refine ⟨?_, (hmax mx hmx).2⟩
        by_contra hgt
        apply hlim
        right
        simp only [hmx, Option.any_some, decide_eq_true_eq]
        exact Nat.lt_of_not_ge hgt
      · intro v hv'
        rcases List.mem_append.mp hv' with h_old | h_new
        · exact href v h_old
        · have hvr := List.mem_replicate.mp h_new
          simpa only [hvr.2] using hv

/-- `throw` allocates an exception of an existing tag, its fields typed by the tag's
parameters. -/
theorem StoreOK.addExn {s : Store} (h : StoreOK s) {ta : Nat} {ti : TagInst} {ts : List ValType}
    {vs : List Val} (hti : s.tags[ta]? = some ti) (hts : ti.type.expand = some ⟨ts, []⟩)
    (hvs : List.Forall₂ (Val.HasType s) vs ts) :
    s.Extends { s with exns := s.exns ++ [⟨ta, vs⟩] } ∧
      StoreOK { s with exns := s.exns ++ [⟨ta, vs⟩] } := by
  have hr := Store.Extends.refl s
  have hs : s.Extends { s with exns := s.exns ++ [⟨ta, vs⟩] } :=
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      fun i x hx => ⟨x, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1 ▸ hx,
        rfl⟩⟩
  refine ⟨hs, h.tags, fun fi hfi => (h.funcs fi hfi).extends hs, ?_, h.mems,
    fun gi hgi => ⟨(h.globals gi hgi).1, hs.value (h.globals gi hgi).2⟩,
    fun ei hei => ⟨(h.elems ei hei).1, fun r hr => hs.value ((h.elems ei hei).2 r hr)⟩, ?_⟩
  · intro ti' hti'
    obtain ⟨hok, hcl, hlen, href⟩ := h.tables ti' hti'
    exact ⟨hok, hcl, hlen, fun r hr => hs.value (href r hr)⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨ti', ts', hti', hts', hfs⟩ := h.exns e he
      exact ⟨ti', ts', hti', hts', hs.values hfs⟩
    · rw [List.mem_singleton.mp he]
      exact ⟨ti, ts, hti, hts, hs.values hvs⟩

theorem forall₂_set_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {i : Nat} {x : α} {y : β} (hy : ys[i]? = some y)
    (hx : R x y) : List.Forall₂ R (xs.set i x) ys := by
  induction h generalizing i with
  | nil => simp at hy
  | @cons a b xs ys hab hs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst y
      exact .cons hx hs
    | succ i => exact .cons hab (ih hy)

theorem forall₂_set {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (i : Nat) {x : α} {y : β} (hr : R x y) :
    List.Forall₂ R (xs.set i x) (ys.set i y) := by
  induction h generalizing i with
  | nil => exact .nil
  | cons hab hs ih =>
    cases i with
    | zero => exact .cons hr hs
    | succ i => exact .cons hab (ih i)

/-- `local.set x`: the frame holds `v` at `x`, the local now set; the context after the write
reads every local the context with `x` initialized did. -/
theorem FrameCtx.setLocal {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {lt : LocalType} {v : Val} (hx : localAt C.locals x = some lt)
    (hv : v.HasType s lt.type) :
    ∃ C', FrameCtx s { f with locals := f.locals.set x (some v) } C' ∧
      (C.addSets [x]).Entails C' := by
  obtain ⟨C₀, ls, ret, ⟨C₁, lts, hi, hvs, rfl⟩, rfl⟩ := h
  have hx' : lts[x]? = some lt := (localAt_singletons lts x).symm.trans hx
  obtain ⟨ov, hov, hl⟩ := forall₂_lookup_right hvs hx'
  have hcl : lt.type.Closed 0 := by cases ov <;> simp_all [LocalOK]
  let lts' := lts.set x ⟨true, lt.type⟩
  refine ⟨{ C₁ with locals := lts'.map (1, ·), labels := ls, return_ := ret },
    ⟨_, ls, ret, ⟨C₁, lts', hi, forall₂_set hvs x ⟨rfl, hcl, hv⟩, rfl⟩, rfl⟩, ?_⟩
  refine ⟨rfl, rfl, rfl, fun _ tt h => ⟨tt, h, rfl⟩, fun _ lim h => ⟨lim, h⟩, rfl, rfl,
    Nat.le_refl _, ?_, rfl, rfl, fun _ h => h, fun hd => hd⟩
  intro y lty hy
  simp only [Context.addSets, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.mem_cons, hi.noSets, hi.noDead, List.not_mem_nil, or_false,
    Bool.false_eq_true] at hy ⊢
  rw [localAt_singletons] at hy ⊢
  by_cases hxy : y = x
  · subst hxy
    rw [hx'] at hy
    cases hy
    exact ⟨⟨true, lt.type⟩,
      by simp [lts', List.getElem?_set_self (List.getElem?_eq_some_iff.mp hx').1],
      rfl, fun _ => rfl⟩
  · refine ⟨lty, by simp [lts', List.getElem?_set_ne (Ne.symm hxy), hy], rfl, ?_⟩
    rintro (h' | h')
    · exact h'
    · exact absurd h' hxy

end FVA.Wasm.Valid
