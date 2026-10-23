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

private theorem reassemble {s s' : Store} (he : s.Extends s')
    (hf : ∀ fi ∈ s'.funcs, FuncInstOK s fi)
    (ht : ∀ ti ∈ s'.tables, ti.type.Ok ∧ ti.elem.length = ti.type.limits.min ∧
      ∀ r ∈ ti.elem, Val.HasType s (.ref r) (.ref ti.type.elem))
    (hm : ∀ mi ∈ s'.mems, memTypeOk ⟨mi.pages, mi.max⟩)
    (hg : ∀ gi ∈ s'.globals, Val.HasType s gi.value gi.type.val)
    (hel : ∀ ei ∈ s'.elems, ∀ r ∈ ei.elem, Val.HasType s (.ref r) (.ref ei.type)) :
    StoreOK s' := by
  refine ⟨fun fi hfi => (hf fi hfi).extends he, ?_, hm,
    fun gi hgi => he.value (hg gi hgi), fun ei hei r hr => he.value (hel ei hei r hr)⟩
  intro ti hti
  obtain ⟨hok, hlen, href⟩ := ht ti hti
  exact ⟨hok, hlen, fun r hr => he.value (href r hr)⟩

theorem StoreOK.setMem {s : Store} (h : StoreOK s) {a : Nat} {m m' : MemInst}
    (ha : s.mems[a]? = some m) (he : m.Extends m') (hm : memTypeOk ⟨m'.pages, m'.max⟩) :
    s.Extends (s.setMem a m') ∧ StoreOK (s.setMem a m') := by
  have hr := Store.Extends.refl s
  have hs : s.Extends (s.setMem a m') :=
    ⟨hr.1, hr.2.1, listExtends_set mem_extends_refl ha he,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs h.funcs h.tables (forall_set h.mems hm) h.globals h.elems⟩

theorem StoreOK.setTable {s : Store} (h : StoreOK s) {a : Nat} {t t' : TableInst}
    (ha : s.tables[a]? = some t) (he : t.Extends t')
    (ht : t'.type.Ok ∧ t'.elem.length = t'.type.limits.min ∧
      ∀ r ∈ t'.elem, Val.HasType s (.ref r) (.ref t'.type.elem)) :
    s.Extends (s.setTable a t') ∧ StoreOK (s.setTable a t') := by
  have hr := Store.Extends.refl s
  have hs : s.Extends (s.setTable a t') :=
    ⟨hr.1, listExtends_set table_extends_refl ha he, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs h.funcs (forall_set h.tables ht) h.mems h.globals h.elems⟩

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
  exact ⟨hs, reassemble hs h.funcs h.tables h.mems (forall_set h.globals hv) h.elems⟩

theorem StoreOK.dropElem {s : Store} (h : StoreOK s) {a : Nat} {e : ElemInst}
    (ha : s.elems[a]? = some e) :
    s.Extends { s with elems := s.elems.set a { e with elem := [] } } ∧
      StoreOK { s with elems := s.elems.set a { e with elem := [] } } := by
  have hr := Store.Extends.refl s
  have hs : s.Extends { s with elems := s.elems.set a { e with elem := [] } } :=
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      listExtends_set elem_extends_refl ha ⟨rfl, Or.inr rfl⟩, hr.2.2.2.2.2⟩
  exact ⟨hs, reassemble hs h.funcs h.tables h.mems h.globals
    (forall_set h.elems (by simp))⟩

theorem StoreOK.dropData {s : Store} (h : StoreOK s) {a : Nat} {d : DataInst}
    (ha : s.datas[a]? = some d) :
    s.Extends { s with datas := s.datas.set a { data := [] } } ∧
      StoreOK { s with datas := s.datas.set a { data := [] } } := by
  have hr := Store.Extends.refl s
  have hs : s.Extends { s with datas := s.datas.set a { data := [] } } :=
    ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      listExtends_set data_extends_refl ha (Or.inr rfl)⟩
  exact ⟨hs, reassemble hs h.funcs h.tables h.mems h.globals h.elems⟩

theorem StoreOK.writeMem {s : Store} (h : StoreOK s) {a : Nat} {m : MemInst}
    (ha : s.mems[a]? = some m) (ea k v : Nat) :
    s.Extends (s.setMem a (m.write ea k v)) ∧ StoreOK (s.setMem a (m.write ea k v)) :=
  h.setMem ha ⟨rfl, Nat.le_refl _⟩ (h.mems m (List.mem_of_getElem? ha))

theorem StoreOK.writeTable {s : Store} (h : StoreOK s) {a : Nat} {t : TableInst}
    (ha : s.tables[a]? = some t) (i : Nat) {r : Ref}
    (hv : Val.HasType s (.ref r) (.ref t.type.elem)) :
    s.Extends (s.setTable a { t with elem := t.elem.set i r }) ∧
      StoreOK (s.setTable a { t with elem := t.elem.set i r }) := by
  obtain ⟨hok, hlen, href⟩ := h.tables _ (List.mem_of_getElem? ha)
  apply h.setTable ha
  · exact ⟨rfl, rfl, by simp⟩
  · exact ⟨hok, by simpa only [List.length_set] using hlen, forall_set href hv⟩

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
  obtain ⟨⟨hmin, hmax⟩, hlen, href⟩ := h.tables _ (List.mem_of_getElem? ha)
  dsimp only [TableInst.grow] at hg
  split at hg
  · cases hg
  · rename_i hlim
    cases hg
    apply h.setTable ha
    · exact ⟨rfl, rfl, by simp⟩
    · refine ⟨⟨?_, ?_⟩, by simp, ?_⟩
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

theorem FrameCtx.setLocal {s : Store} {f : Frame} {C : Context} (h : FrameCtx s f C)
    {x : Nat} {t : ValType} {v : Val} (hx : localAt C.locals x = some t)
    (hv : v.HasType s t) : FrameCtx s { f with locals := f.locals.set x v } C := by
  obtain ⟨C₀, ls, ret, ⟨C₁, ts, hi, hvs, rfl⟩, rfl⟩ := h
  refine ⟨_, ls, ret, ⟨C₁, ts, hi, ?_, rfl⟩, rfl⟩
  exact forall₂_set_left hvs ((localAt_singletons ts x).symm.trans hx) hv

end FVA.Wasm.Valid
