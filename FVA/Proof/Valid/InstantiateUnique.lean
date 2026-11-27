import FVA.Proof.Valid.InstantiateAllocation

/-!
# Initializer values are unique (contract U29b T3(i))

`Instantiated` names the initializer values existentially: each global's initializer, run in the
allocation holding all of them, evaluates to its own value. For a valid module these values are
unique — the `k`-th global's initializer is one constant instruction reading imported globals and
the `k` defined before it (R1 = B), then tables + element segments read every global — so two
witnesses allocate the same store and instance. Launch canonicalization (`FVA.Proof.Wasi`) rests
on it.
-/

namespace FVA.Wasm.Valid.InitProof

open FVA.Wasm FVA.Wasm.Exec

/-- `m`'s initializers evaluate to `g`, `t`, `e` in the allocation holding them (`Instantiated`'s
initializer conditions). -/
def InitHolds (H : HostSem) (s : Store) (m : Module) (imports : List ExternVal) (g : List Val)
    (t : List Ref) (e : List (List Ref)) : Prop :=
  List.Forall₂ (fun gl v => Steps H
      ⟨(allocModule s m imports g t e).1, ⟨[], (allocModule s m imports g t e).2⟩,
        gl.init.map .plain⟩
      ⟨(allocModule s m imports g t e).1, ⟨[], (allocModule s m imports g t e).2⟩,
        [v.instr]⟩) m.globals g ∧
    List.Forall₂ (fun tb r => Steps H
      ⟨(allocModule s m imports g t e).1, ⟨[], (allocModule s m imports g t e).2⟩,
        tb.init.map .plain⟩
      ⟨(allocModule s m imports g t e).1, ⟨[], (allocModule s m imports g t e).2⟩,
        [(Val.ref r).instr]⟩) m.tables t ∧
    List.Forall₂ (fun el rs => List.Forall₂ (fun ex r => Steps H
      ⟨(allocModule s m imports g t e).1, ⟨[], (allocModule s m imports g t e).2⟩,
        ex.map .plain⟩
      ⟨(allocModule s m imports g t e).1, ⟨[], (allocModule s m imports g t e).2⟩,
        [(Val.ref r).instr]⟩) el.init rs) m.elems e

/-- The instance `allocModule` builds depends on the store, module and imports alone. -/
theorem alloc_inst_eq (s : Store) (m : Module) (imports : List ExternVal) (g g' : List Val)
    (t t' : List Ref) (e e' : List (List Ref)) :
    (allocModule s m imports g t e).2 = (allocModule s m imports g' t' e').2 := rfl

/-- Two relations over one list, each functional where both hold, relate it to one list. -/
theorem forall₂_eq {α β : Type} {R S : α → β → Prop} :
    ∀ {xs : List α} {ys ys' : List β}, List.Forall₂ R xs ys → List.Forall₂ S xs ys' →
      (∀ x ∈ xs, ∀ y y', R x y → S x y' → y = y') → ys = ys'
  | _, _, _, .nil, .nil, _ => rfl
  | _, _, _, .cons h hs, .cons h' hs', hu => by
    rw [hu _ (List.mem_cons_self ..) _ _ h h',
      forall₂_eq hs hs' fun x hx => hu x (List.mem_cons_of_mem _ hx)]

/-- One constant instruction, run under one instance in two stores that hold the same values at
the globals its context names, gives one value. -/
theorem const_value_eq {H H' : HostSem} {C : Context} {s s' : Store} {inst : ModuleInst}
    {i : Instr} {u : ValType} {v v' : Val} (hi : InstrT C i ⟨[], [.val u]⟩)
    (hc : ConstInstr C i)
    (hf : ∀ (x : Nat) (dt : DefType), C.funcs[x]? = some dt → ∃ a, inst.funcs[x]? = some a)
    (hg : ∀ (x : Nat) (gt : GlobalType), C.globals[x]? = some gt →
      ∃ (a : Nat) (gi gi' : GlobalInst), inst.globals[x]? = some a ∧
        s.globals[a]? = some gi ∧ s'.globals[a]? = some gi' ∧ gi.value = gi'.value)
    (h : Steps H ⟨s, ⟨[], inst⟩, [.plain i]⟩ ⟨s, ⟨[], inst⟩, [v.instr]⟩)
    (h' : Steps H' ⟨s', ⟨[], inst⟩, [.plain i]⟩ ⟨s', ⟨[], inst⟩, [v'.instr]⟩) : v = v' := by
  have hval : ∀ (w : Val), [AInstr.plain i] = [w.instr] → v = w ∧ v' = w := fun w hw => by
    rw [hw] at h h'
    exact ⟨(value_inj (List.singleton_inj.mp
        (congrArg Config.instrs (Ref.steps_values (vs := [w]) h)))),
      (value_inj (List.singleton_inj.mp
        (congrArg Config.instrs (Ref.steps_values (vs := [w]) h'))))⟩
  cases i <;> simp only [ConstInstr] at hc
  case iconst w n =>
    cases hi
    rename_i hn
    cases w with
    | w32 => obtain ⟨rfl, rfl⟩ := hval (.i32 ⟨n, hn⟩) rfl; rfl
    | w64 => obtain ⟨rfl, rfl⟩ := hval (.i64 ⟨n, hn⟩) rfl; rfl
  case fconst w n =>
    cases hi
    rename_i hn
    cases w with
    | w32 => obtain ⟨rfl, rfl⟩ := hval (.f32 ⟨n, hn⟩) rfl; rfl
    | w64 => obtain ⟨rfl, rfl⟩ := hval (.f64 ⟨n, hn⟩) rfl; rfl
  case refNull ht =>
    cases hi
    have hs : ∀ s, Ref.step ⟨s, ⟨[], inst⟩, [.plain (.refNull ht)]⟩ =
        some ⟨s, ⟨[], inst⟩, [(Val.ref .null).instr]⟩ := fun s => by
      simp [Ref.step, Ref.seq, Ref.toVal, Ref.atInstr, Ref.instrStep, Val.instr]
    have hu : ∀ s, Ref.uniqueStep false ⟨s, ⟨[], inst⟩, [.plain (.refNull ht)]⟩ = true :=
      fun s => by simp [Ref.uniqueStep, Ref.seqUnique, Ref.toVal, Ref.atUnique, Ref.instrUnique]
    rw [value_of_step (hs s) (hu s) h, value_of_step (hs s') (hu s') h']
  case refFunc x =>
    cases hi
    rename_i dt hfx _
    obtain ⟨a, ha⟩ := hf x dt hfx
    have hs : ∀ s, Ref.step ⟨s, ⟨[], inst⟩, [.plain (.refFunc x)]⟩ =
        some ⟨s, ⟨[], inst⟩, [(Val.ref (.func a)).instr]⟩ := fun s => by
      simp [Ref.step, Ref.seq, Ref.toVal, Ref.atInstr, Ref.instrStep, ha, Val.instr]
    have hu : ∀ s, Ref.uniqueStep false ⟨s, ⟨[], inst⟩, [.plain (.refFunc x)]⟩ = true :=
      fun s => by simp [Ref.uniqueStep, Ref.seqUnique, Ref.toVal, Ref.atUnique, Ref.instrUnique]
    rw [value_of_step (hs s) (hu s) h, value_of_step (hs s') (hu s') h']
  case globalGet x =>
    cases hi
    rename_i gt hgx
    obtain ⟨a, gi, gi', ha, hgi, hgi', heq⟩ := hg x gt hgx
    have hs : ∀ (s : Store) (gi : GlobalInst), s.globals[a]? = some gi →
        Ref.step ⟨s, ⟨[], inst⟩, [.plain (.globalGet x)]⟩ =
          some ⟨s, ⟨[], inst⟩, [gi.value.instr]⟩ := fun s gi hgi => by
      simp [Ref.step, Ref.seq, Ref.toVal, Ref.atInstr, Ref.instrStep, ha, hgi]
    have hu : ∀ s, Ref.uniqueStep false ⟨s, ⟨[], inst⟩, [.plain (.globalGet x)]⟩ = true :=
      fun s => by simp [Ref.uniqueStep, Ref.seqUnique, Ref.toVal, Ref.atUnique, Ref.instrUnique]
    rw [value_of_step (hs s gi hgi) (hu s) h, value_of_step (hs s' gi' hgi') (hu s') h', heq]

/-- The `k`-th global's initializer reads each global it names at one address in two allocations,
the same value there when their first `k` values agree. -/
theorem alloc_global_agree {s : Store} {m : Module} {imports : List ExternVal}
    (hm : ImportsMatch s m imports) {g g' : List Val} {t t' : List Ref}
    {e e' : List (List Ref)} (hl : m.globals.length = g.length)
    (hl' : m.globals.length = g'.length) {k : Nat} (hk : g.take k = g'.take k) {x : Nat}
    {gt : GlobalType} (hx : (globalContext m k).globals[x]? = some gt) :
    ∃ (a : Nat) (gi gi' : GlobalInst), (allocModule s m imports g t e).2.globals[x]? = some a ∧
      (allocModule s m imports g t e).1.globals[a]? = some gi ∧
      (allocModule s m imports g' t' e').1.globals[a]? = some gi' ∧ gi.value = gi'.value := by
  have himp := import_globals hm
  change (importGlobals m.defTypes m.imports ++
    (m.globals.take k).map (·.type.close m.defTypes))[x]? = some gt at hx
  rw [alloc_inst_globals]
  by_cases hlt : x < (importGlobals m.defTypes m.imports).length
  · rw [List.getElem?_append_left hlt] at hx
    obtain ⟨a, ha, gi, hgi, -⟩ := forall₂_lookup_right himp hx
    refine ⟨a, gi, gi, lookup_append ha, ?_, ?_, rfl⟩ <;>
    · rw [alloc_globals_eq]
      exact lookup_append hgi
  · have hle := Nat.le_of_not_lt hlt
    obtain ⟨j, rfl⟩ : ∃ j, x = (importGlobals m.defTypes m.imports).length + j :=
      ⟨_, (Nat.add_sub_cancel' hle).symm⟩
    rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_take] at hx
    split at hx
    · rename_i hjk
      obtain ⟨gl, hgj, -⟩ := Option.map_eq_some_iff.mp hx
      have hj : j < g.length := hl ▸ lookup_lt hgj
      have hj' : j < g'.length := hl' ▸ lookup_lt hgj
      have hz : (m.globals.zip g)[j]? = some (gl, g[j]) :=
        List.getElem?_zip_eq_some.mpr ⟨hgj, List.getElem?_eq_getElem hj⟩
      have hz' : (m.globals.zip g')[j]? = some (gl, g'[j]) :=
        List.getElem?_zip_eq_some.mpr ⟨hgj, List.getElem?_eq_getElem hj'⟩
      obtain ⟨a, ha, hga⟩ := forall₂_lookup_right
        (alloc_global_lookup (s := s) (imports := imports) g t e hl) hz
      obtain ⟨a', ha', hga'⟩ := forall₂_lookup_right
        (alloc_global_lookup (s := s) (imports := imports) g' t' e' hl') hz'
      obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
      have hv : g[j] = g'[j] := by
        have h₁ := congrArg (·[j]?) hk
        simp only [List.getElem?_take, hjk, ↓reduceIte, List.getElem?_eq_getElem hj,
          List.getElem?_eq_getElem hj', Option.some.injEq] at h₁
        exact h₁
      refine ⟨a, _, _, ?_, hga, hga', hv⟩
      rw [List.getElem?_append_right (by rw [himp.length_eq]; omega), himp.length_eq,
        Nat.add_sub_cancel_left]
      exact ha
    · cases hx

/-- Contract U29b T3(i): a valid module's initializer values are unique — two witnesses of
`Instantiated`'s initializer conditions hold the same values, so they allocate the same store and
instance. -/
theorem init_values_unique {H H' : HostSem} {s : Store} {m : Module}
    {imports : List ExternVal} (hv : ModuleValid m) (hm : ImportsMatch s m imports)
    {g g' : List Val} {t t' : List Ref} {e e' : List (List Ref)}
    (h : InitHolds H s m imports g t e) (h' : InitHolds H' s m imports g' t' e') :
    g = g' ∧ t = t' ∧ e = e' := by
  obtain ⟨hg, ht, he⟩ := h
  obtain ⟨hg', ht', he'⟩ := h'
  have hl := hg.length_eq
  have hl' := hg'.length_eq
  have hfun : ∀ (g : List Val) (t : List Ref) (e : List (List Ref)) (x : Nat) (dt : DefType),
      (moduleContext m).funcs[x]? = some dt →
      ∃ a, (allocModule s m imports g t e).2.funcs[x]? = some a := fun g t e x dt hx => by
    obtain ⟨a, ha, -⟩ := forall₂_lookup_right (alloc_funcs hv hm g t e) hx
    exact ⟨a, ha⟩
  have hpre : ∀ k, g.take k = g'.take k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      by_cases hk : k < m.globals.length
      · obtain ⟨gl, hgk⟩ : ∃ gl, m.globals[k]? = some gl := ⟨_, List.getElem?_eq_getElem hk⟩
        obtain ⟨v, hvk, hst⟩ := forall₂_lookup_left hg hgk
        obtain ⟨v', hvk', hst'⟩ := forall₂_lookup_left hg' hgk
        obtain ⟨-, hexpr, hconst⟩ := hv.globals k gl hgk
        obtain ⟨i, u, hinit, hci, hi, -⟩ := const_singleton hexpr hconst
        rw [hinit] at hst hst'
        have hvv : v = v' := const_value_eq hi hci (hfun g t e) (fun x gt hx =>
          alloc_global_agree (t' := t') (e' := e') hm hl hl' ih hx) hst
          (by rw [alloc_inst_eq s m imports g' g t' t e' e] at hst'; exact hst')
        rw [List.take_add_one, List.take_add_one, ih, hvk, hvk', hvv]
      · rw [List.take_of_length_le (l := g) (by omega),
          List.take_of_length_le (l := g') (by omega)]
        rwa [List.take_of_length_le (l := g) (by omega),
          List.take_of_length_le (l := g') (by omega)] at ih
  have hgg : g = g' := by
    have h₁ := hpre m.globals.length
    rwa [hl, List.take_length, ← hl, hl', List.take_length] at h₁
  subst hgg
  have hall : ∀ x gt, (moduleContext m).globals[x]? = some gt →
      ∃ (a : Nat) (gi gi' : GlobalInst), (allocModule s m imports g t e).2.globals[x]? = some a ∧
        (allocModule s m imports g t e).1.globals[a]? = some gi ∧
        (allocModule s m imports g t' e').1.globals[a]? = some gi' ∧
        gi.value = gi'.value := fun x gt hx => by
    apply alloc_global_agree hm hl hl' (k := m.globals.length) rfl
    show (importGlobals m.defTypes m.imports ++
      (m.globals.take m.globals.length).map (·.type.close m.defTypes))[x]? = some gt
    rw [List.take_length]
    exact hx
  have hzero : ∀ x gt, (globalContext m 0).globals[x]? = some gt →
      ∃ (a : Nat) (gi gi' : GlobalInst), (allocModule s m imports g t e).2.globals[x]? = some a ∧
        (allocModule s m imports g t e).1.globals[a]? = some gi ∧
        (allocModule s m imports g t' e').1.globals[a]? = some gi' ∧
        gi.value = gi'.value := fun x gt hx =>
    alloc_global_agree hm hl hl' (k := 0) rfl hx
  have hinst := alloc_inst_eq s m imports g g t' t e' e
  refine ⟨rfl, ?_, ?_⟩
  · refine forall₂_eq ht ht' fun tb htb r r' hr hr' => ?_
    obtain ⟨-, -, hte, htc⟩ := hv.tables tb htb
    obtain ⟨i, u, hinit, hci, hi, -⟩ := const_singleton hte htc
    rw [hinit] at hr hr'
    rw [hinst] at hr'
    exact Val.ref.inj (const_value_eq hi hci (hfun g t e) hzero hr hr')
  · refine forall₂_eq he he' fun el hel rs rs' hrs hrs' => ?_
    refine forall₂_eq hrs hrs' fun ex hex r r' hr hr' => ?_
    have hc := (hv.elems el hel).2.1 ex hex
    obtain ⟨i, u, hinit, hci, hi, -⟩ := const_singleton hc.1 hc.2
    rw [hinit] at hr hr'
    rw [hinst] at hr'
    exact Val.ref.inj (const_value_eq hi hci (hfun g t e) hall hr hr')

end FVA.Wasm.Valid.InitProof
