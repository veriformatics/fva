import FVA.Proof.Exec.Oblivious

/-!
# Data-oblivious framing: one step (contract U28g F1 `step_put`)

Each admitted step kind, from any state `P` alike the patched one (`Eqv P (put ts m)`): `P`
steps, alike the patched successor (`put (move F ts) m'`, `F` the step's position map).
-/

-- `fva trust` pins every FVA base module's compiled bytes (D49, `trust/oleans.tsv`); this
-- module's parallel elaboration wrote different `.olean` bytes per build (3 builds, 3 digests),
-- sequential elaboration the same bytes each time
set_option Elab.async false

namespace FVA.Wasm.Exec.Machine.Oblivious

open FVA.Wasm FVA.Wasm.Exec

/-- A value moves from the code to the operand stack. -/
theorem step_put_val {m m' P : MState} {ts : List (Pos × TVal)} {e : AInstr}
    {rest : List AInstr} {v : Val} (hP : Eqv P (put ts m)) (hc : m.code = e :: rest)
    (hv : Ref.toVal e = some v) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put ts m') := by
  simp only [MState.step, hc, hv, Option.some.injEq] at h
  subst h
  rw [put_eq, eqv_iff] at hP
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP
  refine ⟨{ P with stack := v :: P.stack, code := rest }, ?_, ?_⟩
  · simp only [MState.step, hPc, hc, hv]
  · rw [put_eq, eqv_iff]
    exact ⟨hPm, hPb, hPf, by simp only [hPs], rfl, hPk⟩

/-- `throw_ref` with other operands or code around its exception drops them (3.0
`throw_ref-instrs`): only the active stack and code change. -/
theorem step_put_throwAdmin {m m' P : MState} {ts : List (Pos × TVal)} {rest : List AInstr}
    {a : Nat} {stk : List Val} (hP : Eqv P (put ts m)) (hc : m.code = .plain .throwRef :: rest)
    (hs : m.stack = .ref (.exn a) :: stk) (hb : (stk.isEmpty && rest.isEmpty) = false)
    (h : m.step = some m') : ∃ P', P.step = some P' ∧ Eqv P' (put ts m') := by
  simp only [MState.step, hc, Ref.toVal, MState.stepPlain, hs, hb, Bool.cond_false,
    Option.some.injEq] at h
  subst h
  rw [put_eq, eqv_iff] at hP
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP
  refine ⟨P.cont [.ref (.exn a)] [.plain .throwRef] [], ?_, ?_⟩
  · simp only [MState.step, hPc, hc, Ref.toVal, MState.stepPlain, hPs, hs, hb, Bool.cond_false]
  · rw [put_eq, eqv_iff]
    exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩

/-! ## Pushes: entries counted from the bottom keep their patches -/

/-- The control entry a position names (`loc`, `saved`), counted from the bottom. -/
def Pos.ctlIdx : Pos → Option Nat
  | .loc k _ | .saved k _ => some k
  | _ => none

/-- Every patch's control entry lies below `n`. -/
def CtlBound (ts : List (Pos × TVal)) (n : Nat) : Prop :=
  ∀ t ∈ ts, ∀ k, t.1.ctlIdx = some k → k < n

theorem CtlBound.mono {ts : List (Pos × TVal)} {n n' : Nat} (h : CtlBound ts n) (hn : n ≤ n') :
    CtlBound ts n' := fun t ht k hk => Nat.lt_of_lt_of_le (h t ht k hk) hn

theorem length_modifyAt {α : Type} (f : α → α) : ∀ (n : Nat) (xs : List α),
    (modifyAt f n xs).length = xs.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | n + 1, _ :: xs => by simp [modifyAt, length_modifyAt f n xs]

theorem putCtl_cons {ts : List (Pos × TVal)} {ctl : List Ctl} (e : Ctl)
    (hb : CtlBound ts ctl.length) : putCtl ts (e :: ctl) = e :: putCtl ts ctl := by
  induction ts generalizing ctl with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    have hb' : CtlBound ts ctl.length := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    have hidx : ∀ k, p.ctlIdx = some k → ctlAt (e :: ctl) k = ctlAt ctl k + 1 := by
      intro k hk
      have := hb (p, v) List.mem_cons_self k hk
      simp only [ctlAt, List.length_cons]
      omega
    cases p <;> cases v <;> simp only [putCtl] <;> try exact ih hb'
    case loc.val k i w =>
      rw [hidx k rfl]
      exact ih (ctl := modifyAt _ _ ctl) (by rw [length_modifyAt]; exact hb')
    case saved.val k j w =>
      rw [hidx k rfl]
      exact ih (ctl := modifyAt _ _ ctl) (by rw [length_modifyAt]; exact hb')

theorem putCtl_append {ts : List (Pos × TVal)} {ctl : List Ctl} (hb : CtlBound ts ctl.length) :
    ∀ es : List Ctl, putCtl ts (es ++ ctl) = es ++ putCtl ts ctl
  | [] => rfl
  | e :: es => by
    rw [List.cons_append, putCtl_cons e (by simpa using hb.mono (by simp)), putCtl_append hb es]
    rfl

/-- A push from an alike state: new operands + code, entries `es` above the control stack. -/
theorem eqv_push {m P : MState} {ts : List (Pos × TVal)} (hP : Eqv P (put ts m))
    (hb : CtlBound ts m.ctl.length) (stk : List Val) (code : List AInstr) (es : List Ctl) :
    Eqv { P with stack := stk, code := code, ctl := es ++ P.ctl }
      (put ts { m with stack := stk, code := code, ctl := es ++ m.ctl }) := by
  rw [put_eq, eqv_iff] at hP ⊢
  obtain ⟨hPm, hPb, hPf, -, -, hPk⟩ := hP
  exact ⟨hPm, hPb, hPf, rfl, rfl, by simp only [hPk, putCtl_append hb]⟩

theorem expand_locals (bt : BlockType) (f : Frame) (L : List (Option Val)) :
    bt.expand { f with locals := L } = bt.expand f := by
  cases bt <;> rfl

/-- `block`, `loop`, `try_table`: entries pushed, every position kept. -/
theorem step_put_enter {m m' P : MState} {ts : List (Pos × TVal)} {i : Instr}
    {rest : List AInstr} (hP : Eqv P (put ts m)) (hc : m.code = .plain i :: rest)
    (hi : (match i with | .block .. | .loop .. | .tryTable .. => true | _ => false) = true)
    (hb : CtlBound ts m.ctl.length) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put ts m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨-, -, hPf, hPs, hPc, -⟩ := hP'
  have hbt : ∀ bt : BlockType, bt.expand P.frame = bt.expand m.frame := fun bt => by
    rw [hPf]; exact expand_locals ..
  cases i <;> simp only [Bool.false_eq_true] at hi
  all_goals
    simp only [MState.step, hc, Ref.toVal, MState.stepPlain, Option.bind_eq_some_iff,
      MState.enter, MState.enterTry] at h
    obtain ⟨ft, hft, h⟩ := h
    cases hlt : Nat.blt m.stack.length ft.params.length <;>
      simp only [hlt, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h
    first
      | refine ⟨_, ?_, eqv_push hP hb _ _ [_]⟩
      | refine ⟨_, ?_, eqv_push hP hb _ _ [_, _]⟩
    simp only [MState.step, hPc, hc, Ref.toVal, MState.stepPlain, hbt, hft, Option.bind_some,
      MState.enter, MState.enterTry, hPs, hlt, Bool.cond_false]
    rfl

/-! ## `invoke`: the running frame becomes the new frame entry's caller -/

/-- `invoke`'s position map: the running frame's locals become the caller locals of the frame
entry pushed at bottom index `n`. -/
def invMap (n : Nat) : PMap
  | .top i => some (.loc n i)
  | p => some p

theorem putCtl_invoke {N : Nat} (lab : Ctl) (n : Nat) (saved : List Val) (rest : List AInstr) :
    ∀ {ts : List (Pos × TVal)}, CtlBound ts N → ∀ (f : Frame) (ctl : List Ctl), ctl.length = N →
    putCtl (move (invMap N) ts) (lab :: .frame n f saved rest :: ctl) =
      lab :: .frame n { f with locals := putLocals ts f.locals } saved rest :: putCtl ts ctl
  | [], _, _, _, _ => rfl
  | (p, v) :: ts, hb, f, ctl, hN => by
    have hb' : CtlBound ts N := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    have hidx : ∀ k, p.ctlIdx = some k →
        ctlAt (lab :: .frame n f saved rest :: ctl) k = ctlAt ctl k + 1 + 1 := by
      intro k hk
      have := hb (p, v) List.mem_cons_self k hk
      simp only [ctlAt, List.length_cons]
      omega
    have ih := putCtl_invoke lab n saved rest hb'
    cases p <;> cases v <;>
      simp only [move, invMap, List.filterMap_cons, Option.map_some] at ih ⊢ <;>
      simp only [putCtl, putLocals]
    case byte.byte => exact ih f ctl hN
    case byte.val => exact ih f ctl hN
    case top.byte => exact ih f ctl hN
    case top.val i w =>
      have h1 : ctlAt (lab :: .frame n f saved rest :: ctl) N = 0 + 1 := by
        simp only [ctlAt, List.length_cons]; omega
      rw [h1]
      simp only [modifyAt, setCallerLocal]
      exact ih { f with locals := f.locals.set i (some w) } ctl hN
    case loc.byte => exact ih f ctl hN
    case loc.val k i w =>
      rw [hidx k rfl]
      simp only [modifyAt]
      exact ih f _ (by rw [length_modifyAt, hN])
    case saved.byte => exact ih f ctl hN
    case saved.val k j w =>
      rw [hidx k rfl]
      simp only [modifyAt]
      exact ih f _ (by rw [length_modifyAt, hN])

theorem putLocals_move_invMap (ts : List (Pos × TVal)) (n : Nat) (L : List (Option Val)) :
    putLocals (move (invMap n) ts) L = L := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    cases p <;> cases v <;> simpa [move, invMap, putLocals] using ih

theorem putMems_move_invMap (ts : List (Pos × TVal)) (n : Nat) (ms : List MMem) :
    putMems (move (invMap n) ts) ms = putMems ts ms := by
  induction ts generalizing ms with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    cases p <;> cases v <;> simp only [move, invMap, List.filterMap_cons, Option.map_some,
      putMems] at ih ⊢ <;> exact ih _

/-- A call of a module function: positions follow `invMap`. -/
theorem step_put_invoke {m m' P : MState} {ts : List (Pos × TVal)} {a : Nat}
    {rest : List AInstr} (hP : Eqv P (put ts m)) (hc : m.code = .invoke a :: rest)
    (hb : CtlBound ts m.ctl.length) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move (invMap m.ctl.length) ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  have hfuncs : P.store.base.funcs = m.store.base.funcs := by
    have := congrArg Store.funcs hPb
    simpa using this
  simp only [MState.step, hc, Ref.toVal, MState.invoke] at h
  split at h
  next dt inst code hfa =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ft, hft, h⟩ := h
    cases hlt : Nat.blt m.stack.length ft.params.length <;>
      simp only [hlt, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h
    refine ⟨{ P with
      frame := ⟨(m.stack.take ft.params.length).reverse.map some ++ code.localDefaults, inst⟩
      stack := []
      code := code.body.map .plain
      ctl := .label ft.results.length [] [] [] ::
        .frame ft.results.length P.frame (m.stack.drop ft.params.length) rest :: P.ctl }, ?_, ?_⟩
    · simp only [MState.step, hPc, hc, Ref.toVal, MState.invoke, hfuncs, hfa, hft,
        Option.bind_some, hPs, hlt, Bool.cond_false]
    · rw [put_eq, eqv_iff]
      refine ⟨by simpa [putMems_move_invMap] using hPm, hPb, ?_, rfl, rfl, ?_⟩
      · simp only [putLocals_move_invMap]
      · rw [putCtl_invoke _ _ _ _ hb m.frame m.ctl rfl, hPk, hPf]
  next => simp at h

/-! ## Pops: the popped entry's patches, the rest moved by `popTo` -/

/-- Patches of `ts` on the entry at bottom index `k`, in order. -/
def putEntry : List (Pos × TVal) → Nat → Ctl → Ctl
  | [], _, e => e
  | (.loc k' i, .val v) :: ts, k, e => putEntry ts k (bif k' == k then setCallerLocal i v e else e)
  | (.saved k' j, .val v) :: ts, k, e => putEntry ts k (bif k' == k then setSaved j v e else e)
  | _ :: ts, k, e => putEntry ts k e

theorem move_cons (F : PMap) (p : Pos) (v : TVal) (ts : List (Pos × TVal)) :
    move F ((p, v) :: ts) = ((F p).map (·, v)).toList ++ move F ts := by
  simp only [move, List.filterMap_cons]
  cases F p <;> rfl

theorem ctlAt_cons_top {e : Ctl} {ctl : List Ctl} {N : Nat} (hN : ctl.length = N) :
    ctlAt (e :: ctl) N = 0 := by
  simp only [ctlAt, List.length_cons]; omega

theorem ctlAt_cons_lt {e : Ctl} {ctl : List Ctl} {N k : Nat} (hN : ctl.length = N) (hk : k < N) :
    ctlAt (e :: ctl) k = ctlAt ctl k + 1 := by
  simp only [ctlAt, List.length_cons]; omega

theorem putCtl_pop (b : Bool) {N : Nat} : ∀ {ts : List (Pos × TVal)} (e : Ctl) (ctl : List Ctl),
    ctl.length = N → CtlBound ts (N + 1) →
    putCtl ts (e :: ctl) = putEntry ts N e :: putCtl (move (popTo N b) ts) ctl
  | [], _, _, _, _ => rfl
  | (p, v) :: ts, e, ctl, hN, hb => by
    have hb' : CtlBound ts (N + 1) := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    have hk : ∀ k, p.ctlIdx = some k → k ≤ N := fun k hk =>
      Nat.le_of_lt_succ (hb (p, v) List.mem_cons_self k hk)
    have ih := fun e' ctl' (h' : ctl'.length = N) => putCtl_pop b (ts := ts) e' ctl' h' hb'
    rw [move_cons]
    cases p with
    | byte mi a =>
      cases v <;> simp only [popTo, Option.map_some, Option.toList_some, List.singleton_append,
        putCtl, putEntry] <;> exact ih e ctl hN
    | top i =>
      cases v <;> cases b <;> simp only [popTo, Bool.cond_true, Bool.cond_false, Option.map_some,
        Option.map_none, Option.toList_some, Option.toList_none, List.singleton_append,
        List.nil_append, putCtl, putEntry] <;> exact ih e ctl hN
    | loc k i =>
      have hkN := hk k rfl
      rcases Nat.lt_or_eq_of_le hkN with hlt | rfl
      · have h1 : (k == N) = false := by simpa using Nat.ne_of_lt hlt
        have h2 : decide (N < k) = false := by simpa using Nat.le_of_lt hlt
        cases v with
        | byte c =>
          simp only [popTo, h1, h2, Bool.cond_false, Option.map_some, Option.toList_some,
            List.singleton_append, putCtl, putEntry]
          exact ih e ctl hN
        | val w =>
          simp only [popTo, h1, h2, Bool.cond_false, Option.map_some, Option.toList_some,
            List.singleton_append, putCtl, putEntry, ctlAt_cons_lt hN hlt, modifyAt]
          exact ih e _ (by rw [length_modifyAt, hN])
      · cases v with
        | byte c =>
          cases b <;> simp only [popTo, beq_self_eq_true, Bool.cond_true, Bool.cond_false,
            Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
            List.singleton_append, List.nil_append, putCtl, putEntry] <;> exact ih e ctl hN
        | val w =>
          cases b <;> simp only [popTo, beq_self_eq_true, Bool.cond_true, Bool.cond_false,
            Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
            List.singleton_append, List.nil_append, putCtl, putEntry, ctlAt_cons_top hN,
            modifyAt] <;> exact ih _ ctl hN
    | saved k j =>
      have hkN := hk k rfl
      rcases Nat.lt_or_eq_of_le hkN with hlt | rfl
      · have h2 : decide (N ≤ k) = false := by simpa using hlt
        have h1 : (k == N) = false := by simpa using Nat.ne_of_lt hlt
        cases v with
        | byte c =>
          simp only [popTo, h2, Bool.cond_false, Option.map_some, Option.toList_some,
            List.singleton_append, putCtl, putEntry]
          exact ih e ctl hN
        | val w =>
          simp only [popTo, h2, Bool.cond_false, Option.map_some, Option.toList_some,
            List.singleton_append, putCtl, putEntry, h1, ctlAt_cons_lt hN hlt, modifyAt]
          exact ih e _ (by rw [length_modifyAt, hN])
      · cases v with
        | byte c =>
          simp only [popTo, le_refl, decide_true, Bool.cond_true, Option.map_none,
            Option.toList_none, List.nil_append, putCtl, putEntry]
          exact ih e ctl hN
        | val w =>
          simp only [popTo, le_refl, decide_true, Bool.cond_true, Option.map_none,
            Option.toList_none, List.nil_append, putCtl, putEntry, beq_self_eq_true,
            ctlAt_cons_top hN, modifyAt]
          exact ih _ ctl hN

theorem putEntry_label {k : Nat} (n : Nat) (cont : List Instr) (saved : List Val)
    (rest : List AInstr) : ∀ {ts : List (Pos × TVal)}, (∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j) →
    putEntry ts k (.label n cont saved rest) = .label n cont saved rest
  | [], _ => rfl
  | (p, v) :: ts, h => by
    have h' : ∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have h0 : ∀ j, p ≠ .saved k j := h (p, v) List.mem_cons_self
    cases p <;> cases v <;> simp only [putEntry, setCallerLocal, Bool.cond_self] <;>
      try exact putEntry_label n cont saved rest h'
    case saved.val k' j w =>
      have : (k' == k) = false := by simpa using fun hk => h0 j (by rw [hk])
      rw [this, Bool.cond_false]; exact putEntry_label n cont saved rest h'

theorem putEntry_handler {k : Nat} (n : Nat) (cs : List Catch) (saved : List Val)
    (rest : List AInstr) : ∀ {ts : List (Pos × TVal)}, (∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j) →
    putEntry ts k (.handler n cs saved rest) = .handler n cs saved rest
  | [], _ => rfl
  | (p, v) :: ts, h => by
    have h' : ∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have h0 : ∀ j, p ≠ .saved k j := h (p, v) List.mem_cons_self
    cases p <;> cases v <;> simp only [putEntry, setCallerLocal, Bool.cond_self] <;>
      try exact putEntry_handler n cs saved rest h'
    case saved.val k' j w =>
      have : (k' == k) = false := by simpa using fun hk => h0 j (by rw [hk])
      rw [this, Bool.cond_false]; exact putEntry_handler n cs saved rest h'

theorem putEntry_frame {k : Nat} (n : Nat) (saved : List Val) (rest : List AInstr) :
    ∀ {ts : List (Pos × TVal)} (f : Frame), (∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j) →
    putEntry ts k (.frame n f saved rest) =
      .frame n { f with locals := putLocals (move (popTo k true) ts) f.locals } saved rest
  | [], _, _ => rfl
  | (p, v) :: ts, f, h => by
    have h' : ∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have h0 : ∀ j, p ≠ .saved k j := h (p, v) List.mem_cons_self
    rw [move_cons]
    cases p with
    | byte mi a =>
      cases v <;> simp only [putEntry, popTo, Option.map_some, Option.toList_some,
        List.singleton_append, putLocals] <;> exact putEntry_frame n saved rest f h'
    | top i =>
      cases v <;> simp only [putEntry, popTo, Bool.cond_true, Option.map_none, Option.toList_none,
        List.nil_append] <;> exact putEntry_frame n saved rest f h'
    | loc k' i =>
      by_cases hk : k' = k
      · subst hk
        cases v with
        | byte c =>
          simp only [putEntry, popTo, beq_self_eq_true, Bool.cond_true, Option.map_some,
            Option.toList_some, List.singleton_append, putLocals]
          exact putEntry_frame n saved rest f h'
        | val w =>
          simp only [putEntry, popTo, beq_self_eq_true, Bool.cond_true, Option.map_some,
            Option.toList_some, List.singleton_append, putLocals, setCallerLocal]
          exact putEntry_frame n saved rest { f with locals := f.locals.set i (some w) } h'
      · have h1 : (k' == k) = false := by simpa using hk
        cases v <;> cases hlt : decide (k < k') <;>
          simp only [putEntry, popTo, h1, hlt, Bool.cond_false, Bool.cond_true, Option.map_some,
            Option.map_none, Option.toList_some, Option.toList_none, List.singleton_append,
            List.nil_append, putLocals] <;> exact putEntry_frame n saved rest f h'
    | saved k' j =>
      have hk : k' ≠ k := fun hk => h0 j (by rw [hk])
      have h1 : (k' == k) = false := by simpa using hk
      cases v <;> cases hle : decide (k ≤ k') <;>
        simp only [putEntry, popTo, h1, hle, Bool.cond_false, Bool.cond_true, Option.map_some,
          Option.map_none, Option.toList_some, Option.toList_none, List.singleton_append,
          List.nil_append, putLocals] <;> exact putEntry_frame n saved rest f h'

theorem popTo_loc (k k' i : Nat) (b : Bool) :
    popTo k b (.loc k' i) = none ∨ popTo k b (.loc k' i) = some (.top i) ∨
      popTo k b (.loc k' i) = some (.loc k' i) := by
  simp only [popTo]
  cases (k' == k) <;> cases b <;> cases decide (k < k') <;> simp

theorem popTo_saved (k k' j : Nat) (b : Bool) :
    popTo k b (.saved k' j) = none ∨ popTo k b (.saved k' j) = some (.saved k' j) := by
  simp only [popTo]
  cases decide (k ≤ k') <;> simp

theorem putMems_move_popTo (k : Nat) (b : Bool) :
    ∀ (ts : List (Pos × TVal)) (ms : List MMem), putMems (move (popTo k b) ts) ms = putMems ts ms
  | [], _ => rfl
  | (p, v) :: ts, ms => by
    rw [move_cons]
    have ih := putMems_move_popTo k b ts
    cases p with
    | byte mi a =>
      cases v <;> simp only [popTo, Option.map_some, Option.toList_some, List.singleton_append,
        putMems] <;> exact ih _
    | top i =>
      cases v <;> cases b <;> simp only [popTo, Bool.cond_true, Bool.cond_false, Option.map_some,
        Option.map_none, Option.toList_some, Option.toList_none, List.singleton_append,
        List.nil_append, putMems] <;> exact ih _
    | loc k' i =>
      rcases popTo_loc k k' i b with h | h | h <;> rw [h] <;> cases v <;>
        simp only [Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.singleton_append, List.nil_append, putMems] <;> exact ih _
    | saved k' j =>
      rcases popTo_saved k k' j b with h | h <;> rw [h] <;> cases v <;>
        simp only [Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.singleton_append, List.nil_append, putMems] <;> exact ih _

theorem putLocals_move_popTo (k : Nat) :
    ∀ (ts : List (Pos × TVal)) (L : List (Option Val)),
    putLocals (move (popTo k false) ts) L = putLocals ts L
  | [], _ => rfl
  | (p, v) :: ts, L => by
    rw [move_cons]
    have ih := putLocals_move_popTo k ts
    cases p with
    | byte mi a =>
      cases v <;> simp only [popTo, Option.map_some, Option.toList_some, List.singleton_append,
        putLocals] <;> exact ih _
    | top i =>
      cases v <;> simp only [popTo, Bool.cond_false, Option.map_some, Option.toList_some,
        List.singleton_append, putLocals] <;> exact ih _
    | loc k' i =>
      have h : popTo k false (.loc k' i) = none ∨ popTo k false (.loc k' i) = some (.loc k' i) := by
        simp only [popTo]; cases (k' == k) <;> cases decide (k < k') <;> simp
      rcases h with h | h <;> rw [h] <;> cases v <;>
        simp only [Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.singleton_append, List.nil_append, putLocals] <;> exact ih _
    | saved k' j =>
      rcases popTo_saved k k' j false with h | h <;> rw [h] <;> cases v <;>
        simp only [Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.singleton_append, List.nil_append, putLocals] <;> exact ih _

theorem noSaved_of_hitSaved {ps : List Pos} {ts : List (Pos × TVal)} {k : Nat}
    (hsup : ∀ t ∈ ts, t.1 ∈ ps) (h : hitSaved ps k = false) :
    ∀ t ∈ ts, ∀ j, t.1 ≠ .saved k j := by
  intro t ht j hj
  have hm := hsup t ht
  rw [hj] at hm
  simp only [hitSaved, List.any_eq_false] at h
  exact h _ hm (by simp)

/-- A block, handler or frame ends (empty code): its entry pops, positions follow `popTo`. -/
theorem step_put_exit {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    (hP : Eqv P (put ts m)) (hc : m.code = []) (hsup : ∀ t ∈ ts, t.1 ∈ ps)
    (hb : CtlBound ts m.ctl.length) (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  cases hk : m.ctl with
  | nil => simp [MState.step, hc, hk] at h
  | cons e ctl =>
    have hb1 : CtlBound ts (ctl.length + 1) := by simpa [hk] using hb
    simp only [tstep, hc, hk, List.length_cons, Nat.add_sub_cancel] at hF
    cases e with
    | label n cont saved rest =>
      cases hs : hitSaved ps ctl.length <;>
        simp only [hs, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
      subst hF
      have hns := noSaved_of_hitSaved hsup hs
      simp only [MState.step, hc, hk, Option.some.injEq] at h
      subst h
      refine ⟨{ P with
        stack := P.stack ++ saved
        code := rest
        ctl := putCtl (move (popTo ctl.length false) ts) ctl }, ?_, ?_⟩
      · simp only [MState.step, hPc, hc, hPk, hk, putCtl_pop false _ ctl rfl hb1,
          putEntry_label _ _ _ _ hns]
      · rw [put_eq, eqv_iff]
        exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb,
          by rw [hPf, putLocals_move_popTo], by rw [hPs], rfl, rfl⟩
    | handler n cs saved rest =>
      cases hs : hitSaved ps ctl.length <;>
        simp only [hs, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
      subst hF
      have hns := noSaved_of_hitSaved hsup hs
      simp only [MState.step, hc, hk, Option.some.injEq] at h
      subst h
      refine ⟨{ P with
        stack := P.stack ++ saved
        code := rest
        ctl := putCtl (move (popTo ctl.length false) ts) ctl }, ?_, ?_⟩
      · simp only [MState.step, hPc, hc, hPk, hk, putCtl_pop false _ ctl rfl hb1,
          putEntry_handler _ _ _ _ hns]
      · rw [put_eq, eqv_iff]
        exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb,
          by rw [hPf, putLocals_move_popTo], by rw [hPs], rfl, rfl⟩
    | frame n caller saved rest =>
      cases hs : hitSaved ps ctl.length <;>
        simp only [hs, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
      subst hF
      have hns := noSaved_of_hitSaved hsup hs
      simp only [MState.step, hc, hk] at h
      cases hn : Nat.beq m.stack.length n <;>
        simp only [hn, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
      subst h
      refine ⟨{ P with
        frame := { caller with locals := putLocals (move (popTo ctl.length true) ts) caller.locals }
        stack := P.stack ++ saved
        code := rest
        ctl := putCtl (move (popTo ctl.length true) ts) ctl }, ?_, ?_⟩
      · simp only [MState.step, hPc, hc, hPk, hk, putCtl_pop true _ ctl rfl hb1,
          putEntry_frame _ _ _ _ hns, hPs, hn, Bool.cond_true]
      · rw [put_eq, eqv_iff]
        exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, rfl, by rw [hPs], rfl, rfl⟩

/-! ## Multi-entry pops (`br`, `return`) -/

theorem move_move (F G : PMap) (ts : List (Pos × TVal)) :
    move G (move F ts) = move (fun p => (F p).bind G) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    rw [move_cons, move_cons]
    cases hF : F p with
    | none => simp only [Option.map_none, Option.toList_none, List.nil_append, Option.bind_none, ih]
    | some q =>
      rw [Option.map_some, Option.toList_some, List.singleton_append, move_cons, Option.bind_some,
        ih]

theorem popTo_popTo {k N : Nat} (hk : k ≤ N) (p : Pos) :
    (popTo N false p).bind (popTo k false) = popTo k false p := by
  cases p with
  | byte mi a => rfl
  | top i => rfl
  | loc k' i =>
    simp only [popTo]
    by_cases h1 : k' = N
    · subst h1
      have : (k' == k) = true ∨ decide (k < k') = true := by
        rcases Nat.lt_or_eq_of_le hk with h | h
        · right; simpa using h
        · left; simp [h]
      rcases this with h | h <;> simp [h]
    · by_cases h2 : N < k'
      · have h3 : (k' == k) = false := by simpa using (by omega : k' ≠ k)
        have h4 : decide (k < k') = true := by simpa using (by omega : k < k')
        simp [h1, h2, h3, h4]
      · simp [h1, h2, popTo]
  | saved k' j =>
    simp only [popTo]
    by_cases h1 : N ≤ k'
    · have h2 : k ≤ k' := Nat.le_trans hk h1
      simp [h1, h2]
    · simp [h1, popTo]

theorem move_popTo_popTo {k N : Nat} (hk : k ≤ N) (ts : List (Pos × TVal)) :
    move (popTo k false) (move (popTo N false) ts) = move (popTo k false) ts := by
  rw [move_move]
  congr 1
  funext p
  exact popTo_popTo hk p

theorem ctlIdx_popTo {N : Nat} {b : Bool} {p q : Pos} (h : popTo N b p = some q) {k : Nat}
    (hk : q.ctlIdx = some k) : k < N := by
  cases p with
  | byte mi a => simp only [popTo, Option.some.injEq] at h; subst h; simp [Pos.ctlIdx] at hk
  | top i =>
    cases b <;> simp only [popTo, Bool.cond_true, Bool.cond_false, reduceCtorEq,
      Option.some.injEq] at h
    subst h; simp [Pos.ctlIdx] at hk
  | loc k' i =>
    simp only [popTo] at h
    by_cases h1 : k' = N
    · subst h1
      cases b <;> simp only [beq_self_eq_true, Bool.cond_true, Bool.cond_false, reduceCtorEq,
        Option.some.injEq] at h
      subst h; simp [Pos.ctlIdx] at hk
    · by_cases h2 : N < k'
      · simp [h1, h2] at h
      · simp [h1, h2] at h
        subst h
        simp only [Pos.ctlIdx, Option.some.injEq] at hk
        omega
  | saved k' j =>
    simp only [popTo] at h
    by_cases h1 : N ≤ k'
    · simp [h1] at h
    · simp [h1] at h
      subst h
      simp only [Pos.ctlIdx, Option.some.injEq] at hk
      omega

theorem CtlBound.popTo (ts : List (Pos × TVal)) (N : Nat) (b : Bool) :
    CtlBound (move (popTo N b) ts) N := by
  intro t ht k hk
  simp only [move, List.mem_filterMap, Option.map_eq_some_iff] at ht
  obtain ⟨⟨p, v⟩, -, q, hq, rfl⟩ := ht
  exact ctlIdx_popTo hq hk

theorem putEntry_label_shape (k n : Nat) (cont : List Instr) (rest : List AInstr) :
    ∀ (ts : List (Pos × TVal)) (saved : List Val),
    ∃ saved', putEntry ts k (.label n cont saved rest) = .label n cont saved' rest
  | [], saved => ⟨saved, rfl⟩
  | (p, v) :: ts, saved => by
    cases p <;> cases v <;> simp only [putEntry] <;>
      first
      | exact putEntry_label_shape k n cont rest ts saved
      | (cases (_ == k) <;>
          simp only [Bool.cond_true, Bool.cond_false, setCallerLocal, setSaved] <;>
          first
          | exact putEntry_label_shape k n cont rest ts saved
          | exact putEntry_label_shape k n cont rest ts _)

theorem putEntry_handler_shape (k n : Nat) (cs : List Catch) (rest : List AInstr) :
    ∀ (ts : List (Pos × TVal)) (saved : List Val),
    ∃ saved', putEntry ts k (.handler n cs saved rest) = .handler n cs saved' rest
  | [], saved => ⟨saved, rfl⟩
  | (p, v) :: ts, saved => by
    cases p <;> cases v <;> simp only [putEntry] <;>
      first
      | exact putEntry_handler_shape k n cs rest ts saved
      | (cases (_ == k) <;>
          simp only [Bool.cond_true, Bool.cond_false, setCallerLocal, setSaved] <;>
          first
          | exact putEntry_handler_shape k n cs rest ts saved
          | exact putEntry_handler_shape k n cs rest ts _)

theorem noSaved_move {K N : Nat} {b : Bool} {ts : List (Pos × TVal)}
    (h : ∀ t ∈ ts, ∀ j, t.1 ≠ .saved K j) : ∀ t ∈ move (popTo N b) ts, ∀ j, t.1 ≠ .saved K j := by
  intro t ht j hj
  simp only [move, List.mem_filterMap, Option.map_eq_some_iff] at ht
  obtain ⟨⟨p, v⟩, hm, q, hq, rfl⟩ := ht
  simp only at hj
  subst hj
  cases p with
  | byte => simp [popTo] at hq
  | top => cases b <;> simp [popTo] at hq
  | loc k' i => rcases popTo_loc N k' i b with h' | h' | h' <;> rw [h'] at hq <;> simp at hq
  | saved k' j' =>
    rcases popTo_saved N k' j' b with h' | h' <;> rw [h'] at hq <;> simp only [reduceCtorEq,
      Option.some.injEq, Pos.saved.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact h _ hm _ rfl

theorem brPop_length : ∀ {l : Nat} {stk : List Val} {ctl : List Ctl}
    {r : List Val × List AInstr × List Ctl}, brPop l stk ctl = some r → r.2.2.length < ctl.length
  | 0, stk, .label n cont saved rest :: ctl, r, h => by
    simp only [brPop] at h
    cases hb : Nat.blt stk.length n <;>
      simp only [hb, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h; simp
  | l + 1, _, .label .. :: _, _, h => by
    simp only [brPop] at h; have := brPop_length h; simp only [List.length_cons]; omega
  | l, _, .handler .. :: _, _, h => by
    simp only [brPop] at h; have := brPop_length h; simp only [List.length_cons]; omega
  | 0, _, .frame .. :: _, _, h | _ + 1, _, .frame .. :: _, _, h | _, _, [], _, h => by
    simp [brPop] at h

theorem brPop_target : ∀ {l : Nat} {stk : List Val} {ctl : List Ctl}
    {r : List Val × List AInstr × List Ctl}, brPop l stk ctl = some r →
    brTarget l ctl = some r.2.2.length
  | 0, stk, .label n cont saved rest :: ctl, r, h => by
    simp only [brPop] at h
    cases hb : Nat.blt stk.length n <;>
      simp only [hb, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h; rfl
  | l + 1, _, .label .. :: _, _, h => by
    simp only [brPop] at h; simpa [brTarget] using brPop_target h
  | l, _, .handler .. :: _, _, h => by
    simp only [brPop] at h; cases l <;> simpa [brTarget] using brPop_target h
  | 0, _, .frame .. :: _, _, h | _ + 1, _, .frame .. :: _, _, h | _, _, [], _, h => by
    simp [brPop] at h

theorem brPop_put : ∀ {l : Nat} {stk : List Val} {ctl : List Ctl}
    {r : List Val × List AInstr × List Ctl} {ts : List (Pos × TVal)}, brPop l stk ctl = some r →
    CtlBound ts ctl.length → (∀ t ∈ ts, ∀ j, t.1 ≠ .saved r.2.2.length j) →
    brTarget l ctl = some r.2.2.length ∧
      brPop l stk (putCtl ts ctl) =
        some (r.1, r.2.1, putCtl (move (popTo r.2.2.length false) ts) r.2.2)
  | 0, stk, .label n cont saved rest :: ctl, r, ts, h, hb, hs => by
    simp only [brPop] at h
    cases hbl : Nat.blt stk.length n <;>
      simp only [hbl, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_⟩
    rw [putCtl_pop false _ ctl rfl (by simpa using hb), putEntry_label _ _ _ _ hs]
    simp only [brPop, hbl, Bool.cond_false]
  | l + 1, stk, .label n cont saved rest :: ctl, r, ts, h, hb, hs => by
    simp only [brPop] at h
    have hlt := brPop_length h
    obtain ⟨ht, hp⟩ := brPop_put (ts := move (popTo ctl.length false) ts) h
      (CtlBound.popTo ts _ false) (noSaved_move hs)
    refine ⟨by simpa [brTarget] using ht, ?_⟩
    obtain ⟨saved', he⟩ := putEntry_label_shape ctl.length n cont rest ts saved
    rw [putCtl_pop false _ ctl rfl (by simpa using hb), he]
    simp only [brPop, hp, move_popTo_popTo (Nat.le_of_lt hlt)]
  | l, stk, .handler n cs saved rest :: ctl, r, ts, h, hb, hs => by
    simp only [brPop] at h
    have hlt := brPop_length h
    obtain ⟨ht, hp⟩ := brPop_put (ts := move (popTo ctl.length false) ts) h
      (CtlBound.popTo ts _ false) (noSaved_move hs)
    refine ⟨by cases l <;> simpa [brTarget] using ht, ?_⟩
    obtain ⟨saved', he⟩ := putEntry_handler_shape ctl.length n cs rest ts saved
    rw [putCtl_pop false _ ctl rfl (by simpa using hb), he]
    cases l <;> simp only [brPop, hp, move_popTo_popTo (Nat.le_of_lt hlt)]
  | 0, _, .frame .. :: _, _, _, h, _, _ | _ + 1, _, .frame .. :: _, _, _, h, _, _
  | _, _, [], _, _, h, _, _ => by simp [brPop] at h

/-- `br l`: labels and handlers pop down to the target label (`brTarget`), whose saved operands
return; positions follow `popTo` at the target. -/
theorem step_put_br {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {l : Nat} {rest : List AInstr} (hP : Eqv P (put ts m)) (hc : m.code = .plain (.br l) :: rest)
    (hsup : ∀ t ∈ ts, t.1 ∈ ps) (hb : CtlBound ts m.ctl.length) (hF : tstep ps m = some F)
    (h : m.step = some m') : ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  simp only [MState.step, hc, Ref.toVal, MState.stepPlain, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  have hlt := brPop_length hr
  have htarget := brPop_target hr
  simp only [tstep, hc, Ref.toVal, plainMap, htarget] at hF
  cases hs : hitSaved ps r.2.2.length <;>
    simp only [hs, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
  subst hF
  have hns := noSaved_of_hitSaved hsup hs
  obtain ⟨-, hp⟩ := brPop_put hr hb hns
  refine ⟨{ P with
    stack := r.1
    code := r.2.1
    ctl := putCtl (move (popTo r.2.2.length false) ts) r.2.2 }, ?_, ?_⟩
  · simp only [MState.step, hPc, hc, Ref.toVal, MState.stepPlain, hPs, hPk, hp, Option.map_some]
  · rw [put_eq, eqv_iff]
    exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, by rw [hPf, putLocals_move_popTo], rfl,
      rfl, rfl⟩

theorem popTo_true_popTo {k N : Nat} (hk : k < N) (p : Pos) :
    (popTo N false p).bind (popTo k true) = popTo k true p := by
  cases p with
  | byte mi a => rfl
  | top i => rfl
  | loc k' i =>
    simp only [popTo]
    by_cases h1 : k' = N
    · subst h1
      have h3 : (k' == k) = false := by simpa using (by omega : k' ≠ k)
      have h4 : decide (k < k') = true := by simpa using hk
      simp [h3, h4]
    · by_cases h2 : N < k'
      · have h3 : (k' == k) = false := by simpa using (by omega : k' ≠ k)
        have h4 : decide (k < k') = true := by simpa using (by omega : k < k')
        simp [h1, h2, h3, h4]
      · simp [h1, h2, popTo]
  | saved k' j =>
    simp only [popTo]
    by_cases h1 : N ≤ k'
    · have h2 : k ≤ k' := by omega
      simp [h1, h2]
    · simp [h1, popTo]

theorem move_popTo_true {k N : Nat} (hk : k < N) (ts : List (Pos × TVal)) :
    move (popTo k true) (move (popTo N false) ts) = move (popTo k true) ts := by
  rw [move_move]
  congr 1
  funext p
  exact popTo_true_popTo hk p

theorem retPop_length : ∀ {stk : List Val} {ctl : List Ctl}
    {r : Frame × List Val × List AInstr × List Ctl}, retPop stk ctl = some r →
    r.2.2.2.length < ctl.length
  | _, .label .. :: _, _, h | _, .handler .. :: _, _, h => by
    simp only [retPop] at h; have := retPop_length h; simp only [List.length_cons]; omega
  | stk, .frame n caller saved rest :: ctl, r, h => by
    simp only [retPop] at h
    cases hb : Nat.blt stk.length n <;>
      simp only [hb, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h; simp
  | _, [], _, h => by simp [retPop] at h

theorem retPop_frameAt : ∀ {stk : List Val} {ctl : List Ctl}
    {r : Frame × List Val × List AInstr × List Ctl}, retPop stk ctl = some r →
    frameAt ctl = some r.2.2.2.length
  | _, .label .. :: _, _, h => by simp only [retPop] at h; simpa [frameAt] using retPop_frameAt h
  | _, .handler .. :: _, _, h => by simp only [retPop] at h; simpa [frameAt] using retPop_frameAt h
  | stk, .frame n caller saved rest :: ctl, r, h => by
    simp only [retPop] at h
    cases hb : Nat.blt stk.length n <;>
      simp only [hb, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h; rfl
  | _, [], _, h => by simp [retPop] at h

theorem retPop_put : ∀ {stk : List Val} {ctl : List Ctl}
    {r : Frame × List Val × List AInstr × List Ctl} {ts : List (Pos × TVal)},
    retPop stk ctl = some r → CtlBound ts ctl.length →
    (∀ t ∈ ts, ∀ j, t.1 ≠ .saved r.2.2.2.length j) →
    retPop stk (putCtl ts ctl) =
      some ({ r.1 with locals := putLocals (move (popTo r.2.2.2.length true) ts) r.1.locals },
        r.2.1, r.2.2.1, putCtl (move (popTo r.2.2.2.length true) ts) r.2.2.2)
  | stk, .label n cont saved rest :: ctl, r, ts, h, hb, hs => by
    simp only [retPop] at h
    have hlt := retPop_length h
    have hp := retPop_put (ts := move (popTo ctl.length false) ts) h (CtlBound.popTo ts _ false)
      (noSaved_move hs)
    obtain ⟨saved', he⟩ := putEntry_label_shape ctl.length n cont rest ts saved
    rw [putCtl_pop false _ ctl rfl (by simpa using hb), he]
    simp only [retPop, hp, move_popTo_true hlt]
  | stk, .handler n cs saved rest :: ctl, r, ts, h, hb, hs => by
    simp only [retPop] at h
    have hlt := retPop_length h
    have hp := retPop_put (ts := move (popTo ctl.length false) ts) h (CtlBound.popTo ts _ false)
      (noSaved_move hs)
    obtain ⟨saved', he⟩ := putEntry_handler_shape ctl.length n cs rest ts saved
    rw [putCtl_pop false _ ctl rfl (by simpa using hb), he]
    simp only [retPop, hp, move_popTo_true hlt]
  | stk, .frame n caller saved rest :: ctl, r, ts, h, hb, hs => by
    simp only [retPop] at h
    cases hbl : Nat.blt stk.length n <;>
      simp only [hbl, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [putCtl_pop true _ ctl rfl (by simpa using hb), putEntry_frame _ _ _ _ hs]
    simp only [retPop, hbl, Bool.cond_false]
  | _, [], _, _, h, _, _ => by simp [retPop] at h

/-- `return`: labels and handlers pop down to the innermost frame, whose caller runs again with
its saved operands; positions follow `popTo` at that frame. -/
theorem step_put_return {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {rest : List AInstr} (hP : Eqv P (put ts m)) (hc : m.code = .plain .return_ :: rest)
    (hsup : ∀ t ∈ ts, t.1 ∈ ps) (hb : CtlBound ts m.ctl.length) (hF : tstep ps m = some F)
    (h : m.step = some m') : ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  simp only [MState.step, hc, Ref.toVal, MState.stepPlain, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  simp only [tstep, hc, Ref.toVal, plainMap, retPop_frameAt hr] at hF
  cases hs : hitSaved ps r.2.2.2.length <;>
    simp only [hs, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
  subst hF
  have hp := retPop_put hr hb (noSaved_of_hitSaved hsup hs)
  refine ⟨{ P with
    frame := { r.1 with locals := putLocals (move (popTo r.2.2.2.length true) ts) r.1.locals }
    stack := r.2.1
    code := r.2.2.1
    ctl := putCtl (move (popTo r.2.2.2.length true) ts) r.2.2.2 }, ?_, ?_⟩
  · simp only [MState.step, hPc, hc, Ref.toVal, MState.stepPlain, hPs, hPk, hp, Option.map_some]
  · rw [put_eq, eqv_iff]
    exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, rfl, rfl, rfl, rfl⟩

/-! ## Unwinding (`throw_ref` with its exception alone: `MState.throwPop`) -/

/-- The saved-operand patches of `ts` on entry `k`, in order. -/
def putSaved : List (Pos × TVal) → Nat → List Val → List Val
  | [], _, sv => sv
  | (.saved k' j, .val v) :: ts, k, sv => putSaved ts k (bif k' == k then sv.set j v else sv)
  | _ :: ts, k, sv => putSaved ts k sv

theorem putEntry_handler_eq (k n : Nat) (cs : List Catch) (rest : List AInstr) :
    ∀ (ts : List (Pos × TVal)) (saved : List Val),
    putEntry ts k (.handler n cs saved rest) = .handler n cs (putSaved ts k saved) rest
  | [], _ => rfl
  | (p, v) :: ts, saved => by
    cases p <;> cases v <;> simp only [putEntry, putSaved] <;>
      first
      | exact putEntry_handler_eq k n cs rest ts saved
      | (cases (_ == k) <;>
          simp only [Bool.cond_true, Bool.cond_false, setCallerLocal, setSaved] <;>
          exact putEntry_handler_eq k n cs rest ts _)

theorem catchStep_congr (S : Store) (f : Frame) (M : List MemInst) (L : List (Option Val))
    (a : Nat) (c : Catch) :
    Ref.catchStep { S with mems := M } { f with locals := L } a c = Ref.catchStep S f a c := by
  cases c <;> rfl

/-- `throw_ref` on its exception alone: the innermost entry takes it (`MState.throwPop`). -/
theorem step_put_throw {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {a : Nat} (hP : Eqv P (put ts m)) (hc : m.code = [.plain .throwRef])
    (hs : m.stack = [.ref (.exn a)]) (hsup : ∀ t ∈ ts, t.1 ∈ ps) (hb : CtlBound ts m.ctl.length)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  have habs : P.store.abs = { m.store.abs with mems := P.store.mems.map MMem.abs } :=
    base_congr hPb _
  simp only [MState.step, hc, hs, Ref.toVal, MState.stepPlain, List.isEmpty_nil, Bool.and_self,
    Bool.cond_true, MState.throwPop] at h
  simp only [tstep, hc, hs, Ref.toVal, plainMap, List.isEmpty_nil, Bool.and_self, Bool.cond_true,
    throwMap] at hF
  have hPstep : P.step = P.throwPop a := by
    simp only [MState.step, hPc, hc, hPs, hs, Ref.toVal, MState.stepPlain, List.isEmpty_nil,
      Bool.and_self, Bool.cond_true]
  cases hk : m.ctl with
  | nil => simp [hk] at h
  | cons e ctl =>
    have hb1 : CtlBound ts (ctl.length + 1) := by simpa [hk] using hb
    simp only [hk, List.length_cons, Nat.add_sub_cancel] at hF h
    cases e with
    | label n cont saved rest =>
      cases hsv : hitSaved ps ctl.length <;>
        simp only [hsv, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
      subst hF
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨{ P with
        stack := .ref (.exn a) :: saved
        code := .plain .throwRef :: rest
        ctl := putCtl (move (popTo ctl.length false) ts) ctl }, ?_, ?_⟩
      · rw [hPstep]
        simp only [MState.throwPop, hPk, hk, putCtl_pop false _ ctl rfl hb1,
          putEntry_label _ _ _ _ (noSaved_of_hitSaved hsup hsv)]
      · rw [put_eq, eqv_iff]
        exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, by rw [hPf, putLocals_move_popTo], rfl,
          rfl, rfl⟩
    | frame n caller saved rest =>
      cases hsv : hitSaved ps ctl.length <;>
        simp only [hsv, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
      subst hF
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨{ P with
        frame := { caller with locals := putLocals (move (popTo ctl.length true) ts) caller.locals }
        stack := .ref (.exn a) :: saved
        code := .plain .throwRef :: rest
        ctl := putCtl (move (popTo ctl.length true) ts) ctl }, ?_, ?_⟩
      · rw [hPstep]
        simp only [MState.throwPop, hPk, hk, putCtl_pop true _ ctl rfl hb1,
          putEntry_frame _ _ _ _ (noSaved_of_hitSaved hsup hsv)]
      · rw [put_eq, eqv_iff]
        exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, rfl, rfl, rfl, rfl⟩
    | handler n cs saved rest =>
      cases cs with
      | nil =>
        cases hsv : hitSaved ps ctl.length <;>
          simp only [hsv, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
        subst hF
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨{ P with
          stack := .ref (.exn a) :: saved
          code := .plain .throwRef :: rest
          ctl := putCtl (move (popTo ctl.length false) ts) ctl }, ?_, ?_⟩
        · rw [hPstep]
          simp only [MState.throwPop, hPk, hk, putCtl_pop false _ ctl rfl hb1,
            putEntry_handler _ _ _ _ (noSaved_of_hitSaved hsup hsv)]
        · rw [put_eq, eqv_iff]
          exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, by rw [hPf, putLocals_move_popTo],
            rfl, rfl, rfl⟩
      | cons c cs' =>
        have hcat :
            Ref.catchStep P.store.abs P.frame a c = Ref.catchStep m.store.abs m.frame a c := by
          rw [habs, hPf]; exact catchStep_congr ..
        cases hcs : Ref.catchStep m.store.abs m.frame a c with
        | some out =>
          simp only [hcs] at hF h
          cases hsv : hitSaved ps ctl.length <;>
            simp only [hsv, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
          subst hF
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨{ P with
            stack := saved
            code := out ++ rest
            ctl := putCtl (move (popTo ctl.length false) ts) ctl }, ?_, ?_⟩
          · rw [hPstep]
            simp only [MState.throwPop, hPk, hk, putCtl_pop false _ ctl rfl hb1,
              putEntry_handler _ _ _ _ (noSaved_of_hitSaved hsup hsv), hcat, hcs]
          · rw [put_eq, eqv_iff]
            exact ⟨by rw [putMems_move_popTo]; exact hPm, hPb, by rw [hPf, putLocals_move_popTo],
              rfl, rfl, rfl⟩
        | none =>
          simp only [hcs, Option.some.injEq] at hF h
          subst hF
          subst h
          refine ⟨{ P with
            ctl := .handler n cs' (putSaved ts ctl.length saved) rest ::
              putCtl (move (popTo ctl.length false) ts) ctl }, ?_, ?_⟩
          · rw [hPstep]
            simp only [MState.throwPop, hPk, hk, putCtl_pop false _ ctl rfl hb1,
              putEntry_handler_eq, hcat, hcs]
          · rw [put_eq, eqv_iff, move_some]
            refine ⟨hPm, hPb, hPf, by simpa [hs] using hPs, by simpa [hc] using hPc, ?_⟩
            simp only [putCtl_pop false _ ctl rfl hb1, putEntry_handler_eq]

/-! ## Bytes: the patched memory, byte by byte -/

/-- Byte `x` of memory `mi` after the byte patches `ts`, over the original byte `o`. -/
def pbyte : List (Pos × TVal) → Nat → Nat → Nat → Nat
  | [], _, _, o => o
  | (.byte mi' a, .byte b) :: ts, mi, x, o => pbyte ts mi x (bif mi' == mi && a == x then b else o)
  | _ :: ts, mi, x, o => pbyte ts mi x o

/-- Every byte patch of `ts` holds a byte and lies inside its (existing) memory. -/
def BytesOK (ts : List (Pos × TVal)) (ms : List MMem) : Prop :=
  ∀ mi a b, (Pos.byte mi a, TVal.byte b) ∈ ts → b < 256 ∧ ∃ mm, ms[mi]? = some mm ∧ a < mm.size

theorem getElem?_modifyAt {α : Type} (f : α → α) : ∀ (n : Nat) (xs : List α) (i : Nat),
    (modifyAt f n xs)[i]? = if i = n then (xs[i]?).map f else xs[i]?
  | _, [], i => by simp [modifyAt]
  | 0, x :: xs, 0 => by simp [modifyAt]
  | 0, x :: xs, i + 1 => by simp [modifyAt]
  | n + 1, x :: xs, 0 => by simp [modifyAt]
  | n + 1, x :: xs, i + 1 => by simp [modifyAt, getElem?_modifyAt f n xs i]

theorem mem_modifyAt {α : Type} {f : α → α} {P : α → Prop} (hf : ∀ x, P x → P (f x)) :
    ∀ (n : Nat) (xs : List α), (∀ x ∈ xs, P x) → ∀ x ∈ modifyAt f n xs, P x
  | _, [], h => by simp [modifyAt]
  | 0, y :: ys, h => by
    simp only [modifyAt, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ⟨hf _ h.1, h.2⟩
  | n + 1, y :: ys, h => by
    simp only [modifyAt, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ⟨h.1, mem_modifyAt hf n ys h.2⟩

theorem byte_writeBytes1 {mm : MMem} (hi : mm.Inv) {a b : Nat} (ha : a < mm.size) (hb : b < 256)
    (x : Nat) : (mm.writeBytes a [b]).byte x = bif a == x then b else mm.byte x := by
  have hc := hi.2.1
  rw [MMem.byte_writeBytes hi.1
    (by simp only [List.length_singleton]; unfold MMem.Cover at hc; omega)
    (by simpa using hb)]
  by_cases h : a = x
  · subst h; simp
  · have : ¬ (a ≤ x ∧ x < a + [b].length) := by simp only [List.length_singleton]; omega
    simp only [this, ↓reduceIte]
    simp [h]

theorem putMems_spec : ∀ (ts : List (Pos × TVal)) (ms : List MMem), (∀ mm ∈ ms, mm.Inv) →
    BytesOK ts ms →
    (∀ mm ∈ putMems ts ms, mm.Inv) ∧
    ∀ mi mm, ms[mi]? = some mm → ∃ mm', (putMems ts ms)[mi]? = some mm' ∧
      mm'.pages = mm.pages ∧ mm'.max = mm.max ∧ mm'.depth = mm.depth ∧
      ∀ x, mm'.byte x = pbyte ts mi x (mm.byte x)
  | [], ms, hi, _ => ⟨hi, fun _ mm h => ⟨mm, h, rfl, rfl, rfl, fun _ => rfl⟩⟩
  | (p, v) :: ts, ms, hi, hok => by
    have htail : BytesOK ts ms := fun mi a b hm => hok mi a b (List.mem_cons_of_mem _ hm)
    cases p with
    | byte mi' a =>
      cases v with
      | byte b =>
        obtain ⟨hb, mm0, hmm0, ha⟩ := hok mi' a b List.mem_cons_self
        set ms₁ := modifyAt (fun mm => mm.writeBytes a [b]) mi' ms with hms₁
        have hget₁ : ∀ (mi : Nat) (mm : MMem), ms[mi]? = some mm → ms₁[mi]? =
            some (if mi = mi' then mm.writeBytes a [b] else mm) := by
          intro mi mm h
          rw [hms₁, getElem?_modifyAt, h]
          split <;> rfl
        have hback : ∀ (mi : Nat) (mm' : MMem), ms₁[mi]? = some mm' → ∃ mm, ms[mi]? = some mm := by
          intro mi mm' h
          rw [hms₁, getElem?_modifyAt] at h
          split at h
          · cases hx : ms[mi]? <;> simp_all
          · exact ⟨mm', h⟩
        have hi₁ : ∀ mm ∈ ms₁, mm.Inv := by
          intro mm hm
          obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.mp hm
          obtain ⟨mm1, h1⟩ := hback i mm hi'
          rw [hget₁ i mm1 h1, Option.some.injEq] at hi'
          have hin : mm1.Inv := hi mm1 (List.mem_of_getElem? h1)
          split at hi'
          · subst hi'
            rename_i hii
            subst hii
            rw [hmm0, Option.some.injEq] at h1
            subst h1
            exact MMem.writeBytes_inv hin (by simp only [List.length_singleton]; omega)
              (by simpa using hb)
          · subst hi'; exact hin
        have hok₁ : BytesOK ts ms₁ := by
          intro mi a' b' hm
          obtain ⟨hb', mm, hmm, ha'⟩ := htail mi a' b' hm
          refine ⟨hb', _, hget₁ mi mm hmm, ?_⟩
          split
          · simp only [MMem.size, (MMem.writeBytes_fields mm a [b]).1]; exact ha'
          · exact ha'
        obtain ⟨hi', hspec⟩ := putMems_spec ts ms₁ hi₁ hok₁
        refine ⟨hi', fun mi mm h => ?_⟩
        obtain ⟨mm', h', hp, hm, hd, hby⟩ := hspec mi _ (hget₁ mi mm h)
        have hf := MMem.writeBytes_fields mm a [b]
        refine ⟨mm', h', ?_, ?_, ?_, fun x => ?_⟩
        · rw [hp]; split <;> simp [hf.1]
        · rw [hm]; split <;> simp [hf.2.1]
        · rw [hd]; split <;> simp [hf.2.2]
        · rw [hby x]
          simp only [pbyte]
          congr 1
          by_cases hmi : mi = mi'
          · subst hmi
            rw [hmm0, Option.some.injEq] at h
            subst h
            simp only [↓reduceIte, beq_self_eq_true, Bool.true_and]
            exact byte_writeBytes1 (hi _ (List.mem_of_getElem? hmm0)) ha hb x
          · have : (mi' == mi) = false := by simpa using Ne.symm hmi
            simp [hmi, this]
      | val w => simpa [putMems, pbyte] using putMems_spec ts ms hi htail
    | top i => cases v <;> simpa [putMems, pbyte] using putMems_spec ts ms hi htail
    | loc k i => cases v <;> simpa [putMems, pbyte] using putMems_spec ts ms hi htail
    | saved k j => cases v <;> simpa [putMems, pbyte] using putMems_spec ts ms hi htail

theorem pbyte_nohit {mi x : Nat} : ∀ {ts : List (Pos × TVal)} (o : Nat),
    (∀ t ∈ ts, t.1 ≠ .byte mi x) → pbyte ts mi x o = o
  | [], _, _ => rfl
  | (p, v) :: ts, o, h => by
    have h' : ∀ t ∈ ts, t.1 ≠ .byte mi x := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have h0 : p ≠ .byte mi x := h (p, v) List.mem_cons_self
    cases p <;> cases v <;> simp only [pbyte] <;> try exact pbyte_nohit o h'
    case byte.byte mi' a b =>
      have : (mi' == mi && a == x) = false := by
        cases h1 : (mi' == mi) <;> cases h2 : (a == x) <;> simp_all
      rw [this, Bool.cond_false]; exact pbyte_nohit o h'

theorem read_congr {m₁ m₂ : MMem} : ∀ {ea : Nat} (n : Nat),
    (∀ x, ea ≤ x → x < ea + n → m₁.byte x = m₂.byte x) → m₁.read ea n = m₂.read ea n
  | _, 0, _ => rfl
  | ea, n + 1, h => by
    simp only [MMem.read]
    rw [h ea (Nat.le_refl _) (by omega), read_congr n (fun x h1 h2 => h x (by omega) (by omega))]

theorem noByte_of_hitBytes {ps : List Pos} {ts : List (Pos × TVal)} {mi ea n : Nat}
    (hsup : ∀ t ∈ ts, t.1 ∈ ps) (h : hitBytes ps mi ea n = false) :
    ∀ x, ea ≤ x → x < ea + n → ∀ t ∈ ts, t.1 ≠ .byte mi x := by
  intro x h1 h2 t ht hx
  have hm := hsup t ht
  rw [hx] at hm
  simp only [hitBytes, List.any_eq_false] at h
  exact h _ hm (by simp [h1, h2])

theorem length_putMems : ∀ (ts : List (Pos × TVal)) (ms : List MMem),
    (putMems ts ms).length = ms.length
  | [], _ => rfl
  | (p, v) :: ts, ms => by
    cases p <;> cases v <;> simp only [putMems, length_putMems ts, length_modifyAt]

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {b : β}, l₂[i]? = some b → ∃ a, l₁[i]? = some a ∧ R a b
  | [], [], .nil, _, _, hb => by simp at hb
  | a :: _, b :: _, .cons hab _, 0, _, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb ⊢; subst hb; exact ⟨a, rfl, hab⟩
  | _ :: _, _ :: _, .cons _ hr, i + 1, _, hb => by
    simp only [List.getElem?_cons_succ] at hb ⊢; exact forall₂_getElem? hr hb

/-- `P`'s memories under `Eqv P (put ts m)`: each `m` memory's pages, maximum and depth, its
bytes patched (`pbyte`). -/
theorem eqv_mem {m P : MState} {ts : List (Pos × TVal)} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems) :
    (∀ mi : Nat, m.store.mems[mi]? = none → P.store.mems[mi]? = none) ∧
    ∀ (mi : Nat) (mm : MMem), m.store.mems[mi]? = some mm → ∃ mmP, P.store.mems[mi]? = some mmP ∧
      mmP.pages = mm.pages ∧ mmP.max = mm.max ∧ mmP.depth = mm.depth ∧
      ∀ x, mmP.byte x = pbyte ts mi x (mm.byte x) := by
  rw [put_eq, eqv_iff] at hP
  have hF := hP.1
  obtain ⟨-, hspec⟩ := putMems_spec ts m.store.mems hinv hok
  have hlen := length_putMems ts m.store.mems
  refine ⟨fun mi h => ?_, fun mi mm h => ?_⟩
  · have := hF.length_eq
    rw [List.getElem?_eq_none_iff] at h ⊢
    simp only at this
    omega
  · obtain ⟨mm', h', hp, hm, hd, hby⟩ := hspec mi mm h
    obtain ⟨i, hi, hq⟩ := forall₂_getElem? hF h'
    obtain ⟨e1, e2, e3, e4⟩ := hq
    exact ⟨i, hi, e1.trans hp, e2.trans hm, e3.trans hd, fun x => (e4 x).trans (hby x)⟩

theorem mem0_eqv {m P : MState} {ts : List (Pos × TVal)} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems) :
    (m.mem0 = none → P.mem0 = none) ∧
    ∀ a mm, m.mem0 = some (a, mm) → ∃ mmP, P.mem0 = some (a, mmP) ∧
      mmP.pages = mm.pages ∧ mmP.max = mm.max ∧ mmP.depth = mm.depth ∧
      ∀ x, mmP.byte x = pbyte ts a x (mm.byte x) := by
  obtain ⟨hnone, hsome⟩ := eqv_mem hP hinv hok
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  have hinst : P.frame.inst = m.frame.inst := by rw [hP'.2.2.1]
  refine ⟨fun h => ?_, fun a mm h => ?_⟩
  · simp only [MState.mem0, hinst] at h ⊢
    cases ha : m.frame.inst.mems[0]? with
    | none => rfl
    | some a =>
      simp only [ha] at h
      cases hm : m.store.mems[a]? with
      | none => simp [hnone a hm]
      | some mm => simp [hm] at h
  · simp only [MState.mem0, hinst] at h ⊢
    cases ha : m.frame.inst.mems[0]? with
    | none => simp [ha] at h
    | some a' =>
      simp only [ha, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨mm', hm', rfl, rfl⟩ := h
      obtain ⟨mmP, hP1, hrest⟩ := hsome a' mm' hm'
      exact ⟨mmP, by simp [hP1], hrest⟩

/-- `load` (unpacked): the read range holds no live byte (`memRead`), so `P` reads the same
value; a bounds failure traps alike (equal pages). -/
theorem step_put_load {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {t : NumType} {ma : MemArg} {rest : List AInstr} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems)
    (hc : m.code = .plain (.load t ma) :: rest) (hsup : ∀ t ∈ ts, t.1 ∈ ps)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  obtain ⟨hn0, hs0⟩ := mem0_eqv hP hinv hok
  rcases hs : m.stack with _ | ⟨v, stk⟩
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  cases v
  case i32 i =>
    cases hm : m.mem0 with
    | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm] at h
    | some am =>
      obtain ⟨a, mm⟩ := am
      obtain ⟨mmP, hPm0, hpg, -, -, hby⟩ := hs0 a mm hm
      have hsize : mmP.size = mm.size := by simp only [MMem.size, hpg]
      simp only [tstep, hc, Ref.toVal, plainMap, hs, memRead, hm] at hF
      simp only [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, Option.map_some,
        Option.some.injEq] at h
      subst h
      cases hb : Nat.blt mm.size (i.toNat + ma.offset + t.bytes)
      · simp only [hb, Bool.cond_false] at hF ⊢
        cases hh : hitBytes ps a (i.toNat + ma.offset) t.bytes <;>
          simp only [hh, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
        subst hF
        have hrd : mmP.read (i.toNat + ma.offset) t.bytes = mm.read (i.toNat + ma.offset) t.bytes :=
          read_congr _ fun x h1 h2 => by
            rw [hby x, pbyte_nohit _ (noByte_of_hitBytes hsup hh x h1 h2)]
        refine ⟨P.cont (t.val (mm.read (i.toNat + ma.offset) t.bytes) :: stk) [] rest, ?_, ?_⟩
        · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
            Option.map_some, hsize, hb, Bool.cond_false, hrd]
        · rw [move_some, put_eq, eqv_iff]
          exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
      · simp only [hb, Bool.cond_true, Option.some.injEq] at hF ⊢
        subst hF
        refine ⟨P.cont stk [.trap] rest, ?_, ?_⟩
        · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
            Option.map_some, hsize, hb, Bool.cond_true]
        · rw [move_some, put_eq, eqv_iff]
          exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
  all_goals simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h

/-- `load` (packed): as `step_put_load` over `p.bits / 8` bytes. -/
theorem step_put_loadPacked {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {w : Width} {pk : PackSize} {sx : Sx} {ma : MemArg} {rest : List AInstr} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems)
    (hc : m.code = .plain (.loadPacked w pk sx ma) :: rest) (hsup : ∀ t ∈ ts, t.1 ∈ ps)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  obtain ⟨hn0, hs0⟩ := mem0_eqv hP hinv hok
  rcases hs : m.stack with _ | ⟨v, stk⟩
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  cases v
  case i32 i =>
    cases hm : m.mem0 with
    | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm] at h
    | some am =>
      obtain ⟨a, mm⟩ := am
      obtain ⟨mmP, hPm0, hpg, -, -, hby⟩ := hs0 a mm hm
      have hsize : mmP.size = mm.size := by simp only [MMem.size, hpg]
      simp only [tstep, hc, Ref.toVal, plainMap, hs, memRead, hm] at hF
      simp only [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, Option.map_some,
        Option.some.injEq] at h
      subst h
      cases hb : Nat.blt mm.size (i.toNat + ma.offset + (pk.bits / 8))
      · simp only [hb, Bool.cond_false] at hF ⊢
        cases hh : hitBytes ps a (i.toNat + ma.offset) (pk.bits / 8) <;>
          simp only [hh, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at hF
        subst hF
        have hrd : mmP.read (i.toNat + ma.offset) (pk.bits / 8) =
            mm.read (i.toNat + ma.offset) (pk.bits / 8) :=
          read_congr _ fun x h1 h2 => by
            rw [hby x, pbyte_nohit _ (noByte_of_hitBytes hsup hh x h1 h2)]
        refine ⟨P.cont (packedVal w pk.bits sx (mm.read (i.toNat + ma.offset) (pk.bits / 8)) :: stk)
          [] rest, ?_, ?_⟩
        · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
            Option.map_some, hsize, hb, Bool.cond_false, hrd]
        · rw [move_some, put_eq, eqv_iff]
          exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
      · simp only [hb, Bool.cond_true, Option.some.injEq] at hF ⊢
        subst hF
        refine ⟨P.cont stk [.trap] rest, ?_, ?_⟩
        · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
            Option.map_some, hsize, hb, Bool.cond_true]
        · rw [move_some, put_eq, eqv_iff]
          exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
  all_goals simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h

/-! ## Writes: the written range's patches die -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem killBytes_byte (mi ea n mi' x : Nat) :
    killBytes mi ea n (.byte mi' x) =
      if mi' = mi ∧ ea ≤ x ∧ x < ea + n then none else some (.byte mi' x) := by
  simp only [killBytes]
  by_cases h : mi' = mi ∧ ea ≤ x ∧ x < ea + n
  · obtain ⟨rfl, h1, h2⟩ := h; simp [h1, h2]
  · rw [ite_f h]
    have : (mi' == mi && decide (ea ≤ x) && decide (x < ea + n)) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      exact h ⟨hb.1.1, hb.1.2, hb.2⟩
    rw [this, Bool.cond_false]

theorem pbyte_kill {mi ea n mi' x : Nat} : ∀ (ts : List (Pos × TVal)) (o : Nat),
    pbyte (move (killBytes mi ea n) ts) mi' x o =
      if mi' = mi ∧ ea ≤ x ∧ x < ea + n then o else pbyte ts mi' x o
  | [], o => by simp [move, pbyte]
  | (p, v) :: ts, o => by
    rw [move_cons]
    have ih := pbyte_kill (mi := mi) (ea := ea) (n := n) (mi' := mi') (x := x) ts
    cases p with
    | byte mj a =>
      rw [killBytes_byte]
      by_cases hk : mj = mi ∧ ea ≤ a ∧ a < ea + n
      · rw [ite_t hk]
        simp only [Option.map_none, Option.toList_none, List.nil_append, ih]
        cases v with
        | byte b =>
          simp only [pbyte]
          by_cases hin : mi' = mi ∧ ea ≤ x ∧ x < ea + n
          · simp only [ite_t hin]
          · have : (mj == mi' && a == x) = false := by
              rw [Bool.eq_false_iff]
              intro hb
              simp only [Bool.and_eq_true, beq_iff_eq] at hb
              obtain ⟨h3, h4⟩ := hb
              exact hin ⟨h3 ▸ hk.1, h4 ▸ hk.2.1, h4 ▸ hk.2.2⟩
            simp only [ite_f hin, this, Bool.cond_false]
        | val w => simp only [pbyte]
      · rw [ite_f hk]
        simp only [Option.map_some, Option.toList_some, List.singleton_append]
        cases v with
        | byte b =>
          simp only [pbyte, ih]
          by_cases hin : mi' = mi ∧ ea ≤ x ∧ x < ea + n
          · have : (mj == mi' && a == x) = false := by
              rw [Bool.eq_false_iff]
              intro hb
              simp only [Bool.and_eq_true, beq_iff_eq] at hb
              obtain ⟨h3, h4⟩ := hb
              exact hk ⟨h3.trans hin.1, h4 ▸ hin.2.1, h4 ▸ hin.2.2⟩
            simp only [ite_t hin, this, Bool.cond_false]
          · simp only [ite_f hin]
        | val w => simp only [pbyte, ih]
    | top i => cases v <;> simp only [killBytes, Option.map_some, Option.toList_some,
        List.singleton_append, pbyte, ih]
    | loc k i => cases v <;> simp only [killBytes, Option.map_some, Option.toList_some,
        List.singleton_append, pbyte, ih]
    | saved k j => cases v <;> simp only [killBytes, Option.map_some, Option.toList_some,
        List.singleton_append, pbyte, ih]

theorem putLocals_move_kill (mi ea n : Nat) : ∀ (ts : List (Pos × TVal)) (L : List (Option Val)),
    putLocals (move (killBytes mi ea n) ts) L = putLocals ts L
  | [], _ => rfl
  | (p, v) :: ts, L => by
    rw [move_cons]
    have ih := putLocals_move_kill mi ea n ts
    cases p with
    | byte mj a =>
      rw [killBytes_byte]; split <;> cases v <;>
        simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
          List.nil_append, List.singleton_append, putLocals, ih]
    | _ => cases v <;> simp only [killBytes, Option.map_some, Option.toList_some,
        List.singleton_append, putLocals, ih]

theorem putCtl_move_kill (mi ea n : Nat) : ∀ (ts : List (Pos × TVal)) (ctl : List Ctl),
    putCtl (move (killBytes mi ea n) ts) ctl = putCtl ts ctl
  | [], _ => rfl
  | (p, v) :: ts, ctl => by
    rw [move_cons]
    have ih := putCtl_move_kill mi ea n ts
    cases p with
    | byte mj a =>
      rw [killBytes_byte]; split <;> cases v <;>
        simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
          List.nil_append, List.singleton_append, putCtl, ih]
    | _ => cases v <;> simp only [killBytes, Option.map_some, Option.toList_some,
        List.singleton_append, putCtl, ih]

theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ (i : Nat) a b, l₁[i]? = some a → l₂[i]? = some b → R a b) →
    List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, h => .cons (h 0 a b rfl rfl)
      (forall₂_of_getElem? (by simpa using hl) fun i a' b' h1 h2 => h (i + 1) a' b' h1 h2)
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- A write of memory `a` over `[ea, ea + n)` on both sides (bytes `B` there, the rest kept):
`P` stays alike the patched state once the written range's patches die. -/
theorem eqv_write {m P : MState} {ts : List (Pos × TVal)} {a ea n : Nat} {mm mmP w wP : MMem}
    (hP : Eqv P (put ts m)) (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems)
    (hm : m.store.mems[a]? = some mm) (hPm : P.store.mems[a]? = some mmP)
    (hw : w.pages = mm.pages ∧ w.max = mm.max ∧ w.depth = mm.depth ∧ w.Inv)
    (hwP : wP.pages = mmP.pages ∧ wP.max = mmP.max ∧ wP.depth = mmP.depth)
    (B : Nat → Nat)
    (hwb : ∀ x, w.byte x = if ea ≤ x ∧ x < ea + n then B x else mm.byte x)
    (hwPb : ∀ x, wP.byte x = if ea ≤ x ∧ x < ea + n then B x else mmP.byte x)
    (stk : List Val) (code : List AInstr) :
    Eqv { P with store := { P.store with mems := P.store.mems.set a wP }, stack := stk,
                 code := code }
      (put (move (killBytes a ea n) ts)
        { m with store := { m.store with mems := m.store.mems.set a w }, stack := stk,
                 code := code }) := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm', hPb, hPf, -, -, hPk⟩ := hP'
  obtain ⟨-, hsome⟩ := eqv_mem hP hinv hok
  obtain ⟨mmP', hPm2, hpg, hmx, hdp, hby⟩ := hsome a mm hm
  rw [hPm, Option.some.injEq] at hPm2
  subst hPm2
  have hinv' : ∀ x ∈ m.store.mems.set a w, x.Inv := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    by_cases hia : a = i
    · subst hia
      have hlt : a < m.store.mems.length := (List.getElem?_eq_some_iff.mp hm).1
      rw [List.getElem?_set_self hlt, Option.some.injEq] at hi
      subst hi; exact hw.2.2.2
    · rw [List.getElem?_set_ne hia] at hi
      exact hinv x (List.mem_of_getElem? hi)
  have hok' : BytesOK (move (killBytes a ea n) ts) (m.store.mems.set a w) := by
    intro mi x b ht
    simp only [move, List.mem_filterMap, Option.map_eq_some_iff] at ht
    obtain ⟨⟨p, v⟩, hmem, q, hq, hqv⟩ := ht
    simp only [Prod.mk.injEq] at hqv
    obtain ⟨rfl, rfl⟩ := hqv
    cases p with
    | byte mj y =>
      rw [killBytes_byte] at hq
      split at hq
      · simp at hq
      · simp only [Option.some.injEq, Pos.byte.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨hb, mm1, hmm1, hlt1⟩ := hok mj y b hmem
        refine ⟨hb, ?_⟩
        by_cases hja : a = mj
        · subst hja
          rw [hm, Option.some.injEq] at hmm1
          subst hmm1
          refine ⟨w, ?_, by simp only [MMem.size, hw.1]; exact hlt1⟩
          exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hm).1
        · exact ⟨mm1, by rw [List.getElem?_set_ne hja]; exact hmm1, hlt1⟩
    | top => simp [killBytes] at hq
    | loc => simp [killBytes] at hq
    | saved => simp [killBytes] at hq
  obtain ⟨-, hspec⟩ := putMems_spec _ _ hinv' hok'
  rw [put_eq, eqv_iff]
  refine ⟨?_, hPb, by simp only [hPf, putLocals_move_kill], rfl, rfl,
    by simp only [hPk, putCtl_move_kill]⟩
  apply forall₂_of_getElem?
  · simp only [List.length_set, length_putMems, hPm'.length_eq, length_putMems]
  · intro i x y hx hy
    by_cases hia : a = i
    · subst hia
      have hlt : a < m.store.mems.length := (List.getElem?_eq_some_iff.mp hm).1
      have hltP : a < P.store.mems.length := (List.getElem?_eq_some_iff.mp hPm).1
      rw [List.getElem?_set_self hltP, Option.some.injEq] at hx
      subst hx
      obtain ⟨y', hy', ypg, ymx, ydp, yby⟩ := hspec a w (List.getElem?_set_self hlt)
      rw [hy, Option.some.injEq] at hy'
      subst hy'
      refine ⟨by rw [hwP.1, ypg, hw.1, hpg], by rw [hwP.2.1, ymx, hw.2.1, hmx],
        by rw [hwP.2.2, ydp, hw.2.2.1, hdp], fun z => ?_⟩
      rw [hwPb z, yby z, pbyte_kill, hwb z]
      by_cases hz : ea ≤ z ∧ z < ea + n
      · simp only [hz, and_self, ↓reduceIte]
      · simp only [hz, ↓reduceIte, and_false, hby z]
    · rw [List.getElem?_set_ne hia] at hx
      have hmi : ∃ mmi, m.store.mems[i]? = some mmi := by
        have := hy
        rw [← Option.isSome_iff_exists]
        have hl : i < (putMems (move (killBytes a ea n) ts) (m.store.mems.set a w)).length :=
          (List.getElem?_eq_some_iff.mp hy).1
        rw [length_putMems, List.length_set] at hl
        simp [hl]
      obtain ⟨mmi, hmmi⟩ := hmi
      obtain ⟨y', hy', ypg, ymx, ydp, yby⟩ :=
        hspec i mmi (by rw [List.getElem?_set_ne hia]; exact hmmi)
      rw [hy, Option.some.injEq] at hy'
      subst hy'
      obtain ⟨x', hx', xpg, xmx, xdp, xby⟩ := hsome i mmi hmmi
      rw [hx, Option.some.injEq] at hx'
      subst hx'
      refine ⟨by rw [xpg, ypg], by rw [xmx, ymx], by rw [xdp, ydp], fun z => ?_⟩
      rw [xby z, yby z, pbyte_kill]
      have : ¬ (i = a ∧ ea ≤ z ∧ z < ea + n) := fun h => hia h.1.symm
      simp only [this, ↓reduceIte]

theorem reach_of_size {mm : MMem} (hi : mm.Inv) {k : Nat} (hk : k ≤ mm.size) :
    k ≤ 2 ^ (mm.depth + W) := Nat.le_trans hk hi.2.1

/-- `store` (unpacked): the written bytes' patches die (`memWrite`), a bounds failure traps. -/
theorem step_put_store {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {t : NumType} {ma : MemArg} {rest : List AInstr} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hPinv : ∀ mm ∈ P.store.mems, mm.Inv)
    (hok : BytesOK ts m.store.mems) (hc : m.code = .plain (.store t ma) :: rest)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  obtain ⟨-, hs0⟩ := mem0_eqv hP hinv hok
  rcases hs : m.stack with _ | ⟨v, _ | ⟨u, stk⟩⟩
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  cases u
  case i32 i =>
    cases hm : m.mem0 with
    | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm] at h
    | some am =>
      obtain ⟨a, mm⟩ := am
      obtain ⟨mmP, hPm0, hpg, hmx, hdp, hby⟩ := hs0 a mm hm
      have hsize : mmP.size = mm.size := by simp only [MMem.size, hpg]
      have hmm : m.store.mems[a]? = some mm := by
        simp only [MState.mem0] at hm
        split at hm
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hm
          obtain ⟨_, h1, rfl, rfl⟩ := hm; exact h1
        · simp at hm
      have hmmP : P.store.mems[a]? = some mmP := by
        simp only [MState.mem0] at hPm0
        split at hPm0
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hPm0
          obtain ⟨_, h1, rfl, rfl⟩ := hPm0; exact h1
        · simp at hPm0
      have hmi : mm.Inv := hinv mm (List.mem_of_getElem? hmm)
      have hmPi : mmP.Inv := hPinv mmP (List.mem_of_getElem? hmmP)
      simp only [tstep, hc, Ref.toVal, plainMap, hs, memWrite, hm] at hF
      cases hc' : v.numBits t with
      | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, hc'] at h
      | some c =>
        simp only [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, hc'] at h
        cases hb : Nat.blt mm.size (i.toNat + ma.offset + t.bytes)
        · simp only [hb, Bool.cond_false, Option.some.injEq] at hF h
          subst hF; subst h
          have hle : i.toNat + ma.offset + t.bytes ≤ mm.size := le_of_blt_false hb
          have hw := MMem.write_fields mm (i.toNat + ma.offset) t.bytes c
          have hwP := MMem.write_fields mmP (i.toNat + ma.offset) t.bytes c
          refine ⟨(P.setMem a (mmP.write (i.toNat + ma.offset) t.bytes c)).cont stk [] rest, ?_,
            eqv_write hP hinv hok hmm hmmP ⟨hw.1, hw.2.1, hw.2.2, MMem.write_inv hmi hle c⟩ hwP
              (fun x => c / 256 ^ (x - (i.toNat + ma.offset)) % 256)
              (fun x => MMem.byte_write hmi.1 (reach_of_size hmi hle) c x)
              (fun x => MMem.byte_write hmPi.1
                (by rw [hdp]; exact reach_of_size hmi hle) c x) stk ([] ++ rest)⟩
          simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0, hc',
            hsize, hb, Bool.cond_false]
        · simp only [hb, Bool.cond_true, Option.some.injEq] at hF h
          subst hF; subst h
          refine ⟨P.cont stk [.trap] rest, ?_, ?_⟩
          · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0, hc',
              hsize, hb, Bool.cond_true]
          · rw [move_some, put_eq, eqv_iff]
            exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
  all_goals simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h

/-- `store` (packed): as `step_put_store` over `p.bits / 8` bytes. -/
theorem step_put_storePacked {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {w : Width} {pk : PackSize} {ma : MemArg} {rest : List AInstr} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hPinv : ∀ mm ∈ P.store.mems, mm.Inv)
    (hok : BytesOK ts m.store.mems) (hc : m.code = .plain (.storePacked w pk ma) :: rest)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  obtain ⟨-, hs0⟩ := mem0_eqv hP hinv hok
  rcases hs : m.stack with _ | ⟨v, _ | ⟨u, stk⟩⟩
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  cases u
  case i32 i =>
    cases hm : m.mem0 with
    | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm] at h
    | some am =>
      obtain ⟨a, mm⟩ := am
      obtain ⟨mmP, hPm0, hpg, hmx, hdp, hby⟩ := hs0 a mm hm
      have hsize : mmP.size = mm.size := by simp only [MMem.size, hpg]
      have hmm : m.store.mems[a]? = some mm := by
        simp only [MState.mem0] at hm
        split at hm
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hm
          obtain ⟨_, h1, rfl, rfl⟩ := hm; exact h1
        · simp at hm
      have hmmP : P.store.mems[a]? = some mmP := by
        simp only [MState.mem0] at hPm0
        split at hPm0
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hPm0
          obtain ⟨_, h1, rfl, rfl⟩ := hPm0; exact h1
        · simp at hPm0
      have hmi : mm.Inv := hinv mm (List.mem_of_getElem? hmm)
      have hmPi : mmP.Inv := hPinv mmP (List.mem_of_getElem? hmmP)
      simp only [tstep, hc, Ref.toVal, plainMap, hs, memWrite, hm] at hF
      cases hc' : v.intBits w with
      | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, hc'] at h
      | some c =>
        simp only [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, hc'] at h
        cases hb : Nat.blt mm.size (i.toNat + ma.offset + (pk.bits / 8))
        · simp only [hb, Bool.cond_false, Option.some.injEq] at hF h
          subst hF; subst h
          have hle : i.toNat + ma.offset + (pk.bits / 8) ≤ mm.size := le_of_blt_false hb
          have hwf := MMem.write_fields mm (i.toNat + ma.offset) (pk.bits / 8) c
          have hwPf := MMem.write_fields mmP (i.toNat + ma.offset) (pk.bits / 8) c
          refine ⟨(P.setMem a (mmP.write (i.toNat + ma.offset) (pk.bits / 8) c)).cont stk [] rest,
            ?_,
            eqv_write hP hinv hok hmm hmmP ⟨hwf.1, hwf.2.1, hwf.2.2, MMem.write_inv hmi hle c⟩ hwPf
              (fun x => c / 256 ^ (x - (i.toNat + ma.offset)) % 256)
              (fun x => MMem.byte_write hmi.1 (reach_of_size hmi hle) c x)
              (fun x => MMem.byte_write hmPi.1
                (by rw [hdp]; exact reach_of_size hmi hle) c x) stk ([] ++ rest)⟩
          simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0, hc',
            hsize, hb, Bool.cond_false]
        · simp only [hb, Bool.cond_true, Option.some.injEq] at hF h
          subst hF; subst h
          refine ⟨P.cont stk [.trap] rest, ?_, ?_⟩
          · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0, hc',
              hsize, hb, Bool.cond_true]
          · rw [move_some, put_eq, eqv_iff]
            exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
  all_goals simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h

theorem move_killBytes_zero (mi d : Nat) : ∀ ts : List (Pos × TVal),
    move (killBytes mi d 0) ts = ts
  | [] => rfl
  | (p, v) :: ts => by
    rw [move_cons, move_killBytes_zero mi d ts]
    cases p with
    | byte mj x =>
      rw [killBytes_byte, ite_f (by omega)]
      rfl
    | _ => rfl

theorem fill_byte {mm : MMem} (hi : mm.Inv) {d n b : Nat} (hn : d + n ≤ mm.size) (hb : b < 256)
    (x : Nat) : (mm.fill d n b).byte x = if d ≤ x ∧ x < d + n then b else mm.byte x := by
  simp only [MMem.fill]
  rw [MMem.byte_writeBytes hi.1 (by simpa using reach_of_size hi hn)
    (fun c hc => by rw [List.eq_of_mem_replicate hc]; exact hb)]
  simp only [List.length_replicate]
  by_cases h : d ≤ x ∧ x < d + n
  · simp only [h, and_self, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [ite_t (by omega : x - d < n), Option.getD_some]
  · simp only [h, ↓reduceIte]

/-- `memory.fill`: a fill writes its range (its patches die), length 0 writes nothing, a bounds
failure traps. -/
theorem step_put_fill {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {rest : List AInstr} (hP : Eqv P (put ts m))
    (hinv : ∀ mm ∈ m.store.mems, mm.Inv) (hPinv : ∀ mm ∈ P.store.mems, mm.Inv)
    (hok : BytesOK ts m.store.mems) (hc : m.code = .plain .memoryFill :: rest)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP'
  obtain ⟨-, hs0⟩ := mem0_eqv hP hinv hok
  rcases hs : m.stack with _ | ⟨u, _ | ⟨v, _ | ⟨y, stk⟩⟩⟩
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  · simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h
  cases u <;> cases y
  case i32.i32 n d =>
    cases hm : m.mem0 with
    | none => simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm] at h
    | some am =>
      obtain ⟨a, mm⟩ := am
      obtain ⟨mmP, hPm0, hpg, hmx, hdp, hby⟩ := hs0 a mm hm
      have hsize : mmP.size = mm.size := by simp only [MMem.size, hpg]
      have hmm : m.store.mems[a]? = some mm := by
        simp only [MState.mem0] at hm
        split at hm
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hm
          obtain ⟨_, h1, rfl, rfl⟩ := hm; exact h1
        · simp at hm
      have hmmP : P.store.mems[a]? = some mmP := by
        simp only [MState.mem0] at hPm0
        split at hPm0
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hPm0
          obtain ⟨_, h1, rfl, rfl⟩ := hPm0; exact h1
        · simp at hPm0
      have hmi : mm.Inv := hinv mm (List.mem_of_getElem? hmm)
      have hmPi : mmP.Inv := hPinv mmP (List.mem_of_getElem? hmmP)
      simp only [tstep, hc, Ref.toVal, plainMap, hs, memWrite, hm] at hF
      simp only [MState.step, hc, hs, MState.stepPlain, Ref.toVal, hm, Option.bind_some] at h
      cases hb : Nat.blt mm.size (d.toNat + n.toNat)
      · simp only [hb, Bool.cond_false] at hF h
        have hle : d.toNat + n.toNat ≤ mm.size := le_of_blt_false hb
        cases hz : Nat.beq n.toNat 0
        · simp only [hz, Bool.cond_false, Option.map_eq_some_iff, Option.some.injEq] at h hF
          obtain ⟨c, hcv, rfl⟩ := h
          subst hF
          have hfb : c % 256 < 256 := Nat.mod_lt _ (by norm_num)
          have hwf := MMem.writeBytes_fields mm d.toNat (List.replicate n.toNat (c % 256))
          have hwPf := MMem.writeBytes_fields mmP d.toNat (List.replicate n.toNat (c % 256))
          refine ⟨(P.setMem a (mmP.fill d.toNat n.toNat (c % 256))).cont stk [] rest, ?_,
            eqv_write hP hinv hok hmm hmmP ⟨hwf.1, hwf.2.1, hwf.2.2,
              MMem.writeBytes_inv hmi (by simpa using hle)
                (fun b hb' => by rw [List.eq_of_mem_replicate hb']; exact hfb)⟩ hwPf
              (fun _ => c % 256) (fun x => fill_byte hmi hle hfb x)
              (fun x => fill_byte hmPi (by rw [hsize]; exact hle) hfb x) stk ([] ++ rest)⟩
          simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
            Option.bind_some, hsize, hb, Bool.cond_false, hz, hcv, Option.map_some]
        · simp only [hz, Bool.cond_true, Option.some.injEq] at h hF
          subst hF; subst h
          refine ⟨P.cont stk [] rest, ?_, ?_⟩
          · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
              Option.bind_some, hsize, hb, Bool.cond_false, hz, Bool.cond_true]
          · have hn0 : n.toNat = 0 := by simpa using hz
            rw [hn0, move_killBytes_zero, put_eq, eqv_iff]
            exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
      · simp only [hb, Bool.cond_true, Option.some.injEq] at hF h
        subst hF; subst h
        refine ⟨P.cont stk [.trap] rest, ?_, ?_⟩
        · simp only [MState.step, hPc, hc, hPs, hs, MState.stepPlain, Ref.toVal, hPm0,
            Option.bind_some, hsize, hb, Bool.cond_true]
        · rw [move_some, put_eq, eqv_iff]
          exact ⟨hPm, hPb, hPf, rfl, rfl, hPk⟩
  all_goals simp [MState.step, hc, hs, MState.stepPlain, Ref.toVal, Ref.instrStep] at h

/-! ## The host call (`environ_sizes_get`, contract F1 `host_put`) -/

theorem eqv_cont {m P : MState} {ts : List (Pos × TVal)} (h : Eqv P (put ts m))
    (stk : List Val) (code : List AInstr) :
    Eqv { P with stack := stk, code := code } (put ts { m with stack := stk, code := code }) := by
  rw [put_eq, eqv_iff] at h ⊢
  obtain ⟨h1, h2, h3, -, -, h6⟩ := h
  exact ⟨h1, h2, h3, rfl, rfl, h6⟩

/-- `hostMap`'s position map for writes `ws` into memory `mem`. -/
def killAll (mem : Nat) (ws : List (Nat × FVA.Wasi.Bytes)) : PMap := fun p =>
  ws.foldl (fun q w => q.bind (killBytes mem w.1 w.2.length)) (some p)

theorem foldl_bind_kill (mem : Nat) : ∀ (ws : List (Nat × FVA.Wasi.Bytes)) (o : Option Pos),
    ws.foldl (fun q w => q.bind (killBytes mem w.1 w.2.length)) o = o.bind (killAll mem ws)
  | [], none => rfl
  | [], some _ => rfl
  | w :: ws, o => by
    simp only [List.foldl_cons]
    rw [foldl_bind_kill mem ws]
    cases o with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, killAll, List.foldl_cons]
      rw [foldl_bind_kill mem ws]

theorem move_killAll_cons (mem : Nat) (w : Nat × FVA.Wasi.Bytes) (ws : List (Nat × FVA.Wasi.Bytes))
    (ts : List (Pos × TVal)) :
    move (killAll mem (w :: ws)) ts =
      move (killAll mem ws) (move (killBytes mem w.1 w.2.length) ts) := by
  rw [move_move]
  congr 1
  funext p
  simp only [killAll, List.foldl_cons, Option.bind_some]
  exact foldl_bind_kill mem ws _

theorem killAll_nil (mem : Nat) : killAll mem [] = some := rfl

theorem writeBytes_byteSpec {mm : MMem} (hi : mm.Inv) {d : Nat} {bs : List UInt8}
    (hn : d + bs.length ≤ mm.size) (x : Nat) :
    (mm.writeBytes d (bs.map UInt8.toNat)).byte x =
      if d ≤ x ∧ x < d + bs.length then (bs.map UInt8.toNat).getD (x - d) 0 else mm.byte x := by
  rw [MMem.byte_writeBytes hi.1 (by simpa using reach_of_size hi hn)
    (fun b hb => by
      simp only [List.mem_map] at hb
      obtain ⟨u, -, rfl⟩ := hb
      exact u.toNat_lt)]
  simp only [List.length_map]

theorem set_self_of_getElem? {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a →
    l.set i a = l
  | _ :: _, 0, _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
  | _ :: xs, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h; simp [set_self_of_getElem? (l := xs) h]
  | [], _, _, h => by simp at h

theorem inv_set {ms : List MMem} (h : ∀ x ∈ ms, x.Inv) {a : Nat} {w : MMem} (hw : w.Inv) :
    ∀ x ∈ ms.set a w, x.Inv := by
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  by_cases hia : a = i
  · subst hia
    have hlt : a < ms.length := by simpa using (List.getElem?_eq_some_iff.mp hi).1
    rw [List.getElem?_set_self hlt, Option.some.injEq] at hi
    subst hi; exact hw
  · rw [List.getElem?_set_ne hia] at hi
    exact h x (List.mem_of_getElem? hi)

theorem bytesOK_set_kill {ts : List (Pos × TVal)} {ms : List MMem} (hok : BytesOK ts ms)
    {a ea n : Nat} {mm w : MMem} (hm : ms[a]? = some mm) (hp : w.pages = mm.pages) :
    BytesOK (move (killBytes a ea n) ts) (ms.set a w) := by
  intro mi x b ht
  simp only [move, List.mem_filterMap, Option.map_eq_some_iff] at ht
  obtain ⟨⟨p, v⟩, hmem, q, hq, hqv⟩ := ht
  simp only [Prod.mk.injEq] at hqv
  obtain ⟨rfl, rfl⟩ := hqv
  cases p with
  | byte mj y =>
    rw [killBytes_byte] at hq
    split at hq
    · simp at hq
    · simp only [Option.some.injEq, Pos.byte.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨hb, mm1, hmm1, hlt1⟩ := hok mj y b hmem
      refine ⟨hb, ?_⟩
      by_cases hja : a = mj
      · subst hja
        rw [hm, Option.some.injEq] at hmm1
        subst hmm1
        exact ⟨w, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hm).1,
          by simp only [MMem.size, hp]; exact hlt1⟩
      · exact ⟨mm1, by rw [List.getElem?_set_ne hja]; exact hmm1, hlt1⟩
  | top => simp [killBytes] at hq
  | loc => simp [killBytes] at hq
  | saved => simp [killBytes] at hq

theorem eqv_writeAll {mem : Nat} : ∀ (ws : List (Nat × FVA.Wasi.Bytes)) {m P : MState}
    {ts : List (Pos × TVal)} {mm mmP : MMem},
    Eqv P (put ts m) → (∀ x ∈ m.store.mems, x.Inv) → (∀ x ∈ P.store.mems, x.Inv) →
    BytesOK ts m.store.mems → m.store.mems[mem]? = some mm → P.store.mems[mem]? = some mmP →
    (∀ w ∈ ws, w.1 + w.2.length ≤ mm.size) →
    Eqv { P with store := { P.store with mems := P.store.mems.set mem (FVA.Wasi.writeAll mmP ws) } }
      (put (move (killAll mem ws) ts)
        { m with store := { m.store with mems := m.store.mems.set mem (FVA.Wasi.writeAll mm ws) } })
  | [], m, P, ts, mm, mmP, hP, _, _, _, hm, hPm, _ => by
    simp only [FVA.Wasi.writeAll, List.foldl_nil, killAll_nil, move_some]
    rw [set_self_of_getElem? hm, set_self_of_getElem? hPm]
    exact hP
  | w :: ws, m, ⟨⟨Pb, Pm⟩, Pf, Ps, Pc, Pk⟩, ts, mm, mmP, hP, hinv, hPinv, hok, hm, hPm, hws => by
    have hP' := hP
    rw [put_eq, eqv_iff] at hP'
    obtain ⟨-, -, -, hPs, hPc, -⟩ := hP'
    simp only at hPs hPc
    subst hPs hPc
    have hw0 : w.1 + w.2.length ≤ mm.size := hws w List.mem_cons_self
    have hmi : mm.Inv := hinv mm (List.mem_of_getElem? hm)
    have hmPi : mmP.Inv := hPinv mmP (List.mem_of_getElem? hPm)
    obtain ⟨-, hs⟩ := eqv_mem hP hinv hok
    obtain ⟨mmP', hPm2, hpg, -, -, -⟩ := hs mem mm hm
    rw [hPm, Option.some.injEq] at hPm2
    subst hPm2
    have hsz : mmP.size = mm.size := by simp only [MMem.size, hpg]
    have hf1 := MMem.writeBytes_fields mm w.1 (w.2.map UInt8.toNat)
    have hfP1 := MMem.writeBytes_fields mmP w.1 (w.2.map UInt8.toNat)
    have hbytes : ∀ b ∈ w.2.map UInt8.toNat, b < 256 := fun b hb => by
      simp only [List.mem_map] at hb
      obtain ⟨u, -, rfl⟩ := hb
      exact u.toNat_lt
    have hinv1 := MMem.writeBytes_inv hmi (by simpa using hw0) hbytes
    have hinvP1 := MMem.writeBytes_inv hmPi (by simpa [hsz] using hw0) hbytes
    have hE := eqv_write hP hinv hok hm hPm ⟨hf1.1, hf1.2.1, hf1.2.2, hinv1⟩ hfP1
      (fun x => (w.2.map UInt8.toNat).getD (x - w.1) 0) (writeBytes_byteSpec hmi hw0)
      (writeBytes_byteSpec hmPi (by rw [hsz]; exact hw0)) m.stack m.code
    have hlt : mem < m.store.mems.length := (List.getElem?_eq_some_iff.mp hm).1
    have hltP : mem < Pm.length := (List.getElem?_eq_some_iff.mp hPm).1
    have ih := eqv_writeAll ws hE (inv_set hinv hinv1) (inv_set hPinv hinvP1)
      (bytesOK_set_kill hok hm hf1.1) (List.getElem?_set_self hlt) (List.getElem?_set_self hltP)
      (fun w' hw' => by
        simp only [MMem.size, hf1.1]
        exact hws w' (List.mem_cons_of_mem _ hw'))
    simp only [List.set_set] at ih
    rw [move_killAll_cons]
    exact ih

theorem inProfile_env (σ : FVA.Wasi.State) {s₁ s₂ : Store} (mem : Nat) (vs : List Val)
    (h : (s₁.mems[mem]?).map MemInst.size = (s₂.mems[mem]?).map MemInst.size) :
    FVA.Wasi.inProfile σ .environSizesGet s₁ mem vs =
      FVA.Wasi.inProfile σ .environSizesGet s₂ mem vs := by
  simp only [FVA.Wasi.inProfile]
  cases h1 : s₁.mems[mem]? <;> cases h2 : s₂.mems[mem]? <;> simp only [h1, h2, Option.map_none,
    Option.map_some, reduceCtorEq, Option.some.injEq] at h ⊢
  cases ha : FVA.Wasi.Call.environSizesGet.args vs with
  | none => rfl
  | some a => simp only [FVA.Wasi.Call.regions, h]

theorem decode_env (m₁ m₂ : MemInst) (a : List Nat) :
    FVA.Wasi.decode .environSizesGet m₁ a = FVA.Wasi.decode .environSizesGet m₂ a := by
  simp [FVA.Wasi.decode]

theorem hostCall_eqv {m P : MState} {ts : List (Pos × TVal)} (hP : Eqv P (put ts m)) :
    P.hostCall = m.hostCall := by
  rw [put_eq, eqv_iff] at hP
  obtain ⟨-, hPb, -, hPs, hPc, -⟩ := hP
  have hfuncs : P.store.base.funcs = m.store.base.funcs := by simpa using congrArg Store.funcs hPb
  simp only [MState.hostCall, hPc, hPs, hfuncs]

/-- `host_put` (contract F1): the host call `hostMap` admits (`environ_sizes_get`) answers `P`
alike — same world, same result — its writes killing their patches. -/
theorem host_put {md : Module} {mem : Nat} {σ τ : FVA.Wasi.State} {m P : MState}
    {ts : List (Pos × TVal)} {id k : Nat} {rest : List AInstr} {f : PMap} {ms' : MStore}
    {r : MHostOut} (hP : Eqv P (put ts m)) (hinv : ∀ mm ∈ m.store.mems, mm.Inv)
    (hPinv : ∀ mm ∈ P.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems)
    (hf : hostMap md mem σ id m.store ((m.stack.take k).reverse) = some f)
    (hh : FVA.Wasi.wasiHost md mem none σ id m.store ((m.stack.take k).reverse) =
      some (τ, ms', r)) :
    ∃ msP, FVA.Wasi.wasiHost md mem none σ id P.store ((P.stack.take k).reverse) =
        some (τ, msP, r) ∧
      Eqv (P.hostResume msP r.out rest k) (put (move f ts) (m.hostResume ms' r.out rest k)) := by
  have hP' := hP
  rw [put_eq, eqv_iff] at hP'
  obtain ⟨-, -, -, hPs, -, -⟩ := hP'
  simp only at hPs
  rw [hPs]
  set vs := (m.stack.take k).reverse with hvs
  cases hc : FVA.Wasi.bind md id with
  | none => simp [hostMap, hc] at hf
  | some c =>
    by_cases hce : c = .environSizesGet
    swap
    · simp [hostMap, hc, hce] at hf
    subst hce
    cases hmm : m.store.mems[mem]? with
    | none => simp [hostMap, hc, hmm] at hf
    | some mm =>
      obtain ⟨-, hs⟩ := eqv_mem hP hinv hok
      obtain ⟨mmP, hPmm, hpg, -, -, -⟩ := hs mem mm hmm
      have hsz : mmP.size = mm.size := by simp only [MMem.size, hpg]
      have hmabs : (m.store.abs.mems[mem]?).map MemInst.size = some mm.size := by
        simp [MStore.abs, hmm, abs_size]
      have hPabs : (P.store.abs.mems[mem]?).map MemInst.size = some mm.size := by
        simp [MStore.abs, hPmm, abs_size, hsz]
      have hinP := inProfile_env σ (s₁ := P.store.abs) (s₂ := m.store.abs) mem vs
        (by rw [hmabs, hPabs])
      cases ha : FVA.Wasi.Call.environSizesGet.args vs with
      | none => simp [hostMap, hc, hmm, ha] at hf
      | some a =>
        cases hin : FVA.Wasi.inProfile σ .environSizesGet m.store.abs mem vs with
        | false => simp [hostMap, hc, hmm, ha, hin] at hf
        | true =>
          rw [hin] at hinP
          have hdec := decode_env mmP.abs mm.abs a
          cases hst : FVA.Wasi.step σ (FVA.Wasi.decode .environSizesGet mm.abs a)
              { bytes := [] } with
          | mk τ' resp =>
            cases resp with
            | ok ws =>
              simp [hostMap, hc, hmm, ha, hin, hst] at hf
              subst hf
              cases hbnd : ws.all (fun w => decide (w.1 + w.2.length ≤ mm.size))
              · simp [FVA.Wasi.wasiHost, hc, hmm, ha, hin, FVA.Wasi.callBytes, hst, hbnd] at hh
              simp [FVA.Wasi.wasiHost, hc, hmm, ha, hin, FVA.Wasi.callBytes, hst, hbnd] at hh
              obtain ⟨rfl, rfl, rfl⟩ := hh
              have hb : ∀ w ∈ ws, w.1 + w.2.length ≤ mm.size := fun w hw =>
                of_decide_eq_true (List.all_eq_true.mp hbnd w hw)
              have hbndP : ws.all (fun w => decide (w.1 + w.2.length ≤ mmP.size)) = true := by
                rw [hsz]; exact hbnd
              refine ⟨{ P.store with mems := P.store.mems.set mem (FVA.Wasi.writeAll mmP ws) },
                ?_, ?_⟩
              · simp [FVA.Wasi.wasiHost, hc, hPmm, ha, hinP, FVA.Wasi.callBytes, hdec, hst, hbndP]
              · have hE := eqv_writeAll ws hP hinv hPinv hok hmm hPmm hb
                simp only [MState.hostResume, hPs]
                exact eqv_cont hE _ _
            | err e =>
              simp [hostMap, hc, hmm, ha, hin, hst] at hf
              subst hf
              simp [FVA.Wasi.wasiHost, hc, hmm, ha, hin, FVA.Wasi.callBytes, hst] at hh
              obtain ⟨rfl, rfl, rfl⟩ := hh
              refine ⟨P.store, ?_, ?_⟩
              · simp [FVA.Wasi.wasiHost, hc, hPmm, ha, hinP, FVA.Wasi.callBytes, hdec, hst]
              · rw [move_some]
                simp only [MState.hostResume, hPs]
                exact eqv_cont hP _ _
            | exit x =>
              simp [hostMap, hc, hmm, ha, hin, hst] at hf
              subst hf
              simp [FVA.Wasi.wasiHost, hc, hmm, ha, hin, FVA.Wasi.callBytes, hst] at hh
              obtain ⟨rfl, rfl, rfl⟩ := hh
              refine ⟨P.store, ?_, ?_⟩
              · simp [FVA.Wasi.wasiHost, hc, hPmm, ha, hinP, FVA.Wasi.callBytes, hdec, hst]
              · rw [move_some]
                simp only [MState.hostResume, hPs]
                exact eqv_cont hP _ _

/-! ## One step (contract F1 `step_put`) -/

theorem tstep_invoke {ps : List Pos} {m : MState} {a : Nat} {rest : List AInstr} {F : PMap}
    (hc : m.code = .invoke a :: rest) (hF : tstep ps m = some F) : F = invMap m.ctl.length := by
  simp only [tstep, hc, Ref.toVal] at hF
  split at hF
  · simp only [Option.some.injEq] at hF
    subst hF
    funext p
    cases p <;> rfl
  · simp at hF

/-- `step_put` (contract F1): every step the checker admits, from any state alike the patched one,
steps alike the patched successor (the patches moved by the step's map). -/
theorem step_put {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    (hP : Eqv P (put ts m)) (hinv : ∀ mm ∈ m.store.mems, mm.Inv)
    (hPinv : ∀ mm ∈ P.store.mems, mm.Inv) (hok : BytesOK ts m.store.mems)
    (hb : CtlBound ts m.ctl.length) (hsup : ∀ t ∈ ts, t.1 ∈ ps)
    (hF : tstep ps m = some F) (h : m.step = some m') :
    ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  cases hc : m.code with
  | nil => exact step_put_exit hP hc hsup hb hF h
  | cons e rest =>
    cases hv : Ref.toVal e with
    | some v =>
      have hF1 : F = some := by
        simp only [tstep, hc, hv, Option.some.injEq] at hF; exact hF.symm
      subst hF1
      rw [move_some]
      exact step_put_val hP hc hv h
    | none =>
      cases e
      case plain i =>
        have hpm : plainMap ps m i rest = some F := by simpa only [tstep, hc, hv] using hF
        by_cases hg : Generic i = true
        · rw [plainMap_generic _ _ _ hg] at hpm
          exact step_put_generic hP hc hg hsup hpm h
        · cases i
          case block bt body =>
            have hF1 : F = some := by simp only [plainMap, Option.some.injEq] at hpm; exact hpm.symm
            subst hF1; rw [move_some]; exact step_put_enter hP hc rfl hb h
          case loop bt body =>
            have hF1 : F = some := by simp only [plainMap, Option.some.injEq] at hpm; exact hpm.symm
            subst hF1; rw [move_some]; exact step_put_enter hP hc rfl hb h
          case tryTable bt cs body =>
            have hF1 : F = some := by simp only [plainMap, Option.some.injEq] at hpm; exact hpm.symm
            subst hF1; rw [move_some]; exact step_put_enter hP hc rfl hb h
          case br l => exact step_put_br hP hc hsup hb hF h
          case return_ => exact step_put_return hP hc hsup hb hF h
          case load t ma => exact step_put_load hP hinv hok hc hsup hF h
          case loadPacked w pk sx ma => exact step_put_loadPacked hP hinv hok hc hsup hF h
          case store t ma => exact step_put_store hP hinv hPinv hok hc hF h
          case storePacked w pk ma => exact step_put_storePacked hP hinv hPinv hok hc hF h
          case memoryFill => exact step_put_fill hP hinv hPinv hok hc hF h
          case throwRef =>
            rcases hs : m.stack with _ | ⟨u, stk⟩
            · simp [plainMap, hs, Generic] at hpm
            · cases u
              case ref r =>
                cases r
                case exn a =>
                  cases hb2 : (stk.isEmpty && rest.isEmpty)
                  · have hF1 : F = some := by
                      simp only [plainMap, hs, hb2, Bool.cond_false, Option.some.injEq] at hpm
                      exact hpm.symm
                    subst hF1; rw [move_some]
                    exact step_put_throwAdmin hP hc hs hb2 h
                  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hb2
                    obtain ⟨rfl, rfl⟩ := hb2
                    exact step_put_throw hP hc hs hsup hb hF h
                all_goals simp [plainMap, hs, Generic] at hpm
              all_goals simp [plainMap, hs, Generic] at hpm
          all_goals first
            | (simp [Generic] at hg; done)
            | (exfalso; simp [plainMap, Generic] at hpm)
      case invoke a =>
        have hF1 := tstep_invoke hc hF
        subst hF1
        exact step_put_invoke hP hc hb h
      all_goals first
        | (simp [Ref.toVal] at hv; done)
        | (simp [tstep, hc, hv] at hF)

end FVA.Wasm.Exec.Machine.Oblivious
