import FVA.Proof.Exec.Det

/-!
# Choice points in context: host calls (U14 S4)

`walk` and `runDet` stop at a host invoke: its successors are the outcomes the host relation
allows, never one fixed state. `seqFocus P` says the redex `seq` reaches (after the values before
it, through labels and frames) satisfies `P`; `seqPlug k out` replaces that redex and its top `k`
operands by `out`. `step_focus_host`: every step from a configuration whose focus is a host invoke
keeps the frame and is the plug of a returned, trapped or diverged host outcome, so a proof
quantifies over every allowed outcome at the call (`must_host_focus`).
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

mutual
/-- The redex `seq` reaches in `es` after the values `vs` (top first) satisfies `P`. -/
def seqFocus (P : List Val → AInstr → Prop) : List Val → List AInstr → Prop
  | _, [] => False
  | vs, e :: rest => match toVal e with
    | some v => seqFocus P (v :: vs) rest
    | none => atFocus P vs e

/-- The redex at the non-value `e` (values `vs` before it) satisfies `P`. -/
def atFocus (P : List Val → AInstr → Prop) (vs : List Val) : AInstr → Prop
  | .label _ _ body => seqFocus P [] body
  | .frame _ _ body => seqFocus P [] body
  | e => P vs e
end

mutual
/-- `es` (values `vs` before it, top first) with its focus redex and that redex's top `k`
operands replaced by `out`. -/
def seqPlug (k : Nat) (out : List AInstr) : List Val → List AInstr → List AInstr
  | vs, [] => vals vs.reverse
  | vs, e :: rest => match toVal e with
    | some v => seqPlug k out (v :: vs) rest
    | none => atPlug k out vs e rest

/-- `atPlug` at the non-value `e`: descend into a label or frame, else replace the redex. -/
def atPlug (k : Nat) (out : List AInstr) (vs : List Val) (e : AInstr) (rest : List AInstr) :
    List AInstr :=
  match e with
  | .label n cont body => vals vs.reverse ++ [.label n cont (seqPlug k out [] body)] ++ rest
  | .frame n fi body => vals vs.reverse ++ [.frame n fi (seqPlug k out [] body)] ++ rest
  | _ => vals (vs.drop k).reverse ++ out ++ rest
end

theorem seqFocus_vals (P : List Val → AInstr → Prop) (stk vs : List Val) (es : List AInstr) :
    seqFocus P stk (vals vs ++ es) = seqFocus P (vs.reverse ++ stk) es := by
  induction vs generalizing stk with
  | nil => simp [vals]
  | cons v vs ih =>
    simp only [vals, List.map_cons, List.cons_append, seqFocus, toVal_instr, List.reverse_cons,
      List.append_assoc]
    exact ih (v :: stk)

theorem seqPlug_vals (k : Nat) (out : List AInstr) (stk vs : List Val) (es : List AInstr) :
    seqPlug k out stk (vals vs ++ es) = seqPlug k out (vs.reverse ++ stk) es := by
  induction vs generalizing stk with
  | nil => simp [vals]
  | cons v vs ih =>
    simp only [vals, List.map_cons, List.cons_append, seqPlug, toVal_instr, List.reverse_cons,
      List.append_assoc]
    exact ih (v :: stk)

/-- A sequence of values has no focus. -/
theorem not_seqFocus_vals {P : List Val → AInstr → Prop} (stk vs : List Val) :
    ¬ seqFocus P stk (vals vs) := by
  have h := seqFocus_vals P stk vs []
  rw [List.append_nil] at h
  rw [h]
  simp [seqFocus]

/-- The focus of a host invoke of address `a` with arguments `args` (bottom first): the redex is
`invoke a`, the `m` values below it are `args`. -/
def HostAt (a m : Nat) (args : List Val) (vs : List Val) (e : AInstr) : Prop :=
  e = .invoke a ∧ m ≤ vs.length ∧ (vs.take m).reverse = args

/-- The focus of a filled evaluation context is its pending trap. -/
theorem seqFocus_eval_trap {P : List Val → AInstr → Prop} (hP : ∀ vs, ¬ P vs .trap)
    (E : EvalCtx) : ∀ stk rest, ¬ seqFocus P stk (E.fill [.trap] ++ rest) := by
  induction E with
  | hole =>
    intro stk rest h
    simp only [EvalCtx.fill, List.singleton_append, seqFocus, toVal, atFocus] at h
    exact hP _ h
  | seq vs inner rest₀ ih =>
    intro stk rest h
    simp only [EvalCtx.fill, List.append_assoc, seqFocus_vals] at h
    exact ih _ _ h
  | label n cont inner ih =>
    intro stk rest h
    simp only [EvalCtx.fill, List.singleton_append, seqFocus, toVal, atFocus] at h
    exact ih [] [] (by simpa only [List.append_nil] using h)

/-- The focus of a filled block context is the non-value `x` it surrounds (for `x` neither a
label nor a frame). -/
theorem seqFocus_block {P : List Val → AInstr → Prop} {x : AInstr} (hx : toVal x = none)
    (hl : ∀ n cont body, x ≠ .label n cont body) (hfr : ∀ n fi body, x ≠ .frame n fi body)
    {k : Nat} (L : BlockCtx k) (vs : List Val) :
    ∀ stk rest, seqFocus P stk (L.fill (vals vs ++ [x]) ++ rest) → ∃ st, P st x := by
  have hat : ∀ st, atFocus P st x = P st x := by
    intro st
    cases x with
    | label n cont body => exact absurd rfl (hl n cont body)
    | frame n fi body => exact absurd rfl (hfr n fi body)
    | _ => rfl
  induction L with
  | base vs₀ rest₀ =>
    intro stk rest h
    simp only [BlockCtx.fill, List.append_assoc, seqFocus_vals,
      List.cons_append, seqFocus, hx, hat] at h
    exact ⟨_, h⟩
  | label vs₀ n cont inner rest₀ ih =>
    intro stk rest h
    simp only [BlockCtx.fill, List.append_assoc, seqFocus_vals,
      List.cons_append, seqFocus, toVal, atFocus] at h
    exact ih [] [] (by simpa only [List.append_nil] using h)

set_option maxHeartbeats 1000000 in
/-- Every step from a configuration whose focus is the host invoke of `a` (host function `id` of
type `ft`, arguments `args`) keeps the frame and replaces that redex and its operands by a
returned, trapped or diverged outcome of `H id`. -/
theorem step_focus_host {H : HostSem} {c c' : Config} (h : Step H c c') {a id : Nat}
    {ft : FuncType} {args : List Val} (hf : c.store.funcs[a]? = some (.host ft id)) :
    ∀ (stk : List Val) (rest : List AInstr),
      seqFocus (HostAt a ft.params.length args) stk (c.instrs ++ rest) →
      c'.frame = c.frame ∧
      ((∃ res, H id c.store args (.returned c'.store res) ∧
          vals stk.reverse ++ c'.instrs ++ rest =
            seqPlug ft.params.length (vals res) stk (c.instrs ++ rest)) ∨
        (H id c.store args (.trapped c'.store) ∧
          vals stk.reverse ++ c'.instrs ++ rest =
            seqPlug ft.params.length [.trap] stk (c.instrs ++ rest)) ∨
        (H id c.store args .diverged ∧ c' = c)) := by
  have hnot : ∀ (i : Instr) st, ¬ HostAt a ft.params.length args st (.plain i) := by
    intro i st hh; cases hh.1
  induction h
  all_goals intro stk rest hfoc
  case invokeHost s s' f a' ft' id' vs res hf' hlen hH =>
    simp only [List.append_assoc, seqFocus_vals, List.singleton_append, seqFocus, toVal,
      atFocus, HostAt, AInstr.invoke.injEq] at hfoc
    obtain ⟨rfl, -, hargs⟩ := hfoc
    simp only [hf, Option.some.injEq, FuncInst.host.injEq] at hf'
    obtain ⟨rfl, rfl⟩ := hf'
    have hv : ((vs.reverse ++ stk).take ft.params.length).reverse = vs := by
      rw [← hlen, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp), List.reverse_reverse]
    rw [hv] at hargs
    subst hargs
    refine ⟨rfl, Or.inl ⟨res, hH, ?_⟩⟩
    simp only [List.append_assoc, seqPlug_vals, List.singleton_append, seqPlug, toVal, atPlug]
    rw [← hlen, List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp),
      List.nil_append]
  case invokeHostTrap s s' f a' ft' id' vs hf' hlen hH =>
    simp only [List.append_assoc, seqFocus_vals, List.singleton_append, seqFocus, toVal,
      atFocus, HostAt, AInstr.invoke.injEq] at hfoc
    obtain ⟨rfl, -, hargs⟩ := hfoc
    simp only [hf, Option.some.injEq, FuncInst.host.injEq] at hf'
    obtain ⟨rfl, rfl⟩ := hf'
    have hv : ((vs.reverse ++ stk).take ft.params.length).reverse = vs := by
      rw [← hlen, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp), List.reverse_reverse]
    rw [hv] at hargs
    subst hargs
    refine ⟨rfl, Or.inr (Or.inl ⟨hH, ?_⟩)⟩
    simp only [List.append_assoc, seqPlug_vals, List.singleton_append, seqPlug, toVal, atPlug]
    rw [← hlen, List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp),
      List.nil_append]
  case invokeHostDiverge s f a' ft' id' vs hf' hlen hH =>
    simp only [List.append_assoc, seqFocus_vals, List.singleton_append, seqFocus, toVal,
      atFocus, HostAt, AInstr.invoke.injEq] at hfoc
    obtain ⟨rfl, -, hargs⟩ := hfoc
    simp only [hf, Option.some.injEq, FuncInst.host.injEq] at hf'
    obtain ⟨rfl, rfl⟩ := hf'
    have hv : ((vs.reverse ++ stk).take ft.params.length).reverse = vs := by
      rw [← hlen, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp), List.reverse_reverse]
    rw [hv] at hargs
    subst hargs
    exact ⟨rfl, Or.inr (Or.inr ⟨hH, rfl⟩)⟩
  case invoke s f a' ft' inst code vs hf' hlen =>
    simp only [List.append_assoc, seqFocus_vals, List.singleton_append, seqFocus, toVal,
      atFocus, HostAt, AInstr.invoke.injEq] at hfoc
    obtain ⟨rfl, -⟩ := hfoc
    simp [hf] at hf'
  case seq s f s' f' es es' vs tail hs ih =>
    simp only [List.append_assoc, seqFocus_vals] at hfoc
    obtain ⟨hfr, hc⟩ := ih hf (vs.reverse ++ stk) (tail ++ rest) hfoc
    refine ⟨hfr, ?_⟩
    simp only [List.append_assoc, seqPlug_vals, List.reverse_append, List.reverse_reverse,
      vals, List.map_append] at hc ⊢
    rcases hc with ⟨res, hH, he⟩ | ⟨hH, he⟩ | ⟨hH, he⟩
    · exact Or.inl ⟨res, hH, by simpa only [List.append_assoc] using he⟩
    · exact Or.inr (Or.inl ⟨hH, by simpa only [List.append_assoc] using he⟩)
    · simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr (Or.inr ⟨hH, rfl⟩)
  case label s f s' f' n cont es es' hs ih =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨hfr, hc⟩ := ih hf [] [] (by simpa only [List.append_nil] using hfoc)
    refine ⟨hfr, ?_⟩
    simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at hc
    rcases hc with ⟨res, hH, he⟩ | ⟨hH, he⟩ | ⟨hH, he⟩
    · exact Or.inl ⟨res, hH, by simp [seqPlug, toVal, atPlug, he, vals]⟩
    · exact Or.inr (Or.inl ⟨hH, by simp [seqPlug, toVal, atPlug, he, vals]⟩)
    · simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr (Or.inr ⟨hH, rfl⟩)
  case frame s f s' n fi fi' es es' hs ih =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨hfr, hc⟩ := ih hf [] [] (by simpa only [List.append_nil] using hfoc)
    simp only at hfr
    subst hfr
    refine ⟨rfl, ?_⟩
    simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at hc
    rcases hc with ⟨res, hH, he⟩ | ⟨hH, he⟩ | ⟨hH, he⟩
    · exact Or.inl ⟨res, hH, by simp [seqPlug, toVal, atPlug, he, vals]⟩
    · exact Or.inr (Or.inl ⟨hH, by simp [seqPlug, toVal, atPlug, he, vals]⟩)
    · simp only [Config.mk.injEq] at he
      obtain ⟨rfl, -, rfl⟩ := he
      exact Or.inr (Or.inr ⟨hH, rfl⟩)
  case trap s f E hne =>
    exact absurd hfoc (seqFocus_eval_trap (fun st hh => by cases hh.1) E stk rest)
  case br s f n cont l vs L hlen =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨st, hst⟩ := seqFocus_block (P := HostAt a ft.params.length args)
      (x := .plain (.br l)) rfl (fun _ _ _ => nofun) (fun _ _ _ => nofun) L vs [] []
      (by simpa only [List.append_nil] using hfoc)
    exact absurd hst (hnot _ st)
  case return_ s f n f' k vs L hlen =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨st, hst⟩ := seqFocus_block (P := HostAt a ft.params.length args)
      (x := .plain .return_) rfl (fun _ _ _ => nofun) (fun _ _ _ => nofun) L vs [] []
      (by simpa only [List.append_nil] using hfoc)
    exact absurd hst (hnot _ st)
  case labelExit s f n cont vs =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    exact absurd hfoc (not_seqFocus_vals _ _)
  case frameExit s f n f' vs hlen =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    exact absurd hfoc (not_seqFocus_vals _ _)
  case trapFrame s f n fi =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    exact absurd hfoc.1 (by simp)
  case num s f i args' r hr =>
    have hn := num_toVal_none hr
    simp only [List.append_assoc, seqFocus_vals, List.singleton_append, seqFocus, hn,
      atFocus] at hfoc
    exact absurd hfoc (hnot i _)
  all_goals
    simp only [List.append_assoc, seqFocus_vals, List.cons_append,
      List.nil_append, seqFocus, toVal_instr] at hfoc
    simp only [toVal, atFocus] at hfoc
    exact absurd hfoc (hnot _ _)

mutual
/-- A host invoke at the focus steps to the plug of each returned outcome its host allows. -/
theorem step_plug_host_seq {H : HostSem} {s s' : Store} {f : Frame} {a id : Nat}
    {ft : FuncType} {args res : List Val} (hf : s.funcs[a]? = some (.host ft id))
    (hH : H id s args (.returned s' res)) :
    ∀ (stk : List Val) (es : List AInstr), seqFocus (HostAt a ft.params.length args) stk es →
      Step H ⟨s, f, vals stk.reverse ++ es⟩ ⟨s', f, seqPlug ft.params.length (vals res) stk es⟩
  | _, [], h => by simp [seqFocus] at h
  | stk, e :: rest, h => by
    cases hv : toVal e with
    | some v =>
      simp only [seqFocus, hv] at h
      have hs := step_plug_host_seq (f := f) hf hH (v :: stk) rest h
      have he := eq_instr_of_toVal hv
      subst he
      simp only [seqPlug, toVal_instr]
      simpa only [List.reverse_cons, vals, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using hs
    | none =>
      simp only [seqFocus, hv] at h
      simp only [seqPlug, hv]
      exact step_plug_host_at hf hH stk e rest h

/-- `step_plug_host_seq` at the non-value `e`. -/
theorem step_plug_host_at {H : HostSem} {s s' : Store} {f : Frame} {a id : Nat}
    {ft : FuncType} {args res : List Val} (hf : s.funcs[a]? = some (.host ft id))
    (hH : H id s args (.returned s' res)) (stk : List Val) (e : AInstr) (rest : List AInstr)
    (h : atFocus (HostAt a ft.params.length args) stk e) :
    Step H ⟨s, f, vals stk.reverse ++ e :: rest⟩
      ⟨s', f, atPlug ft.params.length (vals res) stk e rest⟩ := by
  cases e with
  | label n cont body =>
    have hb := step_plug_host_seq (f := f) hf hH [] body h
    rw [List.reverse_nil, show vals ([] : List Val) = [] from rfl, List.nil_append] at hb
    have hs := Step.seq (vs := stk.reverse) (rest := rest) (Step.label (n := n) (cont := cont) hb)
    simpa only [atPlug, List.append_assoc, List.singleton_append] using hs
  | frame n fi body =>
    have hb := step_plug_host_seq (f := fi) hf hH [] body h
    rw [List.reverse_nil, show vals ([] : List Val) = [] from rfl, List.nil_append] at hb
    have hs := Step.seq (vs := stk.reverse) (rest := rest) (Step.frame (f := f) (n := n) hb)
    simpa only [atPlug, List.append_assoc, List.singleton_append] using hs
  | invoke b =>
    obtain ⟨hb, hm, hargs⟩ := h
    simp only [AInstr.invoke.injEq] at hb
    subst hb
    have hlen : args.length = ft.params.length := by
      rw [← hargs, List.length_reverse, List.length_take, Nat.min_eq_left hm]
    have hsplit : stk.reverse = (stk.drop ft.params.length).reverse ++ args := by
      rw [← hargs, ← List.reverse_append, List.take_append_drop]
    have hstep := Step.seq (vs := (stk.drop ft.params.length).reverse) (rest := rest)
      (Step.invokeHost (f := f) hf hlen hH)
    simp only [atPlug]
    rw [hsplit]
    simpa only [vals, List.map_append, List.append_assoc, List.singleton_append] using hstep
  | plain i => exact absurd h.1 (by simp)
  | refFuncAddr x => exact absurd h.1 (by simp)
  | refExternAddr x => exact absurd h.1 (by simp)
  | trap => exact absurd h.1 (by simp)
end

/-- `Must` across a host call in context: when the host has a returned outcome and allows
nothing but returns, and every returned outcome's plugged configuration satisfies `Must`, so does
the configuration before the call. -/
theorem must_host_focus {H : HostSem} {Q : Outcome → Prop} {s : Store} {f : Frame}
    {es : List AInstr} {a id : Nat} {ft : FuncType} {args : List Val}
    (hf : s.funcs[a]? = some (.host ft id))
    (hfoc : seqFocus (HostAt a ft.params.length args) [] es)
    (hex : ∃ s' res, H id s args (.returned s' res))
    (honly : ∀ o, H id s args o → ∃ s' res, o = .returned s' res)
    (hk : ∀ s' res, H id s args (.returned s' res) →
      Must H Q ⟨s', f, seqPlug ft.params.length (vals res) [] es⟩) :
    Must H Q ⟨s, f, es⟩ := by
  obtain ⟨s₀, res₀, h₀⟩ := hex
  refine Must.next ⟨_, by simpa using step_plug_host_seq (f := f) hf h₀ [] es hfoc⟩ ?_
  intro c' hs
  obtain ⟨hfr, hc⟩ := step_focus_host hs hf [] [] (by simpa using hfoc)
  simp only at hfr
  rcases hc with ⟨res, hH, he⟩ | ⟨hH, -⟩ | ⟨hH, -⟩
  · simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at he
    obtain ⟨cs, cf, ci⟩ := c'
    simp only at hfr he hH
    subst hfr he
    exact hk cs res hH
  · obtain ⟨_, _, ho⟩ := honly _ hH
    cases ho
  · obtain ⟨_, _, ho⟩ := honly _ hH
    cases ho

/-! ## Float binary operators in context -/

/-- The focus of the numeric redex `plain i` whose `m` operands below it are `args` (bottom
first). -/
def NumAt (i : Instr) (m : Nat) (args : List Val) (vs : List Val) (e : AInstr) : Prop :=
  e = .plain i ∧ m ≤ vs.length ∧ (vs.take m).reverse = args

theorem numResults_fbinop_length {w : Width} {op : FBinOp} {args : List Val} {r : Option Val}
    (h : r ∈ numResults (.fbinop w op) args) : args.length = 2 := by
  unfold numResults at h
  split at h <;> simp_all

set_option maxHeartbeats 1000000 in
/-- Every step from a configuration whose focus is the float operator `fbinop w op` on `args`
keeps the store and the frame and replaces that redex and its operands by an allowed result. -/
theorem step_focus_fbinop {H : HostSem} {c c' : Config} (h : Step H c c') {w : Width}
    {op : FBinOp} {args : List Val} :
    ∀ (stk : List Val) (rest : List AInstr),
      seqFocus (NumAt (.fbinop w op) 2 args) stk (c.instrs ++ rest) →
      c'.store = c.store ∧ c'.frame = c.frame ∧
      ∃ r ∈ numResults (.fbinop w op) args,
        vals stk.reverse ++ c'.instrs ++ rest = seqPlug 2 (numOut r) stk (c.instrs ++ rest) := by
  induction h
  all_goals intro stk rest hfoc
  case num s f i args' r hr =>
    have hn := num_toVal_none hr
    simp only [List.append_assoc, seqFocus_vals, List.singleton_append, seqFocus, hn, atFocus,
      NumAt, AInstr.plain.injEq] at hfoc
    obtain ⟨rfl, -, hargs⟩ := hfoc
    have hlen := numResults_fbinop_length hr
    have hv : ((args'.reverse ++ stk).take 2).reverse = args' := by
      rw [← hlen, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
        List.reverse_reverse]
    rw [hv] at hargs
    subst hargs
    refine ⟨rfl, rfl, r, hr, ?_⟩
    simp only [List.append_assoc, seqPlug_vals, List.singleton_append, seqPlug, hn, atPlug]
    rw [← hlen, List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp),
      List.nil_append]
  case seq s f s' f' es es' vs tail hs ih =>
    simp only [List.append_assoc, seqFocus_vals] at hfoc
    obtain ⟨hst, hfr, r, hr, he⟩ := ih (vs.reverse ++ stk) (tail ++ rest) hfoc
    refine ⟨hst, hfr, r, hr, ?_⟩
    simp only [List.append_assoc, seqPlug_vals, List.reverse_append, List.reverse_reverse,
      vals, List.map_append] at he ⊢
    simpa only [List.append_assoc] using he
  case label s f s' f' n cont es es' hs ih =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨hst, hfr, r, hr, he⟩ := ih [] [] (by simpa only [List.append_nil] using hfoc)
    refine ⟨hst, hfr, r, hr, ?_⟩
    simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at he
    simp [seqPlug, toVal, atPlug, he, vals]
  case frame s f s' n fi fi' es es' hs ih =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨hst, hfr, r, hr, he⟩ := ih [] [] (by simpa only [List.append_nil] using hfoc)
    simp only at hst hfr
    subst hst hfr
    refine ⟨rfl, rfl, r, hr, ?_⟩
    simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at he
    simp [seqPlug, toVal, atPlug, he, vals]
  case trap s f E hne =>
    exact absurd hfoc (seqFocus_eval_trap (fun st hh => by cases hh.1) E stk rest)
  case br s f n cont l vs L hlen =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨st, hst⟩ := seqFocus_block (P := NumAt (.fbinop w op) 2 args)
      (x := .plain (.br l)) rfl (fun _ _ _ => nofun) (fun _ _ _ => nofun) L vs [] []
      (by simpa only [List.append_nil] using hfoc)
    exact absurd hst.1 (by simp)
  case return_ s f n f' k vs L hlen =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    obtain ⟨st, hst⟩ := seqFocus_block (P := NumAt (.fbinop w op) 2 args)
      (x := .plain .return_) rfl (fun _ _ _ => nofun) (fun _ _ _ => nofun) L vs [] []
      (by simpa only [List.append_nil] using hfoc)
    exact absurd hst.1 (by simp)
  case labelExit s f n cont vs =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    exact absurd hfoc (not_seqFocus_vals _ _)
  case frameExit s f n f' vs hlen =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    exact absurd hfoc (not_seqFocus_vals _ _)
  case trapFrame s f n fi =>
    simp only [List.singleton_append, seqFocus, toVal, atFocus] at hfoc
    exact absurd hfoc.1 (by simp)
  all_goals
    simp only [List.append_assoc, seqFocus_vals, List.cons_append,
      List.nil_append, seqFocus, toVal_instr] at hfoc
    simp only [toVal, atFocus] at hfoc
    exact absurd hfoc.1 (by simp)

mutual
/-- A float operator at the focus steps to the plug of each allowed result. -/
theorem step_plug_fbinop_seq {H : HostSem} {s : Store} {f : Frame} {w : Width} {op : FBinOp}
    {args : List Val} {r : Option Val} (hr : r ∈ numResults (.fbinop w op) args) :
    ∀ (stk : List Val) (es : List AInstr), seqFocus (NumAt (.fbinop w op) 2 args) stk es →
      Step H ⟨s, f, vals stk.reverse ++ es⟩ ⟨s, f, seqPlug 2 (numOut r) stk es⟩
  | _, [], h => by simp [seqFocus] at h
  | stk, e :: rest, h => by
    cases hv : toVal e with
    | some v =>
      simp only [seqFocus, hv] at h
      have hs := step_plug_fbinop_seq (H := H) (s := s) (f := f) hr (v :: stk) rest h
      have he := eq_instr_of_toVal hv
      subst he
      simp only [seqPlug, toVal_instr]
      simpa only [List.reverse_cons, vals, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using hs
    | none =>
      simp only [seqFocus, hv] at h
      simp only [seqPlug, hv]
      exact step_plug_fbinop_at hr stk e rest h

/-- `step_plug_fbinop_seq` at the non-value `e`. -/
theorem step_plug_fbinop_at {H : HostSem} {s : Store} {f : Frame} {w : Width} {op : FBinOp}
    {args : List Val} {r : Option Val} (hr : r ∈ numResults (.fbinop w op) args)
    (stk : List Val) (e : AInstr) (rest : List AInstr)
    (h : atFocus (NumAt (.fbinop w op) 2 args) stk e) :
    Step H ⟨s, f, vals stk.reverse ++ e :: rest⟩ ⟨s, f, atPlug 2 (numOut r) stk e rest⟩ := by
  cases e with
  | label n cont body =>
    have hb := step_plug_fbinop_seq (H := H) (s := s) (f := f) hr [] body h
    rw [List.reverse_nil, show vals ([] : List Val) = [] from rfl, List.nil_append] at hb
    have hs := Step.seq (vs := stk.reverse) (rest := rest) (Step.label (n := n) (cont := cont) hb)
    simpa only [atPlug, List.append_assoc, List.singleton_append] using hs
  | frame n fi body =>
    have hb := step_plug_fbinop_seq (H := H) (s := s) (f := fi) hr [] body h
    rw [List.reverse_nil, show vals ([] : List Val) = [] from rfl, List.nil_append] at hb
    have hs := Step.seq (vs := stk.reverse) (rest := rest) (Step.frame (f := f) (n := n) hb)
    simpa only [atPlug, List.append_assoc, List.singleton_append] using hs
  | plain i =>
    obtain ⟨hi, hm, hargs⟩ := h
    simp only [AInstr.plain.injEq] at hi
    subst hi
    have hlen : args.length = 2 := by
      rw [← hargs, List.length_reverse, List.length_take, Nat.min_eq_left hm]
    have hsplit : stk.reverse = (stk.drop 2).reverse ++ args := by
      rw [← hargs, ← List.reverse_append, List.take_append_drop]
    have hstep := Step.seq (vs := (stk.drop 2).reverse) (rest := rest)
      (Step.num (H := H) (s := s) (f := f) hr)
    simp only [atPlug]
    rw [hsplit]
    simpa only [vals, List.map_append, List.append_assoc, List.singleton_append] using hstep
  | invoke b => exact absurd h.1 (by simp)
  | refFuncAddr x => exact absurd h.1 (by simp)
  | refExternAddr x => exact absurd h.1 (by simp)
  | trap => exact absurd h.1 (by simp)
end

/-- `Must` across a float operator in context: when it has a result, and every allowed result's
plugged configuration satisfies `Must`, so does the configuration before it. -/
theorem must_fbinop_focus {H : HostSem} {Q : Outcome → Prop} {s : Store} {f : Frame}
    {es : List AInstr} {w : Width} {op : FBinOp} {args : List Val}
    (hfoc : seqFocus (NumAt (.fbinop w op) 2 args) [] es)
    (hne : (numResults (.fbinop w op) args).Nonempty)
    (hk : ∀ r ∈ numResults (.fbinop w op) args, Must H Q ⟨s, f, seqPlug 2 (numOut r) [] es⟩) :
    Must H Q ⟨s, f, es⟩ := by
  obtain ⟨r₀, hr₀⟩ := hne
  have h₀ := step_plug_fbinop_seq (H := H) (s := s) (f := f) hr₀ [] es hfoc
  refine Must.next ⟨_, by simpa using h₀⟩ ?_
  intro c' hs
  obtain ⟨hst, hfr, r, hr, he⟩ := step_focus_fbinop hs [] [] (by simpa using hfoc)
  simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at he
  obtain ⟨cs, cf, ci⟩ := c'
  simp only at hst hfr he
  subst hst hfr he
  exact hk r hr

end FVA.Wasm.Exec.Ref
