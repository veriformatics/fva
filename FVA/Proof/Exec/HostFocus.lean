import FVA.Proof.Exec.Det

/-!
# Host-call focus (U27 T4)

`seq` reports a host call as `.host a args k`: `invoke a` of a host function on `args`, in
context `k`. Each allowed outcome of the call is a step (`host_step`), and every step from such
a configuration is one of them (`host_complete`), under either growth policy.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

@[simp] theorem HCtx.result_seq (vs : List Val) (k : HCtx) (rest : List AInstr) (a : Nat)
    (args : List Val) (o : HostOutcome) :
    (HCtx.seq vs k rest).result a args o = vals vs ++ k.result a args o ++ rest := by
  cases o <;> rfl

@[simp] theorem HCtx.result_label (n : Nat) (cont : List Instr) (k : HCtx) (a : Nat)
    (args : List Val) (o : HostOutcome) :
    (HCtx.label n cont k).result a args o = [.label n cont (k.result a args o)] := by
  cases o <;> rfl

@[simp] theorem HCtx.result_frame (n : Nat) (fi : Frame) (k : HCtx) (a : Nat)
    (args : List Val) (o : HostOutcome) :
    (HCtx.frame n fi k).result a args o = [.frame n fi (k.result a args o)] := by
  cases o <;> rfl

/-- A step inside a host-call context, frame unchanged, is a step of the whole sequence. -/
theorem HCtx.lift {H : HostSem} {fits : Bool} {s s' : Store} {es es' : List AInstr}
    (h : ∀ f, StepP H fits ⟨s, f, es⟩ ⟨s', f, es'⟩) :
    ∀ (k : HCtx) (f : Frame), StepP H fits ⟨s, f, k.fill es⟩ ⟨s', f, k.fill es'⟩
  | .hole, f => h f
  | .seq vs k rest, f => StepP.seq (vs := vs) (rest := rest) (HCtx.lift h k f)
  | .label n cont k, f => StepP.label (n := n) (cont := cont) (HCtx.lift h k f)
  | .frame n fi k, f => StepP.frame (f := f) (n := n) (HCtx.lift h k fi)

/-- Each allowed outcome of the focused host call is a step. -/
theorem host_step {H : HostSem} {fits : Bool} {s : Store} {f : Frame} {stk : List Val}
    {es : List AInstr} {a : Nat} {args : List Val} {k : HCtx} {ft : FuncType} {id : Nat}
    {o : HostOutcome} (hq : seq s f stk es = .host a args k)
    (hf : s.funcs[a]? = some (.host ft id)) (ho : H id s args o) :
    StepP H fits ⟨s, f, vals stk.reverse ++ es⟩ ⟨hostStore s o, f, k.result a args o⟩ := by
  have hx := seq_explains H s f stk es
  rw [hq] at hx
  obtain ⟨ft', id', hf', hlen, hes⟩ := hx
  rw [hf] at hf'
  simp only [Option.some.injEq, FuncInst.host.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  rw [hes]
  cases o with
  | returned s' vs => exact HCtx.lift (fun f => StepP.invokeHost hf hlen ho) k f
  | trapped s' => exact HCtx.lift (fun f => StepP.invokeHostTrap hf hlen ho) k f
  | diverged => exact HCtx.lift (fun f => StepP.invokeHostDiverge hf hlen ho) k f

theorem atInstr_plain_ne_host {s : Store} {f : Frame} {vs : List Val} {i : Instr}
    {rest : List AInstr} {a : Nat} {args : List Val} {k : HCtx} :
    atInstr s f vs (.plain i) rest ≠ .host a args k := by
  by_cases hb : ∃ j, i = .br j
  · obtain ⟨j, rfl⟩ := hb
    simp [atInstr]
  · by_cases hr : i = .return_
    · subst hr
      simp [atInstr]
    · rw [atInstr_plain (fun j hj => hb ⟨j, hj⟩) hr]
      split <;> simp

theorem seq_eval_trap_ne_host (s : Store) (f : Frame) (E : EvalCtx) :
    ∀ (stk : List Val) (rest : List AInstr) (a : Nat) (args : List Val) (k : HCtx),
      seq s f stk (E.fill [.trap] ++ rest) ≠ .host a args k := by
  induction E with
  | hole =>
    intro stk rest a args k
    simp only [EvalCtx.fill, List.singleton_append, seq, toVal, atInstr]
    rcases Bool.eq_false_or_eq_true (stk.isEmpty && rest.isEmpty) with h | h <;> simp [h]
  | seq vs E rest' ih =>
    intro stk rest a args k
    simp only [EvalCtx.fill, List.append_assoc, seq_vals]
    exact ih _ _ a args k
  | label n cont E ih =>
    intro stk rest a args k
    simp only [EvalCtx.fill, List.singleton_append, seq, toVal, atInstr]
    have hi := ih [] []
    simp only [List.append_nil] at hi
    split <;> first
      | (simp_all [Bool.cond_eq_ite]; done)
      | (simp_all [Bool.cond_eq_ite]; split <;> simp)

set_option maxHeartbeats 1000000 in
/-- Every step from a configuration whose next redex is a host call is an allowed outcome of
that call, in place. -/
theorem host_complete {H : HostSem} {fits : Bool} {c d : Config} (h : StepP H fits c d) :
    ∀ (stk : List Val) (rest : List AInstr) (a : Nat) (args : List Val) (k : HCtx),
      seq c.store c.frame stk (c.instrs ++ rest) = .host a args k →
      ∃ ft id o, c.store.funcs[a]? = some (.host ft id) ∧ H id c.store args o ∧
        d.store = hostStore c.store o ∧ d.frame = c.frame ∧
        vals stk.reverse ++ d.instrs ++ rest = k.result a args o := by
  induction h
  all_goals intro stk rest a' args' k' hq
  case invokeHost s s' f a ft id vs res hf hlen hH =>
    rw [List.append_assoc, seq_vals] at hq
    simp only [List.singleton_append, seq, toVal, atInstr, hf, List.length_append,
      List.length_reverse, hlen, Bool.cond_eq_ite, Nat.blt_eq] at hq
    simp only [Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Out.host.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    refine ⟨ft, id, .returned s' res, hf, ?_, rfl, rfl, ?_⟩
    · simpa [← hlen] using hH
    · simp [HCtx.result, HCtx.fill, ← hlen]
  case invokeHostTrap s s' f a ft id vs hf hlen hH =>
    rw [List.append_assoc, seq_vals] at hq
    simp only [List.singleton_append, seq, toVal, atInstr, hf, List.length_append,
      List.length_reverse, hlen, Bool.cond_eq_ite, Nat.blt_eq] at hq
    simp only [Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Out.host.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    refine ⟨ft, id, .trapped s', hf, ?_, rfl, rfl, ?_⟩
    · simpa [← hlen] using hH
    · simp [HCtx.result, HCtx.fill, ← hlen]
  case invokeHostDiverge s f a ft id vs hf hlen hH =>
    rw [List.append_assoc, seq_vals] at hq
    simp only [List.singleton_append, seq, toVal, atInstr, hf, List.length_append,
      List.length_reverse, hlen, Bool.cond_eq_ite, Nat.blt_eq] at hq
    simp only [Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Out.host.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    refine ⟨ft, id, .diverged, hf, ?_, rfl, rfl, ?_⟩
    · simpa [← hlen] using hH
    · simp [HCtx.result, HCtx.fill, ← hlen]
  case seq s f s' f' es es' vs tail h ih =>
    rw [List.append_assoc, List.append_assoc, seq_vals] at hq
    obtain ⟨ft, id, o, hf, hH, hs, hfr, hk⟩ :=
      ih (vs.reverse ++ stk) (tail ++ rest) a' args' k' (by simpa only [List.append_assoc] using hq)
    refine ⟨ft, id, o, hf, hH, hs, hfr, ?_⟩
    simpa [List.reverse_append, List.append_assoc] using hk
  case label s f s' f' n cont es es' h ih =>
    simp only [List.singleton_append, seq, toVal, atInstr] at hq
    split at hq
    all_goals first
      | (simp only [reduceCtorEq] at hq)
      | (simp only [Bool.cond_eq_ite] at hq; split at hq <;> simp only [reduceCtorEq] at hq)
      | (rename_i a args k hb
         simp only [Out.host.injEq] at hq
         obtain ⟨rfl, rfl, rfl⟩ := hq
         obtain ⟨ft, id, o, hf, hH, hs, hfr, hk⟩ := ih [] [] a args k (by simpa using hb)
         refine ⟨ft, id, o, hf, hH, hs, hfr, ?_⟩
         simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hk
         simp [hk])
  case frame s f s' n fi fi' es es' h ih =>
    simp only [List.singleton_append, seq, toVal, atInstr] at hq
    split at hq
    all_goals first
      | (simp only [reduceCtorEq] at hq)
      | (simp only [Bool.cond_eq_ite] at hq; split at hq <;> simp only [reduceCtorEq] at hq)
      | (simp only [Bool.cond_eq_ite] at hq; split at hq <;>
          (try split at hq) <;> simp only [reduceCtorEq] at hq)
      | (rename_i a args k hb
         simp only [Out.host.injEq] at hq
         obtain ⟨rfl, rfl, rfl⟩ := hq
         obtain ⟨ft, id, o, hf, hH, hs, hfr, hk⟩ := ih [] [] a args k (by simpa using hb)
         refine ⟨ft, id, o, hf, hH, hs, rfl, ?_⟩
         simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hk
         simp only at hfr
         simp [hk, hfr])
  case trap s f E hne =>
    exact absurd hq (seq_eval_trap_ne_host s f E stk rest a' args' k')
  case num s f i args r hr =>
    have hn := num_toVal_none hr
    rw [List.append_assoc, seq_vals] at hq
    simp only [List.singleton_append, seq, hn] at hq
    exact absurd hq atInstr_plain_ne_host
  case labelExit | frameExit | trapFrame =>
    simp_all [seq, toVal, atInstr, seq_values, isTrapOnly, Bool.cond_eq_ite]
    all_goals (split at hq <;> simp at hq)
  case br s f n cont l vs L hlen =>
    obtain ⟨extra, hb⟩ := seq_block_br s f vs L 0 [] []
    simp only [Nat.add_zero, List.append_nil] at hb
    simp only [List.singleton_append, seq, toVal, atInstr, hb, Bool.cond_eq_ite] at hq
    split at hq <;> simp at hq
  case return_ s f n fi k vs L hlen =>
    obtain ⟨extra, hb⟩ := seq_block_ret s fi vs L [] []
    simp only [List.append_nil] at hb
    simp only [List.singleton_append, seq, toVal, atInstr, hb, Bool.cond_eq_ite] at hq
    split at hq <;> simp at hq
  case invoke s f a ft inst code vs hf hlen =>
    rw [List.append_assoc, seq_vals] at hq
    simp only [List.singleton_append, seq, toVal, atInstr, hf, Bool.cond_eq_ite] at hq
    split at hq <;> simp at hq
  all_goals
    simp only [List.append_assoc, List.cons_append, List.nil_append, seq_vals, seq,
      toVal_instr] at hq
    simp only [toVal] at hq
    exact absurd hq atInstr_plain_ne_host

end FVA.Wasm.Exec.Ref
