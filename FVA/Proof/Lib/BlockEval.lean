import FVA.Proof.Lib.Footprint

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- Saved operand stacks around an evaluator's focused block. -/
inductive BContext where
  | base (outer : Context)
  | label (vs : List Val) (n : Nat) (cont : List Instr) (rest : List AInstr) (outer : BContext)
  | frame (vs : List Val) (n : Nat) (caller : Frame) (rest : List AInstr) (outer : BContext)

/-- `Context.fill` with the operand values `vs` saved below each label or frame (`Context`
saves none). -/
def BContext.fill : BContext → Config → Config
  | .base C, c => C.fill c
  | .label vs n cont rest C, c =>
      C.fill ⟨c.store, c.frame, vals vs ++ (.label n cont c.instrs :: rest)⟩
  | .frame vs n caller rest C, c =>
      C.fill ⟨c.store, caller, vals vs ++ (.frame n c.frame c.instrs :: rest)⟩

theorem BContext.seq {s s' : Store} {f f' : Frame} {es es' : List AInstr}
    (C : BContext) (hu : seqUnique false s f [] es = true) (hs : seq s f [] es = .step s' f' es') :
    seqUnique false (C.fill ⟨s, f, es⟩).store (C.fill ⟨s, f, es⟩).frame []
      (C.fill ⟨s, f, es⟩).instrs = true ∧
    seq (C.fill ⟨s, f, es⟩).store (C.fill ⟨s, f, es⟩).frame []
      (C.fill ⟨s, f, es⟩).instrs = .step (C.fill ⟨s', f', es'⟩).store
        (C.fill ⟨s', f', es'⟩).frame (C.fill ⟨s', f', es'⟩).instrs := by
  induction C generalizing s s' f f' es es' with
  | base C => exact C.seq hu hs
  | label vs n cont rest C ih =>
    apply ih
    · simpa only [List.append_assoc, List.singleton_append, seqUnique_vals, List.append_nil,
        seqUnique_cons_none _ (toVal_label ..), atUnique_label] using hu
    · simp only [List.append_assoc, List.singleton_append, seq_vals, List.append_nil,
        seq_cons_none _ (toVal_label ..), atInstr_label, hs, List.reverse_reverse]
  | frame vs n caller rest C ih =>
    apply ih
    · simpa only [List.append_assoc, List.singleton_append, seqUnique_vals, List.append_nil,
        seqUnique_cons_none _ (toVal_frame ..), atUnique_frame] using hu
    · simp only [List.append_assoc, List.singleton_append, seq_vals, List.append_nil,
        seq_cons_none _ (toVal_frame ..), atInstr_frame, hs, List.reverse_reverse]

theorem BContext.access_fill (C : BContext) (c : Config) : access (C.fill c) = access c := by
  induction C generalizing c with
  | base C => exact C.access_fill c
  | label vs n cont rest C ih =>
    rw [BContext.fill, ih]
    simp only [access, seqAccess_vals, List.append_nil,
      seqAccess_cons_none _ (toVal_label ..), atAccess_label]
  | frame vs n caller rest C ih =>
    rw [BContext.fill, ih]
    simp only [access, seqAccess_vals, List.append_nil,
      seqAccess_cons_none _ (toVal_frame ..), atAccess_frame]

theorem BContext.within {R W : Nat → Nat → Prop} (C : BContext) {c : Config}
    (h : Within R W c) : Within R W (C.fill c) := by
  cases hx : access c with
  | none => exact within_of_access_none (by rw [C.access_fill, hx])
  | some x =>
    refine within_of_access (by rw [C.access_fill, hx]) (fun hw a hlo hhi => ?_)
      (fun hw a hlo hhi => ?_)
    · exact h.1 x.mem a (reads_iff.mpr ⟨x, hx, hw, rfl, hlo, hhi⟩)
    · exact h.2 x.mem a (writes_iff.mpr ⟨x, hx, hw, rfl, hlo, hhi⟩)

/-- A checked block: `k` unique steps, its final configuration, and every step's access. -/
def blockEval : Nat → Store → Frame → List AInstr → Option (Config × List (Option Access))
  | 0, s, f, es => some (⟨s, f, es⟩, [])
  | k + 1, s, f, es =>
    bif seqUnique false s f [] es then
      match seq s f [] es with
      | .step s' f' es' => (blockEval k s' f' es').map fun (c, trace) =>
          (c, seqAccess s f [] es :: trace)
      | _ => none
    else none

/-- All accesses of a computed block fit its caller's footprint. -/
def TraceOK (R W : Nat → Nat → Prop) : List (Option Access) → Prop
  | [] => True
  | a :: trace => AccessOK R W a ∧ TraceOK R W trace

/-- Rewriting one evaluator result transports `Until` across the whole block. -/
theorem blockEval_until {H : HostSem} {R W : Nat → Nat → Prop} {Q : Config → Prop}
    {k : Nat} {s : Store} {f : Frame} {es : List AInstr} {c' : Config}
    {trace : List (Option Access)} (C : BContext)
    (he : blockEval k s f es = some (c', trace)) (ht : TraceOK R W trace)
    (hq : Until H (Within R W) Q (C.fill c')) :
    Until H (Within R W) Q (C.fill ⟨s, f, es⟩) := by
  induction k generalizing s f es c' trace with
  | zero =>
    simp only [blockEval, Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl⟩
    exact hq
  | succ k ih =>
    cases hu : seqUnique false s f [] es with
    | false => simp only [blockEval, hu, Bool.cond_false, reduceCtorEq] at he
    | true =>
      cases hs : seq s f [] es <;>
        simp only [blockEval, hu, Bool.cond_true, hs, reduceCtorEq] at he
      rename_i s' f' es'
      cases hx : blockEval k s' f' es' with
      | none => simp only [hx, Option.map_none, reduceCtorEq] at he
      | some result =>
        rcases result with ⟨c'', trace'⟩
        simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        obtain ⟨hu', hs'⟩ := C.seq hu hs
        exact until_of_seq hu' hs' (C.within (within_of_accessOK ht.1)) (ih hx ht.2 hq)

open Lean Meta Elab Tactic in
/-- Compute a fixed block, leaving its aggregate footprint and successor judgment. -/
elab "wasm_eval" n:num " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (H, P, Q, cc) := ty.consumeMData.app4? ``Until
    | throwError "wasm_eval: expected Until"
  let some (R, W) := P.consumeMData.app2? ``Within
    | throwError "wasm_eval: expected Within"
  let (C, c, fill) ← match cc.consumeMData.app2? ``BContext.fill with
    | some (C, c) => pure (C, c, ``BContext.fill)
    | none => match cc.consumeMData.app2? ``Context.fill with
      | some (C, c) => pure (← mkAppM ``BContext.base #[C], c, ``BContext.fill)
      | none => throwError "wasm_eval: expected BContext.fill or Context.fill"
  let c ← whnfR c
  let some (s, f, es) := c.app3? ``Config.mk
    | throwError "wasm_eval: expected literal configuration"
  let stx ← `(tactic| simp (config := { bitVecOfNat := true }) (disch := omega) only
    [blockEval, wasm_step, wasm_access, BitVec.reduceOfNat, BitVec.reduceEq, $xs,*])
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let expr ← mkAppM ``blockEval #[mkNatLit n.getNat, s, f, es]
  let (result, _) ← dischargeWrapper.with fun discharge? =>
    simp expr ctx simprocs (some fun e => do
      if let some proof ← Simp.dischargeDefault? e then return some proof
      match discharge? with
      | some discharge => discharge e
      | none => return none)
  let resultExpr ← instantiateMVars result.expr
  let some (_, pair) := resultExpr.consumeMData.app2? ``Option.some
    | throwError m!"wasm_eval: block not computed: {resultExpr}"
  let some (_, _, c', trace) := pair.consumeMData.app4? ``Prod.mk
    | throwError "wasm_eval: malformed block result"
  let he ← result.getProof
  let ht ← mkFreshExprMVar (← mkAppM ``TraceOK #[R, W, trace])
  let hq ← mkFreshExprMVar (← mkAppM ``Until #[H, P, Q, ← mkAppM fill #[C, c']])
  g.assign (mkAppN (mkConst ``blockEval_until)
    #[H, R, W, Q, mkNatLit n.getNat, s, f, es, c', trace, C, he, ht, hq])
  replaceMainGoal [ht.mvarId!, hq.mvarId!]

/-- Discharge `wasm_eval`'s `TraceOK` goal: each step's access inside the footprint. -/
macro "wasm_trace" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [TraceOK, AccessOK, $xs,*])

end FVA.Wasm.Exec.Ref
