import FVA.Proof.Lib.Walk
import FVA.Proof.Exec.Choice

/-!
# Symbolic caller contexts

`C.fill c` = configuration `c` running under the labels and frames of `C`, each with its saved
instruction tail; a step of `c` is a step of `C.fill c` (`Context.seq`), so a proof steps the
innermost code while the callers stay symbolic (`wasm_cstep`). `blockCode` & co. name slices of
a lifted function's code.
-/

namespace FVA.Wasm

/-- The body of a `block`. -/
def blockCode : Instr → List Instr
  | .block _ code => code
  | _ => []

/-- The body of a `loop`. -/
def loopCode : Instr → List Instr
  | .loop _ code => code
  | _ => []

/-- The `then` branch of an `if`. -/
def thenCode : Instr → List Instr
  | .if_ _ code _ => code
  | _ => []

/-- The `else` branch of an `if`. -/
def elseCode : Instr → List Instr
  | .if_ _ _ code => code
  | _ => []

end FVA.Wasm

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- Active labels/frames with saved instruction tails. The hole carries its current frame. -/
inductive Context where
  | hole
  | label (n : Nat) (cont : List Instr) (rest : List AInstr) (outer : Context)
  | frame (n : Nat) (caller : Frame) (rest : List AInstr) (outer : Context)

/-- `c` running under `C`'s labels and frames, each followed by its saved tail. -/
def Context.fill : Context → Config → Config
  | .hole, c => c
  | .label n cont rest outer, c =>
    outer.fill ⟨c.store, c.frame, .label n cont c.instrs :: rest⟩
  | .frame n caller rest outer, c =>
    outer.fill ⟨c.store, caller, .frame n c.frame c.instrs :: rest⟩

theorem Context.seq {s s' : Store} {f f' : Frame} {es es' : List AInstr}
    (C : Context) (hu : seqUnique false s f [] es = true) (hs : seq s f [] es = .step s' f' es') :
    seqUnique false (C.fill ⟨s, f, es⟩).store (C.fill ⟨s, f, es⟩).frame []
      (C.fill ⟨s, f, es⟩).instrs = true ∧
    seq (C.fill ⟨s, f, es⟩).store (C.fill ⟨s, f, es⟩).frame []
      (C.fill ⟨s, f, es⟩).instrs = .step (C.fill ⟨s', f', es'⟩).store
        (C.fill ⟨s', f', es'⟩).frame (C.fill ⟨s', f', es'⟩).instrs := by
  induction C generalizing s s' f f' es es' with
  | hole => exact ⟨hu, hs⟩
  | label n cont rest outer ih =>
    apply ih
    · simpa only [seqUnique_cons_none _ (toVal_label ..), atUnique_label] using hu
    · simp only [seq_cons_none _ (toVal_label ..), atInstr_label, hs,
        List.reverse_nil, vals, List.map_nil, List.nil_append, List.singleton_append]
  | frame n caller rest outer ih =>
    apply ih
    · simpa only [seqUnique_cons_none _ (toVal_frame ..), atUnique_frame] using hu
    · simp only [seq_cons_none _ (toVal_frame ..), atInstr_frame, hs,
        List.reverse_nil, vals, List.map_nil, List.nil_append, List.singleton_append]

theorem must_context_seq {H : HostSem} {Q : Outcome → Prop} {s s' : Store}
    {f f' : Frame} {es es' : List AInstr} (C : Context)
    (hu : seqUnique false s f [] es = true) (hs : seq s f [] es = .step s' f' es')
    (hk : Must H Q (C.fill ⟨s', f', es'⟩)) : Must H Q (C.fill ⟨s, f, es⟩) := by
  obtain ⟨hu', hs'⟩ := C.seq hu hs
  exact must_of_seq hu' hs' hk

open Lean Meta Elab Tactic in
/-- `wasm_step1` inside a symbolic caller context. -/
elab "wasm_cstep" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (H, Q, cc) := ty.consumeMData.app3? ``Must
    | throwError "wasm_cstep: expected Must"
  let some (C, c) := cc.consumeMData.app2? ``Context.fill
    | throwError "wasm_cstep: expected Context.fill"
  let c ← whnfR c
  let some (s, f, l) := c.app3? ``FVA.Wasm.Exec.Config.mk
    | throwError "wasm_cstep: expected literal configuration"
  let stx ← `(tactic| simp only [wasm_step, $xs,*])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let nil ← mkListLit (mkConst ``Val) []
  let (r, _) ← simp (← mkAppM ``seq #[s, f, nil, l]) ctx simprocs
  let out ← instantiateMVars r.expr
  let some (s', f', l') := (← whnfR out).consumeMData.app3? ``Out.step
    | throwError m!"wasm_cstep: next step not computed: {out}"
  let hs ← r.getProof
  let u ← mkAppM ``seqUnique #[mkConst ``Bool.false, s, f, nil, l]
  let hu ← mkFreshExprMVar (← mkEq u (mkConst ``Bool.true))
  let rest ← evalTacticAt stx hu.mvarId!
  unless rest.isEmpty do throwError "wasm_cstep: uniqueness not shown"
  let nextC ← mkAppM ``Context.fill #[C, ← mkAppM ``FVA.Wasm.Exec.Config.mk #[s', f', l']]
  let next ← mkFreshExprMVar (← mkAppM ``Must #[H, Q, nextC])
  g.assign (← mkAppM ``must_context_seq #[C, hu, hs, next])
  replaceMainGoal [next.mvarId!]

@[simp] theorem Context.store (C : Context) (c : Config) : (C.fill c).store = c.store := by
  induction C generalizing c with
  | hole => rfl
  | label n cont rest outer ih => exact ih _
  | frame n caller rest outer ih => exact ih _

theorem Context.focus {P : List Val → AInstr → Prop} (C : Context) (c : Config)
    (h : seqFocus P [] c.instrs) : seqFocus P [] (C.fill c).instrs := by
  induction C generalizing c with
  | hole => exact h
  | label n cont rest outer ih =>
    apply ih
    simpa only [seqFocus, toVal_label, atFocus] using h
  | frame n caller rest outer ih =>
    apply ih
    simpa only [seqFocus, toVal_frame, atFocus] using h

theorem Context.plug (C : Context) (s : Store) (f : Frame) (es : List AInstr)
    (k : Nat) (out : List AInstr) :
    (⟨s, (C.fill ⟨s, f, es⟩).frame,
      seqPlug k out [] (C.fill ⟨s, f, es⟩).instrs⟩ : Config) =
      C.fill ⟨s, f, seqPlug k out [] es⟩ := by
  induction C generalizing s f es with
  | hole => rfl
  | label n cont rest outer ih =>
    simp only [Context.fill, ih]
    simp only [seqPlug, toVal_label, atPlug, List.reverse_nil, vals, List.map_nil,
      List.nil_append, List.singleton_append]
  | frame n caller rest outer ih =>
    simp only [Context.fill, ih]
    simp only [seqPlug, toVal_frame, atPlug, List.reverse_nil, vals, List.map_nil,
      List.nil_append, List.singleton_append]

theorem must_fbinop_context {H : HostSem} {Q : Outcome → Prop} {s : Store} {f : Frame}
    {es : List AInstr} {w : Width} {op : FBinOp} {args : List Val} (C : Context)
    (hfoc : seqFocus (NumAt (.fbinop w op) 2 args) [] es)
    (hne : (numResults (.fbinop w op) args).Nonempty)
    (hk : ∀ r ∈ numResults (.fbinop w op) args,
      Must H Q (C.fill ⟨s, f, seqPlug 2 (numOut r) [] es⟩)) :
    Must H Q (C.fill ⟨s, f, es⟩) := by
  have hh := must_fbinop_focus (H := H) (Q := Q) (s := s)
    (f := (C.fill ⟨s, f, es⟩).frame) (C.focus ⟨s, f, es⟩ hfoc) hne (fun r hr => by
      rw [C.plug]
      exact hk r hr)
  change Must H Q ⟨(C.fill ⟨s, f, es⟩).store, (C.fill ⟨s, f, es⟩).frame,
    (C.fill ⟨s, f, es⟩).instrs⟩
  rw [Context.store]
  exact hh

end FVA.Wasm.Exec.Ref
