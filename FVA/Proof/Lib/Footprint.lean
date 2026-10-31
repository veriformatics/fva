import FVA.Proof.Lib.Context
import FVA.Proof.Exec.Access
import FVA.Spec.CAbi

/-!
# Footprints along executions (contract U19 A3)

`MustW H R W Q c` = total correctness (`Must`) + every reachable configuration inside the
footprint (`Throughout … Within`). `Until H P Q c` = every execution reaches a `Q` configuration,
with `P` at every configuration strictly before it: a loop lemma's form, which says nothing about
the code after its exit. Both step backwards through unique steps only (`mustW_context_seq`,
`until_context_seq`, tactics `wasm_cstepw`, `wasm_cstepu`): a finite checked prefix alone never
proves `Throughout`, so the transport always carries the successor's judgment.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- Total correctness inside a footprint. -/
def MustW (H : HostSem) (R W : Nat → Nat → Prop) (Q : Outcome → Prop) (c : Config) : Prop :=
  Must H Q c ∧ Throughout H (Within R W) c

/-- Every execution from `c` reaches a configuration satisfying `Q`; every configuration before
it satisfies `P`. -/
inductive Until (H : HostSem) (P Q : Config → Prop) : Config → Prop where
  | done {c} : Q c → Until H P Q c
  | next {c} : P c → (∃ c', Step H c c') → (∀ c', Step H c c' → Until H P Q c') → Until H P Q c

theorem within_of_access_none {R W : Nat → Nat → Prop} {c : Config} (h : access c = none) :
    Within R W c := by
  refine ⟨fun ma a hr => ?_, fun ma a hw => ?_⟩
  · obtain ⟨x, hx, -⟩ := reads_iff.mp hr; simp [h] at hx
  · obtain ⟨x, hx, -⟩ := writes_iff.mp hw; simp [h] at hx

/-- A step's footprint from its computed access: a read range inside `R`, a write range inside
`W`. -/
theorem within_of_access {R W : Nat → Nat → Prop} {c : Config} {x : Access}
    (h : access c = some x)
    (hr : x.write = false → ∀ a, x.start ≤ a → a < x.start + x.len → R x.mem a)
    (hw : x.write = true → ∀ a, x.start ≤ a → a < x.start + x.len → W x.mem a) :
    Within R W c := by
  refine ⟨fun ma a hra => ?_, fun ma a hwa => ?_⟩
  · obtain ⟨y, hy, hwr, rfl, hlo, hhi⟩ := reads_iff.mp hra
    rw [h, Option.some.injEq] at hy; subst hy; exact hr hwr a hlo hhi
  · obtain ⟨y, hy, hwr, rfl, hlo, hhi⟩ := writes_iff.mp hwa
    rw [h, Option.some.injEq] at hy; subst hy; exact hw hwr a hlo hhi

theorem access_vals (s : Store) (f : Frame) (vs : List Val) : access ⟨s, f, vals vs⟩ = none := by
  show seqAccess s f [] (vals vs) = none
  rw [← List.append_nil (vals vs), seqAccess_vals]
  rfl

theorem access_trap (s : Store) (f : Frame) : access ⟨s, f, [.trap]⟩ = none := by
  simp [access, seqAccess, atAccess, show toVal AInstr.trap = none from rfl]

theorem access_final {c : Config} {o : Outcome} (hf : Final c o) : access c = none := by
  obtain ⟨s, f, es⟩ := c
  cases o with
  | returned s' vs => obtain ⟨-, rfl⟩ := hf; exact access_vals s f vs
  | trapped s' => obtain ⟨-, rfl⟩ := hf; exact access_trap s f

/-- The access of `C.fill c` is the access of `c`: labels and frames are entered, not executed. -/
theorem Context.access_fill (C : Context) (c : Config) : access (C.fill c) = access c := by
  induction C generalizing c with
  | hole => rfl
  | label n cont rest outer ih =>
    rw [Context.fill, ih]
    simp [access, seqAccess, atAccess, show ∀ es, toVal (AInstr.label n cont es) = none from
      fun _ => rfl]
  | frame n caller rest outer ih =>
    rw [Context.fill, ih]
    simp [access, seqAccess, atAccess, show ∀ fi es, toVal (AInstr.frame n fi es) = none from
      fun _ _ => rfl]

/-- What a step's computed access asks of a footprint: nothing without an access, else its range
inside `R` (a read) or `W` (a write). -/
def AccessOK (R W : Nat → Nat → Prop) : Option Access → Prop
  | none => True
  | some x => (x.write = false → ∀ a, x.start ≤ a → a < x.start + x.len → R x.mem a) ∧
      (x.write = true → ∀ a, x.start ≤ a → a < x.start + x.len → W x.mem a)

theorem within_of_accessOK {R W : Nat → Nat → Prop} {c : Config} (h : AccessOK R W (access c)) :
    Within R W c := by
  cases hx : access c with
  | none => exact within_of_access_none hx
  | some x => rw [hx] at h; exact within_of_access hx h.1 h.2

@[wasm_access] theorem seqAccess_nil (s : Store) (f : Frame) (vs : List Val) :
    seqAccess s f vs [] = none := by rw [seqAccess]
@[wasm_access] theorem seqAccess_cons_val (s : Store) (f : Frame) (vs : List Val) (v : Val)
    (rest : List AInstr) : seqAccess s f vs (v.instr :: rest) = seqAccess s f (v :: vs) rest := by
  rw [seqAccess, toVal_instr]
@[wasm_access] theorem seqAccess_cons_none {s : Store} {f : Frame} {vs : List Val} {e : AInstr}
    (rest : List AInstr) (h : toVal e = none) :
    seqAccess s f vs (e :: rest) = atAccess s f vs e := by
  rw [seqAccess, h]
@[wasm_access] theorem seqAccess_cons_i32 (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (rest : List AInstr) (h : n < 2 ^ 32) :
    seqAccess s f vs (.plain (.iconst .w32 n) :: rest) =
      seqAccess s f (.i32 (BitVec.ofNat 32 n) :: vs) rest := by
  have : n < 4294967296 := h
  rw [seqAccess]; simp [toVal, Nat.blt_eq, this]
@[wasm_access] theorem seqAccess_cons_i64 (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (rest : List AInstr) (h : n < 2 ^ 64) :
    seqAccess s f vs (.plain (.iconst .w64 n) :: rest) =
      seqAccess s f (.i64 (BitVec.ofNat 64 n) :: vs) rest := by
  have : n < 18446744073709551616 := h
  rw [seqAccess]; simp [toVal, Nat.blt_eq, this]
@[wasm_access] theorem atAccess_label (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (cont : List Instr) (body : List AInstr) :
    atAccess s f vs (.label n cont body) = seqAccess s f [] body := by rw [atAccess]
@[wasm_access] theorem atAccess_frame (s : Store) (f : Frame) (vs : List Val) (n : Nat) (fi : Frame)
    (body : List AInstr) : atAccess s f vs (.frame n fi body) = seqAccess s fi [] body := by
  rw [atAccess]
@[wasm_access] theorem atAccess_plain (s : Store) (f : Frame) (vs : List Val) (i : Instr) :
    atAccess s f vs (.plain i) = instrAccess s f i vs := by rw [atAccess]
@[wasm_access] theorem atAccess_invoke (s : Store) (f : Frame) (vs : List Val) (a : Nat) :
    atAccess s f vs (.invoke a) = none := by unfold atAccess; rfl
@[wasm_access] theorem atAccess_trap (s : Store) (f : Frame) (vs : List Val) :
    atAccess s f vs .trap = none := by unfold atAccess; rfl
@[wasm_access] theorem instrAccess_loadPacked (s : Store) (f : Frame) (w : Width) (p : PackSize)
    (sx : Sx) (m : MemArg) (i : BitVec 32) (vs : List Val) :
    instrAccess s f (.loadPacked w p sx m) (.i32 i :: vs) =
      rangeAccess s f false (i.toNat + m.offset) (p.bits / 8) := by rw [instrAccess]
@[wasm_access] theorem instrAccess_load (s : Store) (f : Frame) (t : NumType) (m : MemArg)
    (i : BitVec 32) (vs : List Val) :
    instrAccess s f (.load t m) (.i32 i :: vs) =
      rangeAccess s f false (i.toNat + m.offset) t.bytes := by rw [instrAccess]
section
variable {s : Store} {f : Frame} {vs : List Val}
-- every non-memory instruction has no access, one lemma per constructor: simp cannot discharge
-- `instrAccess`'s catch-all match side conditions
@[wasm_access] theorem instrAccess_iunop {w} {op} : instrAccess s f (.iunop w op) vs = none := rfl
@[wasm_access] theorem instrAccess_ibinop {w} {op} : instrAccess s f (.ibinop w op) vs = none := rfl
@[wasm_access] theorem instrAccess_itestEqz {w} : instrAccess s f (.itestEqz w) vs = none := rfl
@[wasm_access] theorem instrAccess_irelop {w} {op} : instrAccess s f (.irelop w op) vs = none := rfl
@[wasm_access] theorem instrAccess_funop {w} {op} : instrAccess s f (.funop w op) vs = none := rfl
@[wasm_access] theorem instrAccess_fbinop {w} {op} : instrAccess s f (.fbinop w op) vs = none := rfl
@[wasm_access] theorem instrAccess_frelop {w} {op} : instrAccess s f (.frelop w op) vs = none := rfl
@[wasm_access] theorem instrAccess_cvtop {op} : instrAccess s f (.cvtop op) vs = none := rfl
@[wasm_access] theorem instrAccess_refIsNull : instrAccess s f (.refIsNull) vs = none := rfl
@[wasm_access] theorem instrAccess_refFunc {x} : instrAccess s f (.refFunc x) vs = none := rfl
@[wasm_access] theorem instrAccess_drop : instrAccess s f (.drop) vs = none := rfl
@[wasm_access] theorem instrAccess_select {ts} : instrAccess s f (.select ts) vs = none := rfl
@[wasm_access] theorem instrAccess_localGet {x} : instrAccess s f (.localGet x) vs = none := rfl
@[wasm_access] theorem instrAccess_localSet {x} : instrAccess s f (.localSet x) vs = none := rfl
@[wasm_access] theorem instrAccess_localTee {x} : instrAccess s f (.localTee x) vs = none := rfl
@[wasm_access] theorem instrAccess_globalGet {x} : instrAccess s f (.globalGet x) vs = none := rfl
@[wasm_access] theorem instrAccess_globalSet {x} : instrAccess s f (.globalSet x) vs = none := rfl
@[wasm_access] theorem instrAccess_tableGet {x} : instrAccess s f (.tableGet x) vs = none := rfl
@[wasm_access] theorem instrAccess_tableSet {x} : instrAccess s f (.tableSet x) vs = none := rfl
@[wasm_access] theorem instrAccess_tableSize {x} : instrAccess s f (.tableSize x) vs = none := rfl
@[wasm_access] theorem instrAccess_tableGrow {x} : instrAccess s f (.tableGrow x) vs = none := rfl
@[wasm_access] theorem instrAccess_tableFill {x} : instrAccess s f (.tableFill x) vs = none := rfl
@[wasm_access] theorem instrAccess_tableCopy {x} {y} :
    instrAccess s f (.tableCopy x y) vs = none := rfl
@[wasm_access] theorem instrAccess_tableInit {x} {y} :
    instrAccess s f (.tableInit x y) vs = none := rfl
@[wasm_access] theorem instrAccess_elemDrop {x} : instrAccess s f (.elemDrop x) vs = none := rfl
@[wasm_access] theorem instrAccess_memorySize : instrAccess s f (.memorySize) vs = none := rfl
@[wasm_access] theorem instrAccess_memoryGrow : instrAccess s f (.memoryGrow) vs = none := rfl
@[wasm_access] theorem instrAccess_memoryFill : instrAccess s f (.memoryFill) vs = none := rfl
@[wasm_access] theorem instrAccess_memoryCopy : instrAccess s f (.memoryCopy) vs = none := rfl
@[wasm_access] theorem instrAccess_memoryInit {x} : instrAccess s f (.memoryInit x) vs = none := rfl
@[wasm_access] theorem instrAccess_dataDrop {x} : instrAccess s f (.dataDrop x) vs = none := rfl
@[wasm_access] theorem instrAccess_unreachable : instrAccess s f (.unreachable) vs = none := rfl
@[wasm_access] theorem instrAccess_nop : instrAccess s f (.nop) vs = none := rfl
@[wasm_access] theorem instrAccess_block {bt} {body} :
    instrAccess s f (.block bt body) vs = none := rfl
@[wasm_access] theorem instrAccess_loop {bt} {body} :
    instrAccess s f (.loop bt body) vs = none := rfl
@[wasm_access] theorem instrAccess_if_ {bt} {thn} {els} :
    instrAccess s f (.if_ bt thn els) vs = none := rfl
@[wasm_access] theorem instrAccess_br {l} : instrAccess s f (.br l) vs = none := rfl
@[wasm_access] theorem instrAccess_brIf {l} : instrAccess s f (.brIf l) vs = none := rfl
@[wasm_access] theorem instrAccess_brTable {ls} {l} :
    instrAccess s f (.brTable ls l) vs = none := rfl
@[wasm_access] theorem instrAccess_return_ : instrAccess s f (.return_) vs = none := rfl
@[wasm_access] theorem instrAccess_call {x} : instrAccess s f (.call x) vs = none := rfl
@[wasm_access] theorem instrAccess_callIndirect {x} {y} :
    instrAccess s f (.callIndirect x y) vs = none := rfl
end
attribute [wasm_access] access AccessOK mem0 rangeAccess

/-- `wasm_within [lemmas]` on `Within R W c`: computes `c`'s access (`wasm_access`); no access
closes the goal, a load or store leaves its
range obligation. -/
macro "wasm_within" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine within_of_accessOK ?_
             simp only [wasm_access, wasm_step, $ls,*]))

/-- A finished configuration satisfies every footprint, and `MustW` of any `Q` it satisfies. -/
theorem mustW_final {H : HostSem} {R W : Nat → Nat → Prop} {Q : Outcome → Prop} {c : Config}
    {o : Outcome} (hf : Final c o) (hq : Q o) : MustW H R W Q c := by
  refine ⟨Must.done hf hq, fun c' hs => ?_⟩
  rcases hs.cases_head with rfl | ⟨_, h, _⟩
  · exact within_of_access_none (access_final hf)
  · exact absurd h (no_step_final hf)

/-- The successor of a unique computed step is every `Step` successor. -/
theorem step_eq_of_seq {H : HostSem} {s s' : Store} {f f' : Frame} {l l' : List AInstr}
    {c : Config} (hu : seqUnique s f [] l = true) (hs : seq s f [] l = .step s' f' l')
    (h : Step H ⟨s, f, l⟩ c) : c = ⟨s', f', l'⟩ :=
  step_complete h (by simp only [step, hs]) (by simpa only [uniqueStep] using hu)

theorem mustW_of_seq {H : HostSem} {R W : Nat → Nat → Prop} {Q : Outcome → Prop} {s s' : Store}
    {f f' : Frame} {l l' : List AInstr} (hu : seqUnique s f [] l = true)
    (hs : seq s f [] l = .step s' f' l') (hw : Within R W ⟨s, f, l⟩)
    (h : MustW H R W Q ⟨s', f', l'⟩) : MustW H R W Q ⟨s, f, l⟩ := by
  refine ⟨must_of_seq hu hs h.1, fun c hsteps => ?_⟩
  rcases hsteps.cases_head with rfl | ⟨c₁, h₁, hrest⟩
  · exact hw
  · rw [step_eq_of_seq hu hs h₁] at hrest; exact h.2 c hrest

theorem until_of_seq {H : HostSem} {P Q : Config → Prop} {s s' : Store} {f f' : Frame}
    {l l' : List AInstr} (hu : seqUnique s f [] l = true) (hs : seq s f [] l = .step s' f' l')
    (hp : P ⟨s, f, l⟩) (h : Until H P Q ⟨s', f', l'⟩) : Until H P Q ⟨s, f, l⟩ :=
  .next hp ⟨⟨s', f', l'⟩, step_sound (by simp only [step, hs])⟩ fun c hc =>
    step_eq_of_seq hu hs hc ▸ h

/-- A loop lemma hands over to its exits: `Until` with the footprint as its invariant, then
`MustW` from every exit configuration. -/
theorem mustW_of_until {H : HostSem} {R W : Nat → Nat → Prop} {Q : Outcome → Prop}
    {X : Config → Prop} {c : Config} (hu : Until H (Within R W) X c)
    (hk : ∀ c', X c' → MustW H R W Q c') : MustW H R W Q c := by
  induction hu with
  | done hx => exact hk _ hx
  | @next c hp hex _ ih =>
    refine ⟨Must.next hex fun c' h => (ih c' h).1, fun c' hs => ?_⟩
    rcases hs.cases_head with rfl | ⟨c₁, h₁, hrest⟩
    · exact hp
    · exact (ih c₁ h₁).2 c' hrest

/-- Sequential composition of loop lemmas: `Until` to `X`, then `Until` from every `X`. -/
theorem Until.trans {H : HostSem} {P X Q : Config → Prop} {c : Config} (hu : Until H P X c)
    (hk : ∀ c', X c' → Until H P Q c') : Until H P Q c := by
  induction hu with
  | done hx => exact hk _ hx
  | next hp hex _ ih => exact .next hp hex ih

theorem Until.mono {H : HostSem} {P P' Q Q' : Config → Prop} {c : Config} (hu : Until H P Q c)
    (hp : ∀ c, P c → P' c) (hq : ∀ c, Q c → Q' c) : Until H P' Q' c := by
  induction hu with
  | done hx => exact .done (hq _ hx)
  | next h hex _ ih => exact .next (hp _ h) hex ih

theorem within_fill {R W : Nat → Nat → Prop} (C : Context) {c : Config} (h : Within R W c) :
    Within R W (C.fill c) := by
  cases hx : access c with
  | none => exact within_of_access_none (by rw [C.access_fill, hx])
  | some x =>
    refine within_of_access (x := x) (by rw [C.access_fill, hx]) (fun hw a hlo hhi => ?_)
      (fun hw a hlo hhi => ?_)
    · exact h.1 x.mem a (reads_iff.mpr ⟨x, hx, hw, rfl, hlo, hhi⟩)
    · exact h.2 x.mem a (writes_iff.mpr ⟨x, hx, hw, rfl, hlo, hhi⟩)

theorem mustW_context_seq {H : HostSem} {R W : Nat → Nat → Prop} {Q : Outcome → Prop}
    {s s' : Store} {f f' : Frame} {es es' : List AInstr} (C : Context)
    (hu : seqUnique s f [] es = true) (hs : seq s f [] es = .step s' f' es')
    (hw : Within R W ⟨s, f, es⟩) (hk : MustW H R W Q (C.fill ⟨s', f', es'⟩)) :
    MustW H R W Q (C.fill ⟨s, f, es⟩) := by
  obtain ⟨hu', hs'⟩ := C.seq hu hs
  exact mustW_of_seq hu' hs' (within_fill C hw) hk

theorem until_context_seq {H : HostSem} {R W : Nat → Nat → Prop} {Q : Config → Prop}
    {s s' : Store} {f f' : Frame} {es es' : List AInstr} (C : Context)
    (hu : seqUnique s f [] es = true) (hs : seq s f [] es = .step s' f' es')
    (hw : Within R W ⟨s, f, es⟩) (hk : Until H (Within R W) Q (C.fill ⟨s', f', es'⟩)) :
    Until H (Within R W) Q (C.fill ⟨s, f, es⟩) := by
  obtain ⟨hu', hs'⟩ := C.seq hu hs
  exact until_of_seq hu' hs' (within_fill C hw) hk

open Lean Meta Elab Tactic in
/-- One unique step of `C.fill ⟨s, f, l⟩` under `MustW H R W Q` (`stepLemma` =
`mustW_context_seq`) or `Until H (Within R W) Q` (`until_context_seq`): simp computes
`seq s f [] l` and its uniqueness, the goal moves to the successor, and the step's footprint
`Within R W ⟨s, f, l⟩` comes first as a new goal. -/
def footprintStep (stepLemma : Name) (rw : Lean.Expr → MetaM (Lean.Expr × Lean.Expr))
    (xs : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",") : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let fn := ty.consumeMData.getAppFn
  let args := ty.consumeMData.getAppArgs
  let some cc := args.back? | throwError "footprint step: unexpected goal"
  let (R, W) ← rw ty.consumeMData
  let some (C, c) := cc.consumeMData.app2? ``Context.fill
    | throwError "footprint step: expected `Context.fill`"
  let c ← whnfR c
  let some (s, f, l) := c.app3? ``Config.mk | throwError "footprint step: no literal configuration"
  let stx ← `(tactic| simp only [wasm_step, $xs,*])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let nil ← mkListLit (mkConst ``Val) []
  let (r, _) ← simp (← mkAppM ``seq #[s, f, nil, l]) ctx simprocs
  let out ← instantiateMVars r.expr
  let some (s', f', l') := (← whnfR out).consumeMData.app3? ``Out.step
    | throwError m!"footprint step: the next step is not computed: {out}"
  let hs ← r.getProof
  let hu ← mkFreshExprMVar (← mkEq (← mkAppM ``seqUnique #[s, f, nil, l]) (mkConst ``Bool.true))
  let rest ← evalTacticAt stx hu.mvarId!
  unless rest.isEmpty do throwError "footprint step: uniqueness of the step is not shown"
  let next ← mkFreshExprMVar (mkAppN fn (args.pop.push
    (← mkAppM ``Context.fill #[C, ← mkAppM ``Config.mk #[s', f', l']])))
  let hw ← mkFreshExprMVar (← mkAppM ``Within #[R, W, c])
  g.assign (← mkAppM stepLemma #[C, hu, hs, hw, next])
  replaceMainGoal [hw.mvarId!, next.mvarId!]

open Lean Meta Elab Tactic in
/-- `wasm_cstepw [lemmas]` on `MustW H R W Q (C.fill c)`: one unique step + its footprint goal. -/
elab "wasm_cstepw" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  footprintStep ``mustW_context_seq (fun (ty : Lean.Expr) => do
    let args := ty.getAppArgs
    unless ty.getAppFn.isConstOf ``MustW && args.size == 5 do throwError "wasm_cstepw: no `MustW`"
    pure (args[1]!, args[2]!)) xs

open Lean Meta Elab Tactic in
/-- `wasm_cstepu [lemmas]` on `Until H (Within R W) Q (C.fill c)`: one unique step + its
footprint goal. -/
elab "wasm_cstepu" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  footprintStep ``until_context_seq (fun (ty : Lean.Expr) => do
    let args := ty.getAppArgs
    unless ty.getAppFn.isConstOf ``Until && args.size == 4 do throwError "wasm_cstepu: no `Until`"
    let some (R, W) := args[1]!.consumeMData.app2? ``Within |
      throwError "wasm_cstepu: the invariant is no `Within R W`"
    pure (R, W)) xs

end FVA.Wasm.Exec.Ref
