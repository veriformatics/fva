import FVA.Impl.Exec.Machine
import FVA.Proof.Exec.Chunks
import FVA.Proof.Exec.Det
import FVA.Proof.Exec.Instantiate
import Mathlib.Tactic.Common

/-!
# The machine simulates the reference stepper

`stepN k c` = `k` reference steps. The control stack's layers lift every inner `Ref.step`
(`step_wrap`); each machine step is `k` reference steps between the abstractions
(`step_sim`, contract U26 T1).
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

/-- `k` reference steps. -/
def stepN : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => (Ref.step c).bind (stepN k)

theorem stepN_add (a b : Nat) (c : Config) : stepN (a + b) c = (stepN a c).bind (stepN b) := by
  induction a generalizing c with
  | zero => simp [stepN]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [stepN]
    cases Ref.step c <;> simp [ih]

theorem stepN_one {c c' : Config} (h : Ref.step c = some c') : stepN 1 c = some c' := by
  simp [stepN, h]

/-- `k` reference steps, each from a configuration that is no choice point under policy `fits`. -/
def stepNU (fits : Bool) : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => bif Ref.uniqueStep fits c then (Ref.step c).bind (stepNU fits k) else none

theorem stepNU_add (fits : Bool) (a b : Nat) (c : Config) :
    stepNU fits (a + b) c = (stepNU fits a c).bind (stepNU fits b) := by
  induction a generalizing c with
  | zero => simp [stepNU]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [stepNU]
    cases Ref.uniqueStep fits c <;> cases Ref.step c <;> simp [ih]

theorem stepNU_one {fits : Bool} {c c' : Config} (hu : Ref.uniqueStep fits c = true)
    (h : Ref.step c = some c') : stepNU fits 1 c = some c' := by
  simp [stepNU, hu, h]

theorem stepNU_stepN {fits : Bool} : ∀ {k : Nat} {c c' : Config},
    stepNU fits k c = some c' → stepN k c = some c'
  | 0, _, _, h => h
  | k + 1, c, c', h => by
    simp only [stepNU] at h
    cases hu : Ref.uniqueStep fits c
    · simp [hu] at h
    · simp only [hu, Bool.cond_true] at h
      cases hs : Ref.step c with
      | none => simp [hs] at h
      | some c₁ =>
        simp only [hs, Option.bind_some] at h
        simp only [stepN, hs, Option.bind_some]
        exact stepNU_stepN h

/-- A step from a configuration unique under `fits` is that step under `fits`. -/
theorem stepNU_of_one {fits : Bool} {c c' : Config} (h : stepN 1 c = some c')
    (hu : Ref.uniqueStep fits c = true) : stepNU fits 1 c = some c' := by
  simp only [stepN, Option.bind_eq_some_iff] at h
  obtain ⟨c₁, h₁, h₂⟩ := h
  simp only [Option.some.injEq] at h₂
  subst h₂
  exact stepNU_one hu h₁

theorem uniqueStep_focus {fits : Bool} {S : Store} {f : Frame} {stk : List Val} {i : Instr}
    {rest : List AInstr} (hv : Ref.toVal (.plain i) = none) (ht : i ≠ .throwRef)
    (hu : Ref.instrUnique fits i stk = true) :
    Ref.uniqueStep fits ⟨S, f, vals stk.reverse ++ .plain i :: rest⟩ = true := by
  simp only [Ref.uniqueStep, Ref.seqUnique_vals, List.reverse_reverse, List.append_nil,
    Ref.seqUnique, hv, Ref.atUnique_plain ht, hu]

/-- One step at a plain instruction no policy makes a choice point (`rfl` decides `hv` and `hu`,
`nofun` the `throw_ref` exclusion). -/
theorem stepNU_plain {fits : Bool} {S : Store} {f : Frame} {stk : List Val} {i : Instr}
    {rest : List AInstr} {c' : Config}
    (h : Ref.step ⟨S, f, vals stk.reverse ++ .plain i :: rest⟩ = some c')
    (hv : Ref.toVal (.plain i) = none := by rfl) (ht : i ≠ .throwRef := by nofun)
    (hu : Ref.instrUnique fits i stk = true := by rfl) :
    stepNU fits 1 ⟨S, f, vals stk.reverse ++ .plain i :: rest⟩ = some c' :=
  stepNU_one (uniqueStep_focus hv ht hu) h

/-- One control entry around instructions `es` running in frame `f`. -/
def layer : Ctl → Frame → List AInstr → Frame × List AInstr
  | .label n cont saved rest, f, es => (f, vals saved.reverse ++ [.label n cont es] ++ rest)
  | .frame n caller saved rest, f, es => (caller, vals saved.reverse ++ [.frame n f es] ++ rest)

theorem wrap_cons (c : Ctl) (ctl : List Ctl) (f : Frame) (es : List AInstr) :
    wrap (c :: ctl) f es = wrap ctl (layer c f es).1 (layer c f es).2 := by
  cases c <;> rfl

theorem seq_layer_step {S S' : Store} {f f' : Frame} {es es' : List AInstr} (c : Ctl)
    (h : Ref.seq S f [] es = .step S' f' es') :
    Ref.seq S (layer c f es).1 [] (layer c f es).2 =
      .step S' (layer c f' es').1 (layer c f' es').2 := by
  cases c with
  | label n cont saved rest =>
    simp only [layer, List.append_assoc, Ref.seq_vals, List.reverse_reverse, List.append_nil,
      List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h]
  | frame n caller saved rest =>
    simp only [layer, List.append_assoc, Ref.seq_vals, List.reverse_reverse, List.append_nil,
      List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h]

theorem seq_wrap_step {S S' : Store} {f f' : Frame} {es es' : List AInstr} (ctl : List Ctl)
    (h : Ref.seq S f [] es = .step S' f' es') :
    Ref.seq S (wrap ctl f es).1 [] (wrap ctl f es).2 =
      .step S' (wrap ctl f' es').1 (wrap ctl f' es').2 := by
  induction ctl generalizing f f' es es' with
  | nil => simpa [wrap] using h
  | cons c ctl ih =>
    rw [wrap_cons, wrap_cons]
    exact ih (seq_layer_step c h)

/-- The configuration of instructions `es` in frame `f` under the control stack. -/
def wrapC (S : Store) (ctl : List Ctl) (f : Frame) (es : List AInstr) : Config :=
  ⟨S, (wrap ctl f es).1, (wrap ctl f es).2⟩

theorem step_wrap {S S' : Store} {f f' : Frame} {es es' : List AInstr} (ctl : List Ctl)
    (h : Ref.step ⟨S, f, es⟩ = some ⟨S', f', es'⟩) :
    Ref.step (wrapC S ctl f es) = some (wrapC S' ctl f' es') := by
  simp only [Ref.step] at h ⊢
  split at h
  · next s₁ f₁ es₁ hs =>
    simp only [Option.some.injEq, Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [wrapC, seq_wrap_step ctl hs]
  · contradiction

theorem stepN_wrap {S S' : Store} {f f' : Frame} {es es' : List AInstr} (ctl : List Ctl) (k : Nat)
    (h : stepN k ⟨S, f, es⟩ = some ⟨S', f', es'⟩) :
    stepN k (wrapC S ctl f es) = some (wrapC S' ctl f' es') := by
  induction k generalizing S f es with
  | zero =>
    simp only [stepN, Option.some.injEq, Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    simp only [stepN] at h ⊢
    cases hs : Ref.step ⟨S, f, es⟩ with
    | none => simp [hs] at h
    | some c₁ =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [step_wrap ctl (show Ref.step ⟨S, f, es⟩ = some ⟨c₁.store, c₁.frame, c₁.instrs⟩ from hs)]
      simp only [Option.bind_some]
      exact ih h

theorem abs_eq_wrapC (m : MState) :
    m.abs = wrapC m.store.abs m.ctl m.frame (vals m.stack.reverse ++ m.code) := rfl

theorem seqUnique_layer (fits : Bool) (S : Store) (c : Ctl) (f : Frame) (es : List AInstr) :
    Ref.seqUnique fits S (layer c f es).1 [] (layer c f es).2 = Ref.seqUnique fits S f [] es := by
  cases c with
  | label n cont saved rest =>
    simp only [layer, List.append_assoc, Ref.seqUnique_vals, List.singleton_append,
      Ref.seqUnique, Ref.toVal, Ref.atUnique]
  | frame n caller saved rest =>
    simp only [layer, List.append_assoc, Ref.seqUnique_vals, List.singleton_append,
      Ref.seqUnique, Ref.toVal, Ref.atUnique]

/-- The control stack's layers keep the next redex: uniqueness = the innermost one's. -/
theorem uniqueStep_wrapC (fits : Bool) (S : Store) (ctl : List Ctl) (f : Frame)
    (es : List AInstr) :
    Ref.uniqueStep fits (wrapC S ctl f es) = Ref.uniqueStep fits ⟨S, f, es⟩ := by
  induction ctl generalizing f es with
  | nil => rfl
  | cons c ctl ih =>
    have h := ih (layer c f es).1 (layer c f es).2
    simp only [wrapC, Ref.uniqueStep] at h ⊢
    rw [wrap_cons, h, seqUnique_layer]

theorem stepNU_wrap {fits : Bool} {S S' : Store} {f f' : Frame} {es es' : List AInstr}
    (ctl : List Ctl) (k : Nat) (h : stepNU fits k ⟨S, f, es⟩ = some ⟨S', f', es'⟩) :
    stepNU fits k (wrapC S ctl f es) = some (wrapC S' ctl f' es') := by
  induction k generalizing S f es with
  | zero =>
    simp only [stepNU, Option.some.injEq, Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    simp only [stepNU] at h ⊢
    rw [uniqueStep_wrapC]
    cases hu : Ref.uniqueStep fits ⟨S, f, es⟩
    · simp [hu] at h
    · simp only [hu, Bool.cond_true] at h ⊢
      cases hs : Ref.step ⟨S, f, es⟩ with
      | none => simp [hs] at h
      | some c₁ =>
        rw [hs] at h
        simp only [Option.bind_some] at h
        rw [step_wrap ctl (show Ref.step ⟨S, f, es⟩ = some ⟨c₁.store, c₁.frame, c₁.instrs⟩ from hs)]
        simp only [Option.bind_some]
        exact ih h

/-- Machine step `m → m'` = `k` reference steps between the abstractions, each no choice point
under every policy the first is unique under (contract U27 T5). -/
def Sim (m m' : MState) : Prop :=
  ∃ k, stepN k m.abs = some m'.abs ∧
    ∀ fits, Ref.uniqueStep fits m.abs = true → stepNU fits k m.abs = some m'.abs

theorem Sim.zero {m m' : MState} (h : stepN 0 m.abs = some m'.abs) : Sim m m' :=
  ⟨0, h, fun _ _ => h⟩

theorem Sim.one {m m' : MState} (h : stepN 1 m.abs = some m'.abs) : Sim m m' :=
  ⟨1, h, fun _ hu => stepNU_of_one h hu⟩

theorem Sim.ofU {m m' : MState} {k : Nat} (h : ∀ fits, stepNU fits k m.abs = some m'.abs) :
    Sim m m' :=
  ⟨k, stepNU_stepN (h false), fun fits _ => h fits⟩

theorem Sim.notUnique {m m' : MState} {k : Nat} (h : stepN k m.abs = some m'.abs)
    (hu : ∀ fits, Ref.uniqueStep fits m.abs = false) : Sim m m' :=
  ⟨k, h, fun fits h' => by rw [hu] at h'; cases h'⟩

theorem instrStep_mems {S S' : Store} {f f' : Frame} {i : Instr} {stk stk' : List Val}
    {out : List AInstr} (h : Ref.instrStep S f i stk = some (S', f', stk', out))
    (hs : ∀ t m, i ≠ .store t m) (hp : ∀ w p m, i ≠ .storePacked w p m)
    (hg : i ≠ .memoryGrow) : S'.mems = S.mems := by
  fun_cases Ref.instrStep S f i stk <;>
    simp_all only [Ref.instrStep, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Bool.cond_true, Bool.cond_false, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
      ne_eq, not_false_eq_true, imp_false, not_true_eq_false]
  all_goals first
    | (obtain ⟨_, _, rfl, _⟩ := h; rfl)
    | aesop (add norm simp [Store.setTable])

theorem seq_focus (S : Store) (f : Frame) (stk : List Val) {e : AInstr} (rest : List AInstr)
    (he : Ref.toVal e = none) :
    Ref.seq S f [] (vals stk.reverse ++ e :: rest) = Ref.atInstr S f stk e rest := by
  rw [Ref.seq_vals]
  simp [Ref.seq, he]

theorem step_focus {S S' : Store} {f f' : Frame} {stk : List Val} {e : AInstr}
    {rest es' : List AInstr} (he : Ref.toVal e = none)
    (h : Ref.atInstr S f stk e rest = .step S' f' es') :
    Ref.step ⟨S, f, vals stk.reverse ++ e :: rest⟩ = some ⟨S', f', es'⟩ := by
  simp only [Ref.step]
  rw [seq_focus S f stk rest he, h]

theorem toVal_plain_none {i : Instr} (h : ∀ v : Val, v.instr ≠ .plain i) :
    Ref.toVal (.plain i) = none := by
  cases hv : Ref.toVal (.plain i) with
  | none => rfl
  | some v => exact absurd (Ref.eq_instr_of_toVal hv).symm (h v)

theorem step_instr {S S' : Store} {f f' : Frame} {i : Instr} {stk stk' : List Val}
    {out : List AInstr} (rest : List AInstr)
    (h : Ref.instrStep S f i stk = some (S', f', stk', out)) (hv : Ref.toVal (.plain i) = none) :
    Ref.step ⟨S, f, vals stk.reverse ++ .plain i :: rest⟩ =
      some ⟨S', f', vals stk'.reverse ++ out ++ rest⟩ :=
  step_focus hv (Ref.atInstr_plain_of_step rest h)

/-- A machine step whose innermost configuration takes `k` reference steps, its control stack
unchanged. -/
theorem sim_inner {m m' : MState} {k : Nat}
    (h : stepN k ⟨m.store.abs, m.frame, vals m.stack.reverse ++ m.code⟩ =
      some ⟨m'.store.abs, m'.frame, vals m'.stack.reverse ++ m'.code⟩) (hc : m'.ctl = m.ctl) :
    stepN k m.abs = some m'.abs := by
  rw [abs_eq_wrapC, abs_eq_wrapC, hc]
  exact stepN_wrap _ _ h

theorem seq_layer_final_label {S : Store} {f : Frame} {stk : List Val} (n : Nat)
    (cont : List Instr) (saved : List Val) (rest : List AInstr) :
    Ref.seq S (layer (.label n cont saved rest) f (vals stk.reverse)).1 []
        (layer (.label n cont saved rest) f (vals stk.reverse)).2 =
      .step S f (vals (stk ++ saved).reverse ++ rest) := by
  simp only [layer, List.append_assoc, Ref.seq_vals, List.reverse_reverse, List.append_nil,
    List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, Ref.seq_values,
    Ref.isTrapOnly_vals, Bool.cond_false, List.reverse_append, vals, List.map_append]

theorem seq_layer_final_frame {S : Store} {f : Frame} {stk : List Val} (n : Nat)
    (caller : Frame) (saved : List Val) (rest : List AInstr) (hn : stk.length = n) :
    Ref.seq S (layer (.frame n caller saved rest) f (vals stk.reverse)).1 []
        (layer (.frame n caller saved rest) f (vals stk.reverse)).2 =
      .step S caller (vals (stk ++ saved).reverse ++ rest) := by
  have hb : Nat.beq (vals stk.reverse).length n = true := by
    simp [vals, hn]
  simp only [layer, List.append_assoc, Ref.seq_vals, List.reverse_reverse, List.append_nil,
    List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, Ref.seq_values,
    Ref.isTrapOnly_vals, Bool.cond_false, hb, Bool.cond_true, List.reverse_append, vals,
    List.map_append]

theorem seq_wrap_br {S : Store} {f : Frame} {es : List AInstr} {bvs stk' : List Val}
    {code' : List AInstr} : ∀ (l : Nat) (ctl ctl' : List Ctl),
    Ref.seq S f [] es = .br l bvs → brPop l bvs ctl = some (stk', code', ctl') →
    Ref.seq S (wrap ctl f es).1 [] (wrap ctl f es).2 =
      .step S (wrap ctl' f (vals stk'.reverse ++ code')).1
        (wrap ctl' f (vals stk'.reverse ++ code')).2
  | 0, .label n cont saved rest :: ctl, ctl', h, hb => by
    simp only [brPop] at hb
    cases hlt : Nat.blt bvs.length n
    · simp only [hlt, Bool.cond_false, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      rw [wrap_cons]
      apply seq_wrap_step
      simp only [layer, List.append_assoc, Ref.seq_vals, List.reverse_reverse, List.append_nil,
        List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h, hlt, Bool.cond_false,
        List.reverse_append, vals, List.map_append]
    · simp [hlt] at hb
  | l + 1, .label n cont saved rest :: ctl, ctl', h, hb => by
    simp only [brPop] at hb
    rw [wrap_cons]
    apply seq_wrap_br l ctl ctl' _ hb
    simp only [layer, List.append_assoc, Ref.seq_vals, List.singleton_append, Ref.seq, Ref.toVal,
      Ref.atInstr, h]
  | _, .frame .. :: _, _, _, hb => by simp [brPop] at hb
  | _, [], _, _, hb => by simp [brPop] at hb

theorem seq_wrap_ret {S : Store} {f : Frame} {es : List AInstr} {bvs stk' : List Val}
    {code' : List AInstr} {f' : Frame} : ∀ (ctl ctl' : List Ctl),
    Ref.seq S f [] es = .ret bvs → retPop bvs ctl = some (f', stk', code', ctl') →
    Ref.seq S (wrap ctl f es).1 [] (wrap ctl f es).2 =
      .step S (wrap ctl' f' (vals stk'.reverse ++ code')).1
        (wrap ctl' f' (vals stk'.reverse ++ code')).2
  | .label n cont saved rest :: ctl, ctl', h, hb => by
    simp only [retPop] at hb
    rw [wrap_cons]
    apply seq_wrap_ret ctl ctl' _ hb
    simp only [layer, List.append_assoc, Ref.seq_vals, List.singleton_append, Ref.seq, Ref.toVal,
      Ref.atInstr, h]
  | .frame n caller saved rest :: ctl, ctl', h, hb => by
    simp only [retPop] at hb
    cases hlt : Nat.blt bvs.length n
    · simp only [hlt, Bool.cond_false, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
      rw [wrap_cons]
      apply seq_wrap_step
      simp only [layer, List.append_assoc, Ref.seq_vals, List.reverse_reverse, List.append_nil,
        List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h, hlt, Bool.cond_false,
        List.reverse_append, vals, List.map_append]
    · simp [hlt] at hb
  | [], _, _, hb => by simp [retPop] at hb

/-- The instructions just outside control entry `c` once its body is `[trap]`. -/
def trapOut1 : Ctl → List AInstr
  | .label _ _ saved rest | .frame _ _ saved rest => vals saved.reverse ++ .trap :: rest

theorem seq_layer_trap (S : Store) (f : Frame) (c : Ctl) :
    Ref.seq S (layer c f [.trap]).1 [] (layer c f [.trap]).2 =
      .step S (layer c f [.trap]).1 (trapOut1 c) := by
  cases c <;>
    simp only [layer, trapOut1, List.append_assoc, Ref.seq_vals, List.singleton_append, Ref.seq,
      Ref.toVal, Ref.atInstr, Ref.isTrapOnly, List.isEmpty_nil, Bool.and_self, Bool.cond_true,
      List.reverse_reverse, List.append_nil]

theorem step_layer_trap (S : Store) (c : Ctl) (ctl : List Ctl) (f : Frame) :
    Ref.step (wrapC S (c :: ctl) f [.trap]) =
      some (wrapC S ctl (layer c f [.trap]).1 (trapOut1 c)) := by
  simp only [wrapC, wrap_cons, Ref.step, seq_wrap_step ctl (seq_layer_trap S f c)]

theorem step_inner_trap (S : Store) (f : Frame) {stk : List Val} {rest : List AInstr}
    (h0 : ¬ (stk = [] ∧ rest = [])) :
    Ref.step ⟨S, f, vals stk.reverse ++ .trap :: rest⟩ = some ⟨S, f, [.trap]⟩ := by
  apply step_focus rfl
  have hne : (stk.isEmpty && rest.isEmpty) = false := by
    cases stk <;> cases rest <;> simp_all
  simp [Ref.atInstr, hne]

theorem trap_collapse (S : Store) : ∀ (ctl : List Ctl) (f : Frame) (stk : List Val)
    (rest : List AInstr),
    ∃ k, stepN k (wrapC S ctl f (vals stk.reverse ++ .trap :: rest)) =
      some ⟨S, outerFrame ctl f, [.trap]⟩
  | ctl, f, stk, rest => by
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, stepN k₀ (wrapC S ctl f (vals stk.reverse ++ .trap :: rest)) =
        some (wrapC S ctl f [.trap]) := by
      by_cases h0 : stk = [] ∧ rest = []
      · obtain ⟨rfl, rfl⟩ := h0
        exact ⟨0, rfl⟩
      · exact ⟨1, stepN_one (step_wrap ctl (step_inner_trap S f h0))⟩
    match ctl with
    | [] => exact ⟨k₀, hk₀⟩
    | c :: ctl' =>
      have hc : ∃ k, stepN k (wrapC S ctl' (layer c f [.trap]).1 (trapOut1 c)) =
          some ⟨S, outerFrame (c :: ctl') f, [.trap]⟩ := by
        cases c with
        | label n cont saved rest' => exact trap_collapse S ctl' f saved rest'
        | frame n caller saved rest' => exact trap_collapse S ctl' caller saved rest'
      obtain ⟨k, hk⟩ := hc
      refine ⟨k₀ + (1 + k), ?_⟩
      rw [stepN_add, hk₀, Option.bind_some, stepN_add, stepN_one (step_layer_trap S c ctl' f),
        Option.bind_some, hk]

/-! ## Store abstraction -/

/-- Every memory satisfies the machine memory invariant. -/
def MStore.Inv (s : MStore) : Prop := ∀ mm ∈ s.mems, mm.Inv

/-- The machine invariant: every memory's trie well formed, covering, zero past its size. -/
def MState.Inv (m : MState) : Prop := m.store.Inv

theorem MStore.abs_mems (s : MStore) : s.abs.mems = s.mems.map MMem.abs := rfl

theorem mem0_abs (m : MState) :
    Ref.mem0 m.store.abs m.frame = m.mem0.map fun am => (am.1, am.2.abs) := by
  simp only [Ref.mem0, MState.mem0, MStore.abs_mems]
  cases m.frame.inst.mems[0]? with
  | none => rfl
  | some a =>
    simp only [List.getElem?_map, Option.map_map]
    rfl

theorem setMem_abs (m : MState) (a : Nat) (mm : MMem) :
    (m.setMem a mm).store.abs = m.store.abs.setMem a mm.abs := by
  simp [MState.setMem, MStore.abs, Store.setMem, List.map_set]

theorem setMem_inv {m : MState} (hi : m.Inv) {a : Nat} {mm : MMem} (h : mm.Inv) :
    (m.setMem a mm).Inv := by
  intro x hx
  simp only [MState.setMem] at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact hi x hx
  · exact h

theorem mem0_inv {m : MState} (hi : m.Inv) {a : Nat} {mm : MMem} (h : m.mem0 = some (a, mm)) :
    mm.Inv := by
  simp only [MState.mem0] at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, hx, rfl, rfl⟩ := h
    exact hi x (List.mem_of_getElem? hx)
  · contradiction

theorem vals_cons_reverse (v : Val) (stk : List Val) :
    vals (v :: stk).reverse = vals stk.reverse ++ [v.instr] := by
  simp [vals]

theorem le_of_blt_false {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  by_contra hh
  rw [MMem.blt_true (by omega)] at h
  contradiction

theorem instrStep_store_shape {S : Store} {f : Frame} {t : NumType} {ma : MemArg}
    {stk : List Val} {r : Store × Frame × List Val × List AInstr}
    (h : Ref.instrStep S f (.store t ma) stk = some r) :
    ∃ v x rest, stk = v :: .i32 x :: rest := by
  match stk, h with
  | v :: .i32 x :: rest, _ => exact ⟨v, x, rest, rfl⟩
  | [], h | [_], h => simp [Ref.instrStep] at h
  | _ :: .i64 _ :: _, h | _ :: .f32 _ :: _, h | _ :: .f64 _ :: _, h | _ :: .ref _ :: _, h =>
    simp [Ref.instrStep] at h

theorem instrStep_storePacked_shape {S : Store} {f : Frame} {w : Width} {p : PackSize}
    {ma : MemArg} {stk : List Val} {r : Store × Frame × List Val × List AInstr}
    (h : Ref.instrStep S f (.storePacked w p ma) stk = some r) :
    ∃ v x rest, stk = v :: .i32 x :: rest := by
  match stk, h with
  | v :: .i32 x :: rest, _ => exact ⟨v, x, rest, rfl⟩
  | [], h | [_], h => simp [Ref.instrStep] at h
  | _ :: .i64 _ :: _, h | _ :: .f32 _ :: _, h | _ :: .f64 _ :: _, h | _ :: .ref _ :: _, h =>
    simp [Ref.instrStep] at h

theorem instrStep_grow_shape {S : Store} {f : Frame} {stk : List Val}
    {r : Store × Frame × List Val × List AInstr}
    (h : Ref.instrStep S f .memoryGrow stk = some r) : ∃ n rest, stk = .i32 n :: rest := by
  match stk, h with
  | .i32 n :: rest, _ => exact ⟨n, rest, rfl⟩
  | [], h => simp [Ref.instrStep] at h
  | .i64 _ :: _, h | .f32 _ :: _, h | .f64 _ :: _, h | .ref _ :: _, h => simp [Ref.instrStep] at h

theorem instrStep_load {S : Store} {f : Frame} {t : NumType} {ma : MemArg} {x : BitVec 32}
    {stk : List Val} {a : Nat} {mem : MemInst} (hm : Ref.mem0 S f = some (a, mem)) :
    Ref.instrStep S f (.load t ma) (.i32 x :: stk) = some (S, f, stk,
      bif Nat.blt mem.size (x.toNat + ma.offset + t.bytes) then [.trap]
      else [(t.val (mem.read (x.toNat + ma.offset) t.bytes)).instr]) := by
  simp only [Ref.instrStep, hm, Option.map_some]
  cases Nat.blt mem.size (x.toNat + ma.offset + t.bytes) <;> rfl

theorem instrStep_loadPacked {S : Store} {f : Frame} {w : Width} {p : PackSize} {sx : Sx}
    {ma : MemArg} {x : BitVec 32} {stk : List Val} {a : Nat} {mem : MemInst}
    (hm : Ref.mem0 S f = some (a, mem)) :
    Ref.instrStep S f (.loadPacked w p sx ma) (.i32 x :: stk) = some (S, f, stk,
      bif Nat.blt mem.size (x.toNat + ma.offset + p.bits / 8) then [.trap]
      else [(packedVal w p.bits sx (mem.read (x.toNat + ma.offset) (p.bits / 8))).instr]) := by
  simp only [Ref.instrStep, hm, Option.map_some]
  cases Nat.blt mem.size (x.toNat + ma.offset + p.bits / 8) <;> rfl

theorem instrStep_store {S : Store} {f : Frame} {t : NumType} {ma : MemArg} {x : BitVec 32}
    {v : Val} {c : Nat} {stk : List Val} {a : Nat} {mem : MemInst}
    (hm : Ref.mem0 S f = some (a, mem)) (hv : v.numBits t = some c) :
    Ref.instrStep S f (.store t ma) (v :: .i32 x :: stk) =
      bif Nat.blt mem.size (x.toNat + ma.offset + t.bytes) then some (S, f, stk, [.trap])
      else some (S.setMem a (mem.write (x.toNat + ma.offset) t.bytes c), f, stk, []) := by
  simp only [Ref.instrStep, hm, hv]

theorem instrStep_storePacked {S : Store} {f : Frame} {w : Width} {p : PackSize}
    {ma : MemArg} {x : BitVec 32} {v : Val} {c : Nat} {stk : List Val} {a : Nat}
    {mem : MemInst} (hm : Ref.mem0 S f = some (a, mem)) (hv : v.intBits w = some c) :
    Ref.instrStep S f (.storePacked w p ma) (v :: .i32 x :: stk) =
      bif Nat.blt mem.size (x.toNat + ma.offset + p.bits / 8) then some (S, f, stk, [.trap])
      else some (S.setMem a (mem.write (x.toNat + ma.offset) (p.bits / 8) c), f, stk, []) := by
  simp only [Ref.instrStep, hm, hv]

theorem instrStep_grow {S : Store} {f : Frame} {n : BitVec 32} {stk : List Val} {a : Nat}
    {mem : MemInst} (hm : Ref.mem0 S f = some (a, mem)) :
    Ref.instrStep S f .memoryGrow (.i32 n :: stk) = some (match mem.grow n.toNat with
      | some mem' => (S.setMem a mem', f, stk, [vi32 mem.pages])
      | none => (S, f, stk, [(Val.i32 (BitVec.ofInt 32 (-1))).instr])) := by
  simp only [Ref.instrStep, hm, Option.map_some]
  cases mem.grow n.toNat <;> rfl

theorem mem0_abs_some {m : MState} {a : Nat} {mm : MMem} (h : m.mem0 = some (a, mm)) :
    Ref.mem0 m.store.abs m.frame = some (a, mm.abs) := by
  rw [mem0_abs, h]; rfl

theorem abs_size (mm : MMem) : mm.abs.size = mm.size := rfl

/-- A machine step that is one reference step of the innermost configuration, control stack
unchanged. -/
theorem sim_one {m m' : MState} (hc : m'.ctl = m.ctl)
    (h : Ref.step ⟨m.store.abs, m.frame, vals m.stack.reverse ++ m.code⟩ =
      some ⟨m'.store.abs, m'.frame, vals m'.stack.reverse ++ m'.code⟩) :
    Sim m m' := Sim.one (sim_inner (stepN_one h) hc)

theorem write_cover {mm : MMem} (hi : mm.Inv) {ea k : Nat} (h : ¬ mm.size < ea + k) :
    ea + k ≤ 2 ^ (mm.depth + W) := by
  have := hi.2.1
  simp only [MMem.Cover, MMem.size] at this h
  omega

theorem sim_write {m : MState} (hi : m.Inv) {a : Nat} {mm : MMem} (hm : m.mem0 = some (a, mm))
    {ea k c : Nat} (hb : ¬ mm.size < ea + k) :
    (m.setMem a (mm.write ea k c)).Inv ∧
      (m.setMem a (mm.write ea k c)).store.abs = m.store.abs.setMem a (mm.abs.write ea k c) := by
  have hmi := mem0_inv hi hm
  refine ⟨setMem_inv hi (MMem.write_inv hmi (by omega) c), ?_⟩
  rw [setMem_abs, MMem.abs_write hmi.1 (write_cover hmi hb)]

theorem sim_store {m m' : MState} {t : NumType} {ma : MemArg} {v : Val} {x : BitVec 32}
    {stk : List Val} {rest : List AInstr} {a : Nat} {mm : MMem} {c : Nat} (hi : m.Inv)
    (hc : m.code = .plain (.store t ma) :: rest) (hv : Ref.toVal (.plain (.store t ma)) = none)
    (hstk : m.stack = v :: .i32 x :: stk) (hm : m.mem0 = some (a, mm)) (hnb : v.numBits t = some c)
    (h : (bif Nat.blt mm.size (x.toNat + ma.offset + t.bytes) then some (m.cont stk [.trap] rest)
      else some ((m.setMem a (mm.write (x.toNat + ma.offset) t.bytes c)).cont stk [] rest)) =
        some m') : m'.Inv ∧ Sim m m' := by
  have hst := instrStep_store (stk := stk) (x := x) (ma := ma) (mem0_abs_some hm) hnb
  rw [abs_size, ← hstk] at hst
  cases hb : Nat.blt mm.size (x.toNat + ma.offset + t.bytes)
  · simp only [hb, Bool.cond_false, Option.some.injEq] at h hst
    subst h
    obtain ⟨hinv, habs⟩ := sim_write hi hm (Nat.not_lt.mpr (le_of_blt_false hb))
    refine ⟨hinv, sim_one rfl ?_⟩
    rw [hc]
    have := step_instr rest hst hv
    simp only [MState.cont] at this ⊢
    rw [habs]
    simpa [MState.setMem, List.append_assoc] using this
  · simp only [hb, Bool.cond_true, Option.some.injEq] at h hst
    subst h
    refine ⟨hi, sim_one rfl ?_⟩
    rw [hc]
    have := step_instr rest hst hv
    simpa [MState.cont, List.append_assoc] using this

theorem sim_storePacked {m m' : MState} {w : Width} {p : PackSize} {ma : MemArg} {v : Val}
    {x : BitVec 32} {stk : List Val} {rest : List AInstr} {a : Nat} {mm : MMem} {c : Nat}
    (hi : m.Inv) (hc : m.code = .plain (.storePacked w p ma) :: rest)
    (hv : Ref.toVal (.plain (.storePacked w p ma)) = none)
    (hstk : m.stack = v :: .i32 x :: stk) (hm : m.mem0 = some (a, mm)) (hnb : v.intBits w = some c)
    (h : (bif Nat.blt mm.size (x.toNat + ma.offset + p.bits / 8) then
        some (m.cont stk [.trap] rest)
      else some ((m.setMem a (mm.write (x.toNat + ma.offset) (p.bits / 8) c)).cont stk [] rest)) =
        some m') : m'.Inv ∧ Sim m m' := by
  have hst := instrStep_storePacked (stk := stk) (x := x) (ma := ma) (p := p)
    (mem0_abs_some hm) hnb
  rw [abs_size, ← hstk] at hst
  cases hb : Nat.blt mm.size (x.toNat + ma.offset + p.bits / 8)
  · simp only [hb, Bool.cond_false, Option.some.injEq] at h hst
    subst h
    obtain ⟨hinv, habs⟩ := sim_write hi hm (Nat.not_lt.mpr (le_of_blt_false hb))
    refine ⟨hinv, sim_one rfl ?_⟩
    rw [hc]
    have := step_instr rest hst hv
    simp only [MState.cont] at this ⊢
    rw [habs]
    simpa [MState.setMem, List.append_assoc] using this
  · simp only [hb, Bool.cond_true, Option.some.injEq] at h hst
    subst h
    refine ⟨hi, sim_one rfl ?_⟩
    rw [hc]
    have := step_instr rest hst hv
    simpa [MState.cont, List.append_assoc] using this

theorem setMem_self {S : Store} {a : Nat} {x : MemInst} (h : S.mems[a]? = some x) :
    S.setMem a x = S := by
  obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp h
  simp only [Store.setMem]
  rw [← hx, List.set_getElem_self hlt]

theorem setMem_setMem (S : Store) (a : Nat) (x y : MemInst) :
    (S.setMem a x).setMem a y = S.setMem a y := by
  simp [Store.setMem]

theorem mems_setMem {S : Store} {a : Nat} {x y : MemInst} (h : S.mems[a]? = some x) :
    (S.setMem a y).mems[a]? = some y := by
  simp only [Store.setMem]
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1

theorem instrStep_fill {S : Store} {f : Frame} {n d : BitVec 32} {v : Val} {stk : List Val}
    {a : Nat} {mem : MemInst} (hm : Ref.mem0 S f = some (a, mem)) :
    Ref.instrStep S f .memoryFill (.i32 n :: v :: .i32 d :: stk) = some
      (bif Nat.blt mem.size (d.toNat + n.toNat) then (S, f, stk, [.trap])
      else bif Nat.beq n.toNat 0 then (S, f, stk, [])
      else (S, f, stk, [(Val.i32 d).instr, v.instr, .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
        vi32 (d.toNat + 1), v.instr, vi32 (n.toNat - 1), .plain .memoryFill])) := by
  simp only [Ref.instrStep, hm, Option.map_some]

theorem mem0_of {S : Store} {f : Frame} {a : Nat} {x : MemInst} (hf : f.inst.mems[0]? = some a)
    (hS : S.mems[a]? = some x) : Ref.mem0 S f = some (a, x) := by
  simp [Ref.mem0, hf, hS]

theorem fill_loop {fits : Bool}
    {f : Frame} {a : Nat} (hfa : f.inst.mems[0]? = some a) {v : Val} {c : Nat}
    (hc : v.intBits .w32 = some c) (stk : List Val) (rest : List AInstr) :
    ∀ (k : Nat) (S : Store) (mm : MMem) (d n : BitVec 32), n.toNat = k → mm.Inv →
      S.mems[a]? = some mm.abs → d.toNat + k ≤ mm.size →
      stepNU fits (2 * k + 1) ⟨S, f, vals (.i32 n :: v :: .i32 d :: stk).reverse ++
          .plain .memoryFill :: rest⟩ =
        some ⟨S.setMem a (mm.fill d.toNat k (c % 256)).abs, f, vals stk.reverse ++ rest⟩
  | 0, S, mm, d, n, hn, hmi, hS, hb => by
    have hf := instrStep_fill (n := n) (v := v) (d := d) (stk := stk) (mem0_of hfa hS)
    rw [abs_size, MMem.blt_false (by omega), hn] at hf
    simp only [Bool.cond_false, Nat.beq_refl, Bool.cond_true] at hf
    have hfill : mm.fill d.toNat 0 (c % 256) = mm := rfl
    rw [hfill, setMem_self hS]
    exact stepNU_plain (by simpa using step_instr rest hf rfl)
  | k + 1, S, mm, d, n, hn, hmi, hS, hb => by
    have hsz : mm.size ≤ 2 ^ 32 := by
      have := hmi.2.2.2; simp only [MMem.size]; omega
    have hf := instrStep_fill (n := n) (v := v) (d := d) (stk := stk) (mem0_of hfa hS)
    rw [abs_size, MMem.blt_false (by omega), hn] at hf
    simp only [Bool.cond_false, show Nat.beq (k + 1) 0 = false from rfl] at hf
    have h1 := step_instr rest hf rfl
    have hsp := instrStep_storePacked (S := S) (f := f) (w := .w32) (p := .p8) (ma := ⟨0, 0⟩)
      (x := d) (v := v) (c := c) (stk := stk) (mem0_of hfa hS) hc
    rw [abs_size, MMem.blt_false (by simp [PackSize.bits]; omega)] at hsp
    simp only [Bool.cond_false, Nat.add_zero, PackSize.bits, Nat.reduceDiv] at hsp
    have h2 := step_instr
      ([vi32 (d.toNat + 1), v.instr, vi32 (k + 1 - 1), .plain .memoryFill] ++ rest)
      hsp rfl
    have hwc : d.toNat + 1 ≤ 2 ^ (mm.depth + W) := by
      have := hmi.2.1; simp only [MMem.Cover] at this; omega
    have hmi1 : (mm.write d.toNat 1 c).Inv := MMem.write_inv hmi (by omega) c
    have hS1 : (S.setMem a (mm.abs.write d.toNat 1 c)).mems[a]? =
        some (mm.write d.toNat 1 c).abs := by
      rw [MMem.abs_write hmi.1 (by simpa using hwc)]
      exact mems_setMem hS
    have hd1 : (BitVec.ofNat 32 (d.toNat + 1)).toNat + k ≤ (mm.write d.toNat 1 c).size := by
      have hsz1 : (mm.write d.toNat 1 c).size = mm.size := by
        simp only [MMem.size, (MMem.write_fields mm d.toNat 1 c).1]
      rw [hsz1, BitVec.toNat_ofNat]
      have := Nat.mod_le (d.toNat + 1) (2 ^ 32)
      omega
    have ih := fill_loop (fits := fits) hfa hc stk rest k (S.setMem a (mm.abs.write d.toNat 1 c))
      (mm.write d.toNat 1 c)
      (BitVec.ofNat 32 (d.toNat + 1)) (BitVec.ofNat 32 k)
      (by rw [BitVec.toNat_ofNat]; omega) hmi1 hS1 hd1
    have heq : (mm.write d.toNat 1 c).fill (BitVec.ofNat 32 (d.toNat + 1)).toNat k (c % 256) =
        mm.fill d.toNat (k + 1) (c % 256) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rfl
      · have hlt : d.toNat + 1 < 2 ^ 32 := by omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
        rfl
    have e1 : Ref.step ⟨S, f, vals (.i32 n :: v :: .i32 d :: stk).reverse ++
        .plain .memoryFill :: rest⟩ = some ⟨S, f, vals (v :: .i32 d :: stk).reverse ++
          .plain (.storePacked .w32 .p8 ⟨0, 0⟩) ::
          ([vi32 (d.toNat + 1), v.instr, vi32 (k + 1 - 1), .plain .memoryFill] ++ rest)⟩ := by
      rw [h1]; simp [vals]
    have e2 : Ref.step ⟨S, f, vals (v :: .i32 d :: stk).reverse ++
        .plain (.storePacked .w32 .p8 ⟨0, 0⟩) ::
          ([vi32 (d.toNat + 1), v.instr, vi32 (k + 1 - 1), .plain .memoryFill] ++ rest)⟩ =
        some ⟨S.setMem a (mm.abs.write d.toNat 1 c), f, vals (.i32 (BitVec.ofNat 32 k) :: v ::
          .i32 (BitVec.ofNat 32 (d.toNat + 1)) :: stk).reverse ++ .plain .memoryFill :: rest⟩ := by
      rw [h2]; simp [vals, vi32]
    rw [show 2 * (k + 1) + 1 = 1 + (1 + (2 * k + 1)) by ring, stepNU_add, stepNU_plain e1,
      Option.bind_some, stepNU_add, stepNU_plain e2, Option.bind_some, ih, setMem_setMem, heq]

theorem instrStep_copy {S : Store} {f : Frame} {n s d : BitVec 32} {stk : List Val} {a : Nat}
    {mem : MemInst} (hm : Ref.mem0 S f = some (a, mem)) :
    Ref.instrStep S f .memoryCopy (.i32 n :: .i32 s :: .i32 d :: stk) = some
      (bif Nat.blt mem.size (s.toNat + n.toNat) || Nat.blt mem.size (d.toNat + n.toNat) then
        (S, f, stk, [.trap])
      else bif Nat.beq n.toNat 0 then (S, f, stk, [])
      else bif Nat.ble d.toNat s.toNat then
        (S, f, stk, [(Val.i32 d).instr, (Val.i32 s).instr,
          .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
          vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (n.toNat - 1), .plain .memoryCopy])
      else (S, f, stk, [vi32 (d.toNat + n.toNat - 1), vi32 (s.toNat + n.toNat - 1),
          .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
          (Val.i32 d).instr, (Val.i32 s).instr, vi32 (n.toNat - 1), .plain .memoryCopy])) := by
  simp only [Ref.instrStep, hm, Option.map_some]

/-- One byte moved by the stepper: `loadPacked` of the byte at `src`, then `storePacked` at
`dst`, both `i32` addresses below `2^32`. -/
theorem move_byte {fits : Bool}
    {S : Store} {f : Frame} {a : Nat} (hfa : f.inst.mems[0]? = some a)
    {mm : MMem} (hmi : mm.Inv) (hS : S.mems[a]? = some mm.abs) {dst src : BitVec 32}
    (hd : dst.toNat + 1 ≤ mm.size) (hs : src.toNat + 1 ≤ mm.size) (stk : List Val)
    (rest : List AInstr) :
    stepNU fits 2 ⟨S, f, vals stk.reverse ++ [(Val.i32 dst).instr, (Val.i32 src).instr,
        .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ++ rest⟩ =
      some ⟨S.setMem a (mm.write dst.toNat 1 (mm.byte src.toNat)).abs, f,
        vals stk.reverse ++ rest⟩ := by
  have hm := mem0_of hfa hS
  have hl := instrStep_loadPacked (w := .w32) (p := .p8) (sx := .u) (ma := ⟨0, 0⟩) (x := src)
    (stk := .i32 dst :: stk) hm
  rw [abs_size, MMem.blt_false (by simp [PackSize.bits]; omega)] at hl
  simp only [Bool.cond_false, Nat.add_zero, PackSize.bits, Nat.reduceDiv, MMem.abs_read] at hl
  have hbyte : mm.read src.toNat 1 = mm.byte src.toNat := by simp [MMem.read]
  rw [hbyte] at hl
  have hb := MMem.byte_lt mm src.toNat
  have hsp := instrStep_storePacked (S := S) (f := f) (w := .w32) (p := .p8) (ma := ⟨0, 0⟩)
    (x := dst) (v := .i32 (BitVec.ofNat 32 (mm.byte src.toNat))) (c := mm.byte src.toNat)
    (stk := stk) hm (by simp [Val.intBits]; omega)
  rw [abs_size, MMem.blt_false (by simp [PackSize.bits]; omega)] at hsp
  simp only [Bool.cond_false, Nat.add_zero, PackSize.bits, Nat.reduceDiv] at hsp
  have hwc : dst.toNat + 1 ≤ 2 ^ (mm.depth + W) := by
    have := hmi.2.1; simp only [MMem.Cover] at this; omega
  have e1 : Ref.step ⟨S, f, vals stk.reverse ++ [(Val.i32 dst).instr, (Val.i32 src).instr,
        .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ++ rest⟩ =
      some ⟨S, f, vals (.i32 (BitVec.ofNat 32 (mm.byte src.toNat)) :: .i32 dst :: stk).reverse ++
        .plain (.storePacked .w32 .p8 ⟨0, 0⟩) :: rest⟩ := by
    have := step_instr (.plain (.storePacked .w32 .p8 ⟨0, 0⟩) :: rest) hl rfl
    simp only [packedVal] at this
    simpa [vals] using this
  have e2 := step_instr rest hsp rfl
  have hu1 : Ref.uniqueStep fits ⟨S, f, vals stk.reverse ++ [(Val.i32 dst).instr,
      (Val.i32 src).instr, .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩),
      .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ++ rest⟩ = true := by
    have := uniqueStep_focus (fits := fits) (S := S) (f := f) (stk := .i32 src :: .i32 dst :: stk)
      (i := .loadPacked .w32 .p8 .u ⟨0, 0⟩) (rest := .plain (.storePacked .w32 .p8 ⟨0, 0⟩) :: rest)
      rfl nofun rfl
    simpa [vals] using this
  rw [show (2 : Nat) = 1 + 1 by rfl, stepNU_add, stepNU_one hu1 e1, Option.bind_some,
    stepNU_plain e2, MMem.abs_write hmi.1 (by simpa using hwc)]
  simp

theorem write1_eq_writeBytes (mm : MMem) (d b : Nat) (hb : b < 256) (bs : List Nat) :
    (mm.write d 1 b).writeBytes (d + 1) bs = mm.writeBytes d (b :: bs) := by
  simp only [MMem.write, MMem.writeBytes, Nat.mod_eq_of_lt hb]

theorem copy_up_loop {fits : Bool}
    {f : Frame} {a : Nat} (hfa : f.inst.mems[0]? = some a) (stk : List Val)
    (rest : List AInstr) :
    ∀ (k : Nat) (S : Store) (mm : MMem) (d s n : BitVec 32) (src : List Nat), n.toNat = k →
      mm.Inv → S.mems[a]? = some mm.abs → (k = 0 ∨ d.toNat ≤ s.toNat) →
      s.toNat + k ≤ mm.size → d.toNat + k ≤ mm.size → src.length = k →
      (∀ i < k, mm.byte (s.toNat + i) = src.getD i 0) → (∀ b ∈ src, b < 256) →
      stepNU fits (3 * k + 1) ⟨S, f, vals (.i32 n :: .i32 s :: .i32 d :: stk).reverse ++
          .plain .memoryCopy :: rest⟩ =
        some ⟨S.setMem a (mm.writeBytes d.toNat src).abs, f, vals stk.reverse ++ rest⟩
  | 0, S, mm, d, s, n, src, hn, hmi, hS, _, hs, hd, hl, _, _ => by
    have hc := instrStep_copy (n := n) (s := s) (d := d) (stk := stk) (mem0_of hfa hS)
    rw [abs_size, MMem.blt_false (by omega), MMem.blt_false (by omega), hn] at hc
    simp only [Bool.or_false, Bool.cond_false, Nat.beq_refl, Bool.cond_true] at hc
    rw [List.length_eq_zero_iff.mp hl]
    simp only [MMem.writeBytes]
    rw [setMem_self hS]
    exact stepNU_plain (by simpa using step_instr rest hc rfl)
  | k + 1, S, mm, d, s, n, src, hn, hmi, hS, hds, hs, hd, hl, hsrc, hlt => by
    have hsz : mm.size ≤ 2 ^ 32 := by
      have := hmi.2.2.2; simp only [MMem.size]; omega
    have hds' : d.toNat ≤ s.toNat := by omega
    obtain ⟨b, tail, rfl⟩ : ∃ b tail, src = b :: tail := by
      cases src with
      | nil => simp at hl
      | cons b tail => exact ⟨b, tail, rfl⟩
    have hb0 : mm.byte s.toNat = b := by simpa using hsrc 0 (by omega)
    have hc := instrStep_copy (n := n) (s := s) (d := d) (stk := stk) (mem0_of hfa hS)
    rw [abs_size, MMem.blt_false (by omega), MMem.blt_false (by omega), hn] at hc
    simp only [Bool.or_false, Bool.cond_false, show Nat.beq (k + 1) 0 = false from rfl,
      Nat.ble_eq_true_of_le hds', Bool.cond_true] at hc
    have e1 : Ref.step ⟨S, f, vals (.i32 n :: .i32 s :: .i32 d :: stk).reverse ++
        .plain .memoryCopy :: rest⟩ = some ⟨S, f, vals stk.reverse ++ [(Val.i32 d).instr,
          (Val.i32 s).instr, .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩),
          .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ++
          ([vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (k + 1 - 1), .plain .memoryCopy] ++
            rest)⟩ := by
      rw [step_instr rest hc rfl]; simp
    have e2 := move_byte (fits := fits) hfa hmi hS (dst := d) (src := s) (by omega) (by omega) stk
      ([vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (k + 1 - 1), .plain .memoryCopy] ++ rest)
    rw [hb0] at e2
    have hblt : b < 256 := hlt b (by simp)
    have hwc : d.toNat + 1 ≤ 2 ^ (mm.depth + W) := by
      have := hmi.2.1; simp only [MMem.Cover] at this; omega
    have hsz1 : (mm.write d.toNat 1 b).size = mm.size := by
      simp only [MMem.size, (MMem.write_fields mm d.toNat 1 b).1]
    have hmi1 : (mm.write d.toNat 1 b).Inv := MMem.write_inv hmi (by omega) b
    have hS1 : (S.setMem a (mm.write d.toNat 1 b).abs).mems[a]? =
        some (mm.write d.toNat 1 b).abs := mems_setMem hS
    have ih := copy_up_loop (fits := fits) hfa stk rest k (S.setMem a (mm.write d.toNat 1 b).abs)
      (mm.write d.toNat 1 b) (BitVec.ofNat 32 (d.toNat + 1)) (BitVec.ofNat 32 (s.toNat + 1))
      (BitVec.ofNat 32 k) tail (by rw [BitVec.toNat_ofNat]; omega) hmi1 hS1
      (by
        rcases Nat.eq_zero_or_pos k with h0 | hk
        · exact Or.inl h0
        · right; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [hsz1, BitVec.toNat_ofNat]; have := Nat.mod_le (s.toNat + 1) (2 ^ 32)
          rcases Nat.eq_zero_or_pos k with h0 | hk
          · omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [hsz1, BitVec.toNat_ofNat]; have := Nat.mod_le (d.toNat + 1) (2 ^ 32)
          rcases Nat.eq_zero_or_pos k with h0 | hk
          · omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (by simpa using hl)
      (by
        intro i hi
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          MMem.byte_write hmi.1 (by simpa using hwc)]
        simp only [show ¬ (d.toNat ≤ s.toNat + 1 + i ∧ s.toNat + 1 + i < d.toNat + 1) by omega,
          ↓reduceIte]
        simpa [show s.toNat + 1 + i = s.toNat + (i + 1) by omega] using hsrc (i + 1) (by omega))
      (fun x hx => hlt x (by simp [hx]))
    have hwb : (mm.write d.toNat 1 b).writeBytes (BitVec.ofNat 32 (d.toNat + 1)).toNat tail =
        mm.writeBytes d.toNat (b :: tail) := by
      rcases Nat.eq_zero_or_pos k with h0 | hk
      · subst h0
        have htail : tail = [] := List.length_eq_zero_iff.mp (by simpa using hl)
        subst htail
        simp only [MMem.writeBytes, MMem.write, Nat.mod_eq_of_lt hblt]
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), write1_eq_writeBytes mm _ _ hblt]
    rw [show 3 * (k + 1) + 1 = 1 + (2 + (3 * k + 1)) by ring, stepNU_add, stepNU_plain e1,
      Option.bind_some, stepNU_add, e2, Option.bind_some]
    rw [show vals stk.reverse ++ ([vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (k + 1 - 1),
        .plain .memoryCopy] ++ rest) = vals (.i32 (BitVec.ofNat 32 k) ::
          .i32 (BitVec.ofNat 32 (s.toNat + 1)) :: .i32 (BitVec.ofNat 32 (d.toNat + 1)) ::
          stk).reverse ++ .plain .memoryCopy :: rest by simp [vals, vi32]]
    rw [ih, setMem_setMem, hwb]

theorem copy_down_loop {fits : Bool}
    {f : Frame} {a : Nat} (hfa : f.inst.mems[0]? = some a) (stk : List Val)
    (rest : List AInstr) :
    ∀ (k : Nat) (S : Store) (mm : MMem) (d s n : BitVec 32) (src : List Nat), n.toNat = k →
      mm.Inv → S.mems[a]? = some mm.abs → s.toNat < d.toNat →
      s.toNat + k ≤ mm.size → d.toNat + k ≤ mm.size → src.length = k →
      (∀ i < k, mm.byte (s.toNat + i) = src.getD i 0) → (∀ b ∈ src, b < 256) →
      stepNU fits (3 * k + 1) ⟨S, f, vals (.i32 n :: .i32 s :: .i32 d :: stk).reverse ++
          .plain .memoryCopy :: rest⟩ =
        some ⟨S.setMem a (mm.writeBytes d.toNat src).abs, f, vals stk.reverse ++ rest⟩
  | 0, S, mm, d, s, n, src, hn, hmi, hS, _, hs, hd, hl, _, _ => by
    have hc := instrStep_copy (n := n) (s := s) (d := d) (stk := stk) (mem0_of hfa hS)
    rw [abs_size, MMem.blt_false (by omega), MMem.blt_false (by omega), hn] at hc
    simp only [Bool.or_false, Bool.cond_false, Nat.beq_refl, Bool.cond_true] at hc
    have hsrc : src = [] := List.length_eq_zero_iff.mp hl
    subst hsrc
    simp only [MMem.writeBytes]
    rw [setMem_self hS]
    exact stepNU_plain (by simpa using step_instr rest hc rfl)
  | k + 1, S, mm, d, s, n, src, hn, hmi, hS, hsd, hs, hd, hl, hsrc, hlt => by
    have hsz : mm.size ≤ 2 ^ 32 := by
      have := hmi.2.2.2; simp only [MMem.size]; omega
    have hbk : mm.byte (s.toNat + k) = src.getD k 0 := hsrc k (by omega)
    have hblt : src.getD k 0 < 256 := by rw [← hbk]; exact MMem.byte_lt _ _
    have hc := instrStep_copy (n := n) (s := s) (d := d) (stk := stk) (mem0_of hfa hS)
    rw [abs_size, MMem.blt_false (by omega), MMem.blt_false (by omega), hn] at hc
    have hnle : Nat.ble d.toNat s.toNat = false := by
      cases h : Nat.ble d.toNat s.toNat
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) (by omega)
    simp only [Bool.or_false, Bool.cond_false, show Nat.beq (k + 1) 0 = false from rfl, hnle,
      show d.toNat + (k + 1) - 1 = d.toNat + k by omega,
      show s.toNat + (k + 1) - 1 = s.toNat + k by omega] at hc
    have hdk : (BitVec.ofNat 32 (d.toNat + k)).toNat = d.toNat + k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsk : (BitVec.ofNat 32 (s.toNat + k)).toNat = s.toNat + k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have e1 : Ref.step ⟨S, f, vals (.i32 n :: .i32 s :: .i32 d :: stk).reverse ++
        .plain .memoryCopy :: rest⟩ = some ⟨S, f, vals stk.reverse ++
          [(Val.i32 (BitVec.ofNat 32 (d.toNat + k))).instr,
          (Val.i32 (BitVec.ofNat 32 (s.toNat + k))).instr,
          .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩)] ++
          ([(Val.i32 d).instr, (Val.i32 s).instr, vi32 (k + 1 - 1), .plain .memoryCopy] ++
            rest)⟩ := by
      rw [step_instr rest hc rfl]; simp [vi32]
    have e2 := move_byte (fits := fits) hfa hmi hS (dst := BitVec.ofNat 32 (d.toNat + k))
      (src := BitVec.ofNat 32 (s.toNat + k)) (by rw [hdk]; omega) (by rw [hsk]; omega) stk
      ([(Val.i32 d).instr, (Val.i32 s).instr, vi32 (k + 1 - 1), .plain .memoryCopy] ++ rest)
    rw [hdk, hsk, hbk] at e2
    have hwc : d.toNat + k + 1 ≤ 2 ^ (mm.depth + W) := by
      have := hmi.2.1; simp only [MMem.Cover] at this; omega
    set mm₁ := mm.write (d.toNat + k) 1 (src.getD k 0) with hmm₁
    have hsz1 : mm₁.size = mm.size := by
      simp only [hmm₁, MMem.size, (MMem.write_fields mm (d.toNat + k) 1 _).1]
    have hmi1 : mm₁.Inv := MMem.write_inv hmi (by omega) _
    have hS1 : (S.setMem a mm₁.abs).mems[a]? = some mm₁.abs := mems_setMem hS
    have ih := copy_down_loop (fits := fits) hfa stk rest k (S.setMem a mm₁.abs) mm₁ d s
      (BitVec.ofNat 32 k)
      (src.take k) (by rw [BitVec.toNat_ofNat]; omega) hmi1 hS1 hsd (by omega) (by omega)
      (by simp [hl])
      (by
        intro i hi
        rw [hmm₁, MMem.byte_write hmi.1 (by simpa using hwc)]
        simp only [show ¬ (d.toNat + k ≤ s.toNat + i ∧ s.toNat + i < d.toNat + k + 1) by omega,
          ↓reduceIte]
        rw [hsrc i (by omega)]
        simp [List.getD_eq_getElem?_getD, hi])
      (fun x hx => hlt x (List.mem_of_mem_take hx))
    have hfin : (mm₁.writeBytes d.toNat (src.take k)).abs = (mm.writeBytes d.toNat src).abs := by
      obtain ⟨hp1, hm1, hdep1⟩ := MMem.write_fields mm (d.toNat + k) 1 (src.getD k 0)
      obtain ⟨hp2, hm2, hdep2⟩ := MMem.writeBytes_fields mm₁ d.toNat (src.take k)
      obtain ⟨hp3, hm3, hdep3⟩ := MMem.writeBytes_fields mm d.toNat src
      apply MMem.abs_ext
      · rw [hp2, hp3, hp1]
      · rw [hm2, hm3, hm1]
      · intro x
        have htk : (src.take k).length = k := by simp [hl]
        rw [MMem.byte_writeBytes hmi1.1 (by rw [htk, hdep1]; omega)
            (fun y hy => hlt y (List.mem_of_mem_take hy)),
          MMem.byte_writeBytes hmi.1 (by rw [hl]; omega) hlt, htk, hl, hmm₁,
          MMem.byte_write hmi.1 (by simpa using hwc)]
        by_cases h1 : d.toNat ≤ x ∧ x < d.toNat + k
        · have h1' : d.toNat ≤ x ∧ x < d.toNat + (k + 1) := by omega
          simp only [h1, h1', and_self, ↓reduceIte]
          simp [List.getD_eq_getElem?_getD, show x - d.toNat < k by omega]
        · simp only [h1, ↓reduceIte]
          by_cases h2 : x = d.toNat + k
          · subst h2
            have h3 : d.toNat ≤ d.toNat + k ∧ d.toNat + k < d.toNat + (k + 1) := by omega
            have h5 : d.toNat + k ≤ d.toNat + k ∧ d.toNat + k < d.toNat + k + 1 := by omega
            simp only [h3, h5, and_self, ↓reduceIte, show d.toNat + k - d.toNat = k by omega,
              Nat.sub_self, Nat.pow_zero, Nat.div_one]
            exact Nat.mod_eq_of_lt hblt
          · have h3 : ¬ (d.toNat + k ≤ x ∧ x < d.toNat + k + 1) := by omega
            have h4 : ¬ (d.toNat ≤ x ∧ x < d.toNat + (k + 1)) := by omega
            simp only [h3, h4, ↓reduceIte]
    rw [show 3 * (k + 1) + 1 = 1 + (2 + (3 * k + 1)) by ring, stepNU_add, stepNU_plain e1,
      Option.bind_some, stepNU_add, e2, Option.bind_some]
    rw [show vals stk.reverse ++ ([(Val.i32 d).instr, (Val.i32 s).instr, vi32 (k + 1 - 1),
        .plain .memoryCopy] ++ rest) = vals (.i32 (BitVec.ofNat 32 k) :: .i32 s :: .i32 d ::
          stk).reverse ++ .plain .memoryCopy :: rest by simp [vals, vi32]]
    rw [ih, setMem_setMem, hfin]

theorem instrStep_init {S : Store} {f : Frame} {x : Nat} {n s d : BitVec 32} {stk : List Val}
    {a : Nat} {mem : MemInst} {da : Nat} {di : DataInst} (hm : Ref.mem0 S f = some (a, mem))
    (hx : f.inst.datas[x]? = some da) (hdi : S.datas[da]? = some di) :
    Ref.instrStep S f (.memoryInit x) (.i32 n :: .i32 s :: .i32 d :: stk) = some
      (bif Nat.blt di.data.length (s.toNat + n.toNat) || Nat.blt mem.size (d.toNat + n.toNat)
      then (S, f, stk, [.trap])
      else bif Nat.beq n.toNat 0 then (S, f, stk, [])
      else match di.data[s.toNat]? with
        | some b => (S, f, stk, [(Val.i32 d).instr, vi32 b.toNat,
            .plain (.storePacked .w32 .p8 ⟨0, 0⟩), vi32 (d.toNat + 1), vi32 (s.toNat + 1),
            vi32 (n.toNat - 1), .plain (.memoryInit x)])
        | none => (S, f, stk, [.trap])) := by
  simp only [Ref.instrStep, hm, hx, hdi, Option.map_some]
  cases di.data[s.toNat]? <;> rfl

theorem setMem_datas (S : Store) (a : Nat) (x : MemInst) : (S.setMem a x).datas = S.datas := rfl

theorem init_loop {fits : Bool}
    {f : Frame} {a : Nat} (hfa : f.inst.mems[0]? = some a) {x da : Nat}
    {di : DataInst} (hx : f.inst.datas[x]? = some da) (stk : List Val) (rest : List AInstr) :
    ∀ (k : Nat) (S : Store) (mm : MMem) (d s n : BitVec 32), n.toNat = k → mm.Inv →
      S.mems[a]? = some mm.abs → S.datas[da]? = some di → s.toNat + k ≤ di.data.length →
      d.toNat + k ≤ mm.size → s.toNat + k ≤ 2 ^ 32 →
      stepNU fits (2 * k + 1) ⟨S, f, vals (.i32 n :: .i32 s :: .i32 d :: stk).reverse ++
          .plain (.memoryInit x) :: rest⟩ =
        some ⟨S.setMem a (mm.init d.toNat ((di.data.drop s.toNat).take k)).abs, f,
          vals stk.reverse ++ rest⟩
  | 0, S, mm, d, s, n, hn, hmi, hS, hD, hs, hd, _ => by
    have hc := instrStep_init (n := n) (s := s) (d := d) (stk := stk) (mem0_of hfa hS) hx hD
    rw [abs_size, MMem.blt_false (by omega), MMem.blt_false (by omega), hn] at hc
    simp only [Bool.or_false, Bool.cond_false, Nat.beq_refl, Bool.cond_true] at hc
    simp only [List.take_zero, MMem.init, List.map_nil, MMem.writeBytes]
    rw [setMem_self hS]
    exact stepNU_plain (by simpa using step_instr rest hc rfl)
  | k + 1, S, mm, d, s, n, hn, hmi, hS, hD, hs, hd, hsn => by
    have hsz : mm.size ≤ 2 ^ 32 := by
      have := hmi.2.2.2; simp only [MMem.size]; omega
    obtain ⟨b, hb⟩ : ∃ b, di.data[s.toNat]? = some b :=
      ⟨di.data[s.toNat]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hc := instrStep_init (n := n) (s := s) (d := d) (stk := stk) (mem0_of hfa hS) hx hD
    rw [abs_size, MMem.blt_false (by omega), MMem.blt_false (by omega), hn, hb] at hc
    simp only [Bool.or_false, Bool.cond_false, show Nat.beq (k + 1) 0 = false from rfl] at hc
    have hbl : b.toNat < 256 := b.toNat_lt
    have hsp := instrStep_storePacked (S := S) (f := f) (w := .w32) (p := .p8) (ma := ⟨0, 0⟩)
      (x := d) (v := .i32 (BitVec.ofNat 32 b.toNat)) (c := b.toNat) (stk := stk)
      (mem0_of hfa hS) (by simp [Val.intBits])
    rw [abs_size, MMem.blt_false (by simp [PackSize.bits]; omega)] at hsp
    simp only [Bool.cond_false, Nat.add_zero, PackSize.bits, Nat.reduceDiv] at hsp
    have hwc : d.toNat + 1 ≤ 2 ^ (mm.depth + W) := by
      have := hmi.2.1; simp only [MMem.Cover] at this; omega
    have e1 : Ref.step ⟨S, f, vals (.i32 n :: .i32 s :: .i32 d :: stk).reverse ++
        .plain (.memoryInit x) :: rest⟩ = some ⟨S, f, vals (.i32 (BitVec.ofNat 32 b.toNat) ::
          .i32 d :: stk).reverse ++ .plain (.storePacked .w32 .p8 ⟨0, 0⟩) ::
          ([vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (k + 1 - 1),
            .plain (.memoryInit x)] ++ rest)⟩ := by
      rw [step_instr rest hc rfl]; simp [vals, vi32]
    have e2 := step_instr ([vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (k + 1 - 1),
      .plain (.memoryInit x)] ++ rest) hsp rfl
    rw [← MMem.abs_write hmi.1 (by simpa using hwc)] at e2
    set mm₁ := mm.write d.toNat 1 b.toNat with hmm₁
    have hsz1 : mm₁.size = mm.size := by
      simp only [hmm₁, MMem.size, (MMem.write_fields mm d.toNat 1 _).1]
    have hmi1 : mm₁.Inv := MMem.write_inv hmi (by omega) _
    have hS1 : (S.setMem a mm₁.abs).mems[a]? = some mm₁.abs := mems_setMem hS
    have ih := init_loop (fits := fits) hfa hx stk rest k (S.setMem a mm₁.abs) mm₁
      (BitVec.ofNat 32 (d.toNat + 1)) (BitVec.ofNat 32 (s.toNat + 1)) (BitVec.ofNat 32 k)
      (by rw [BitVec.toNat_ofNat]; omega) hmi1 hS1 (by rw [setMem_datas]; exact hD)
      (by rw [BitVec.toNat_ofNat]; have := Nat.mod_le (s.toNat + 1) (2 ^ 32)
          rcases Nat.eq_zero_or_pos k with h0 | hk
          · omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [hsz1, BitVec.toNat_ofNat]; have := Nat.mod_le (d.toNat + 1) (2 ^ 32)
          rcases Nat.eq_zero_or_pos k with h0 | hk
          · omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [BitVec.toNat_ofNat]; have := Nat.mod_le (s.toNat + 1) (2 ^ 32)
          rcases Nat.eq_zero_or_pos k with h0 | hk
          · omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega)
    have hfin : mm₁.init (BitVec.ofNat 32 (d.toNat + 1)).toNat
        ((di.data.drop (BitVec.ofNat 32 (s.toNat + 1)).toNat).take k) =
        mm.init d.toNat ((di.data.drop s.toNat).take (k + 1)) := by
      have hdrop : (di.data.drop s.toNat).take (k + 1) =
          b :: (di.data.drop (s.toNat + 1)).take k := by
        rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
        congr
        exact (List.getElem?_eq_some_iff.mp hb).2
      rw [hdrop]
      rcases Nat.eq_zero_or_pos k with h0 | hk
      · subst h0
        simp only [List.take_zero, MMem.init, List.map_nil, List.map_cons, MMem.writeBytes, hmm₁,
          MMem.write, Nat.mod_eq_of_lt hbl]
      · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        simp only [MMem.init, List.map_cons, hmm₁]
        exact write1_eq_writeBytes mm _ _ hbl _
    rw [show 2 * (k + 1) + 1 = 1 + (1 + (2 * k + 1)) by ring, stepNU_add, stepNU_plain e1,
      Option.bind_some, stepNU_add, stepNU_plain e2, Option.bind_some]
    rw [show vals stk.reverse ++ [] ++ ([vi32 (d.toNat + 1), vi32 (s.toNat + 1), vi32 (k + 1 - 1),
        .plain (.memoryInit x)] ++ rest) = vals (.i32 (BitVec.ofNat 32 k) ::
          .i32 (BitVec.ofNat 32 (s.toNat + 1)) :: .i32 (BitVec.ofNat 32 (d.toNat + 1)) ::
          stk).reverse ++ .plain (.memoryInit x) :: rest by simp [vals, vi32]]
    rw [ih, setMem_setMem, hfin]

theorem mem0_parts {m : MState} {a : Nat} {mm : MMem} (h : m.mem0 = some (a, mm)) :
    m.frame.inst.mems[0]? = some a ∧ m.store.abs.mems[a]? = some mm.abs := by
  simp only [MState.mem0] at h
  split at h
  · next a' ha =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, hx, rfl, rfl⟩ := h
    exact ⟨ha, by simp [MStore.abs_mems, hx]⟩
  · contradiction

/-- A bulk machine step: the innermost configuration runs `k` reference steps to its result. -/
theorem sim_bulk {m : MState} {a : Nat} {mm' : MMem} {stk : List Val} {rest : List AInstr}
    {k : Nat} (hi : m.Inv) (hmi' : mm'.Inv)
    (h : ∀ fits, stepNU fits k ⟨m.store.abs, m.frame, vals m.stack.reverse ++ m.code⟩ =
      some ⟨m.store.abs.setMem a mm'.abs, m.frame, vals stk.reverse ++ rest⟩) :
    ((m.setMem a mm').cont stk [] rest).Inv ∧ Sim m ((m.setMem a mm').cont stk [] rest) := by
  refine ⟨setMem_inv hi hmi', Sim.ofU (k := k) fun fits => ?_⟩
  rw [abs_eq_wrapC, abs_eq_wrapC]
  apply stepNU_wrap
  simp only [MState.cont, setMem_abs, List.nil_append]
  exact h fits

theorem stepPlain_sim {m m' : MState} {i : Instr} {rest : List AInstr}
    (hi : m.Inv) (hc : m.code = .plain i :: rest) (hv : Ref.toVal (.plain i) = none)
    (h : m.stepPlain i rest = some m') : m'.Inv ∧ Sim m m' := by
  fun_cases MState.stepPlain m i rest
  case case1 bt body =>
    simp only [MState.stepPlain, Option.bind_eq_some_iff, MState.enter] at h
    obtain ⟨ft, hft, h⟩ := h
    cases hlt : Nat.blt m.stack.length ft.params.length
    · simp only [hlt, Bool.cond_false, Option.some.injEq] at h
      subst h
      have hle : ft.params.length ≤ m.stack.length := by
        by_contra hh
        rw [MMem.blt_true (by omega)] at hlt
        contradiction
      refine ⟨hi, Sim.one ?_⟩
      rw [abs_eq_wrapC, abs_eq_wrapC, hc]
      apply stepN_one
      apply step_wrap
      have := step_instr (S := m.store.abs) (f := m.frame) rest
        (i := .block bt body) (stk := m.stack) (S' := m.store.abs) (f' := m.frame)
        (stk' := m.stack.drop ft.params.length)
        (out := [.label ft.results.length []
          (vals (m.stack.take ft.params.length).reverse ++ body.map .plain)])
        (by simp [Ref.instrStep, hft, hle]) hv
      simpa [List.append_assoc] using this
    · simp [hlt] at h
  case case2 bt body =>
    simp only [MState.stepPlain, Option.bind_eq_some_iff, MState.enter] at h
    obtain ⟨ft, hft, h⟩ := h
    cases hlt : Nat.blt m.stack.length ft.params.length
    · simp only [hlt, Bool.cond_false, Option.some.injEq] at h
      subst h
      have hle := le_of_blt_false hlt
      refine ⟨hi, Sim.one ?_⟩
      rw [abs_eq_wrapC, abs_eq_wrapC, hc]
      apply stepN_one
      apply step_wrap
      have := step_instr (S := m.store.abs) (f := m.frame) rest
        (i := .loop bt body) (stk := m.stack) (S' := m.store.abs) (f' := m.frame)
        (stk' := m.stack.drop ft.params.length)
        (out := [.label ft.params.length [.loop bt body]
          (vals (m.stack.take ft.params.length).reverse ++ body.map .plain)])
        (by simp [Ref.instrStep, hft, hle]) hv
      simpa [List.append_assoc] using this
    · simp [hlt] at h
  case case3 l =>
    simp only [MState.stepPlain, Option.map_eq_some_iff] at h
    obtain ⟨⟨stk', code', ctl'⟩, hb, rfl⟩ := h
    refine ⟨hi, Sim.one ?_⟩
    rw [abs_eq_wrapC, abs_eq_wrapC, hc]
    apply stepN_one
    have hs : Ref.seq m.store.abs m.frame [] (vals m.stack.reverse ++ .plain (.br l) :: rest) =
        .br l m.stack := by
      rw [seq_focus _ _ _ _ hv]; simp [Ref.atInstr]
    simp only [wrapC, Ref.step, seq_wrap_br l m.ctl ctl' hs hb]
  case case4 =>
    simp only [MState.stepPlain, Option.map_eq_some_iff] at h
    obtain ⟨⟨f', stk', code', ctl'⟩, hb, rfl⟩ := h
    refine ⟨hi, Sim.one ?_⟩
    rw [abs_eq_wrapC, abs_eq_wrapC, hc]
    apply stepN_one
    have hs : Ref.seq m.store.abs m.frame [] (vals m.stack.reverse ++ .plain .return_ :: rest) =
        .ret m.stack := by
      rw [seq_focus _ _ _ _ hv]; simp [Ref.atInstr]
    simp only [wrapC, Ref.step, seq_wrap_ret m.ctl ctl' hs hb]
  case case5 t ma x stk hstk =>
    simp only [MState.stepPlain, hstk, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, mm⟩, hm, rfl⟩ := h
    have hs := step_instr (S := m.store.abs) (f := m.frame) rest (i := .load t ma)
      (stk := m.stack) (S' := m.store.abs) (f' := m.frame) (stk' := stk)
      (hstk ▸ instrStep_load (mem0_abs_some hm)) hv
    rw [abs_size, MMem.abs_read] at hs
    refine ⟨?_, sim_one ?_ ?_⟩
    · cases Nat.blt mm.size (x.toNat + ma.offset + t.bytes) <;> exact hi
    · cases Nat.blt mm.size (x.toNat + ma.offset + t.bytes) <;> rfl
    · rw [hc]
      cases hb : Nat.blt mm.size (x.toNat + ma.offset + t.bytes) <;>
        simpa [hb, MState.cont, vals_cons_reverse, List.append_assoc] using hs
  case case6 w p sx ma x stk hstk =>
    simp only [MState.stepPlain, hstk, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, mm⟩, hm, rfl⟩ := h
    have hs := step_instr (S := m.store.abs) (f := m.frame) rest (i := .loadPacked w p sx ma)
      (stk := m.stack) (S' := m.store.abs) (f' := m.frame) (stk' := stk)
      (hstk ▸ instrStep_loadPacked (mem0_abs_some hm)) hv
    rw [abs_size, MMem.abs_read] at hs
    refine ⟨?_, sim_one ?_ ?_⟩
    · cases Nat.blt mm.size (x.toNat + ma.offset + p.bits / 8) <;> exact hi
    · cases Nat.blt mm.size (x.toNat + ma.offset + p.bits / 8) <;> rfl
    · rw [hc]
      cases hb : Nat.blt mm.size (x.toNat + ma.offset + p.bits / 8) <;>
        simpa [hb, MState.cont, vals_cons_reverse, List.append_assoc] using hs
  case case7 =>
    exact sim_store hi hc hv ‹_› ‹_› ‹_› (by simpa [MState.stepPlain, *] using h)
  case case8 =>
    exact sim_store hi hc hv ‹_› ‹_› ‹_› (by simpa [MState.stepPlain, *] using h)
  case case9 =>
    exfalso
    simp only [MState.stepPlain, *] at h
    simp at h
  case case10 =>
    exact sim_storePacked hi hc hv ‹_› ‹_› ‹_› (by simpa [MState.stepPlain, *] using h)
  case case11 =>
    exact sim_storePacked hi hc hv ‹_› ‹_› ‹_› (by simpa [MState.stepPlain, *] using h)
  case case12 =>
    exfalso
    simp only [MState.stepPlain, *] at h
    simp at h
  case case13 n stk hstk =>
    simp only [MState.stepPlain, hstk, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, mm⟩, hm, rfl⟩ := h
    have hst := instrStep_grow (n := n) (stk := stk) (mem0_abs_some hm)
    rw [← hstk] at hst
    have hmi := mem0_inv hi hm
    cases hg : mm.grow n.toNat with
    | none =>
      rw [MMem.grow_none.mp hg] at hst
      refine ⟨hi, sim_one rfl ?_⟩
      rw [hc]
      simpa [MState.cont, vals_cons_reverse, List.append_assoc] using step_instr rest hst hv
    | some mm' =>
      obtain ⟨hinv', habs⟩ := MMem.grow_some hmi hg
      rw [habs] at hst
      refine ⟨setMem_inv hi hinv', sim_one rfl ?_⟩
      rw [hc]
      have := step_instr rest hst hv
      simp only [MState.cont] at this ⊢
      rw [setMem_abs]
      simpa [MState.setMem, vals_cons_reverse, List.append_assoc, vi32, MMem.abs] using this
  case case14 n v d stk hstk =>
    simp only [MState.stepPlain, hstk, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, mm⟩, hm, h⟩ := h
    obtain ⟨hfa, hS⟩ := mem0_parts hm
    have hmi := mem0_inv hi hm
    have hf := instrStep_fill (n := n) (v := v) (d := d) (stk := stk) (mem0_abs_some hm)
    rw [abs_size, ← hstk] at hf
    cases hb : Nat.blt mm.size (d.toNat + n.toNat)
    · cases hz : Nat.beq n.toNat 0
      · simp only [hb, hz, Bool.cond_false, Option.map_eq_some_iff] at h
        obtain ⟨c, hcb, rfl⟩ := h
        have hle := le_of_blt_false hb
        refine sim_bulk hi (MMem.writeBytes_inv hmi (by simpa using hle)
          (fun x hx => by simp only [List.mem_replicate] at hx; omega)) (k := 2 * n.toNat + 1)
          fun fits => ?_
        have hl := fill_loop (fits := fits) hfa hcb stk rest n.toNat m.store.abs mm d n rfl hmi hS
          hle
        rw [← hstk] at hl
        rw [hc]
        exact hl
      · simp only [hb, hz, Bool.cond_false, Bool.cond_true, Option.some.injEq] at h hf
        subst h
        refine ⟨hi, sim_one rfl ?_⟩
        rw [hc]
        simpa [MState.cont] using step_instr rest hf hv
    · simp only [hb, Bool.cond_true, Option.some.injEq] at h hf
      subst h
      refine ⟨hi, sim_one rfl ?_⟩
      rw [hc]
      simpa [MState.cont] using step_instr rest hf hv
  case case15 n s d stk hstk =>
    simp only [MState.stepPlain, hstk, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, mm⟩, hm, h⟩ := h
    obtain ⟨hfa, hS⟩ := mem0_parts hm
    have hmi := mem0_inv hi hm
    have hcp := instrStep_copy (n := n) (s := s) (d := d) (stk := stk) (mem0_abs_some hm)
    rw [abs_size, ← hstk] at hcp
    cases hb : (Nat.blt mm.size (s.toNat + n.toNat) || Nat.blt mm.size (d.toNat + n.toNat))
    · simp only [hb, Bool.cond_false] at h
      subst h
      have hb1 : ¬ mm.size < s.toNat + n.toNat ∧ ¬ mm.size < d.toNat + n.toNat := by
        simp only [Bool.or_eq_false_iff] at hb
        exact ⟨Nat.not_lt.mpr (le_of_blt_false hb.1), Nat.not_lt.mpr (le_of_blt_false hb.2)⟩
      have hsrc := MMem.readBytes_getD mm s.toNat n.toNat
      have hlen := MMem.readBytes_length mm s.toNat n.toNat
      have hlt := MMem.readBytes_lt mm s.toNat n.toNat
      refine sim_bulk hi (MMem.writeBytes_inv hmi (by rw [hlen]; omega) hlt)
        (k := 3 * n.toNat + 1) fun fits => ?_
      rw [hc, hstk]
      by_cases hds : d.toNat ≤ s.toNat
      · exact copy_up_loop (fits := fits) hfa stk rest n.toNat m.store.abs mm d s n _ rfl hmi hS
          (Or.inr hds)
          (by omega) (by omega) hlen (fun i hi' => (hsrc i hi').symm) hlt
      · exact copy_down_loop (fits := fits) hfa stk rest n.toNat m.store.abs mm d s n _ rfl hmi hS
          (by omega)
          (by omega) (by omega) hlen (fun i hi' => (hsrc i hi').symm) hlt
    · simp only [hb, Bool.cond_true] at h hcp
      subst h
      refine ⟨hi, sim_one rfl ?_⟩
      rw [hc]
      simpa [MState.cont] using step_instr rest hcp hv
  case case16 x n s d stk hstk a mm da hdx hm =>
    simp only [MState.stepPlain, hstk, hm, hdx, Option.bind_eq_some_iff] at h
    obtain ⟨di, hdi, h⟩ := h
    obtain ⟨hfa, hS⟩ := mem0_parts hm
    have hmi := mem0_inv hi hm
    have hD : m.store.abs.datas[da]? = some di := hdi
    have hin := instrStep_init (n := n) (s := s) (d := d) (stk := stk) (mem0_abs_some hm) hdx hD
    rw [abs_size, ← hstk] at hin
    cases hb : (Nat.blt di.data.length (s.toNat + n.toNat) || Nat.blt mm.size (d.toNat + n.toNat))
    · simp only [hb, Bool.cond_false] at h
      cases hw : Nat.blt (2 ^ 32) (s.toNat + n.toNat)
      · simp only [hw, Bool.cond_false, Option.some.injEq] at h
        subst h
        have hb1 : s.toNat + n.toNat ≤ di.data.length ∧ d.toNat + n.toNat ≤ mm.size := by
          simp only [Bool.or_eq_false_iff] at hb
          exact ⟨le_of_blt_false hb.1, le_of_blt_false hb.2⟩
        have hbytes : ∀ b ∈ ((di.data.drop s.toNat).take n.toNat).map UInt8.toNat, b < 256 := by
          intro b hb'
          simp only [List.mem_map] at hb'
          obtain ⟨y, -, rfl⟩ := hb'
          exact y.toNat_lt
        refine sim_bulk hi (MMem.writeBytes_inv hmi (by simp; omega) hbytes)
          (k := 2 * n.toNat + 1) fun fits => ?_
        rw [hc, hstk]
        exact init_loop (fits := fits) hfa hdx stk rest n.toNat m.store.abs mm d s n rfl hmi hS hD
          hb1.1 hb1.2
          (by have := le_of_blt_false hw; norm_num at this ⊢; omega)
      · simp only [hw, Bool.cond_true] at h
        exact absurd h (by simp)
    · simp only [hb, Bool.cond_true, Option.some.injEq] at h hin
      subst h
      refine ⟨hi, sim_one rfl ?_⟩
      rw [hc]
      simpa [MState.cont] using step_instr rest hin hv
  case case17 =>
    exfalso
    simp only [MState.stepPlain, *] at h
    simp at h
  case case18 hblock hloop hbr hret hload hloadp hstore hstorep hgrow hfill hcopy hinit =>
    have hd : m.stepPlain i rest = (Ref.instrStep m.store.abs m.frame i m.stack).map
        fun (s', f', stk', out) =>
          { m with store := { m.store with base := s' }, frame := f', stack := stk',
                   code := out ++ rest } := by
      unfold MState.stepPlain
      split
      all_goals first
        | rfl
        | exact (hblock _ _ rfl).elim
        | exact (hloop _ _ rfl).elim
        | exact (hbr _ rfl).elim
        | exact (hret rfl).elim
        | exact (hload _ _ _ _ rfl (by assumption)).elim
        | exact (hloadp _ _ _ _ _ _ rfl (by assumption)).elim
        | exact (hstore _ _ _ _ _ rfl (by assumption)).elim
        | exact (hstorep _ _ _ _ _ _ rfl (by assumption)).elim
        | exact (hgrow _ _ rfl (by assumption)).elim
        | exact (hfill _ _ _ _ rfl (by assumption)).elim
        | exact (hcopy _ _ _ _ rfl (by assumption)).elim
        | exact (hinit _ _ _ _ _ rfl (by assumption)).elim
    rw [hd, Option.map_eq_some_iff] at h
    obtain ⟨⟨s', f', stk', out⟩, hstep, rfl⟩ := h
    have hmem : s'.mems = m.store.abs.mems := by
      apply instrStep_mems hstep
      · rintro t ma rfl
        obtain ⟨v, x, r, hs⟩ := instrStep_store_shape hstep
        exact hstore t ma v x r rfl hs
      · rintro w p ma rfl
        obtain ⟨v, x, r, hs⟩ := instrStep_storePacked_shape hstep
        exact hstorep w p ma v x r rfl hs
      · rintro rfl
        obtain ⟨n, r, hs⟩ := instrStep_grow_shape hstep
        exact hgrow n r rfl hs
    have hst : ({ m.store with base := s' } : MStore).abs = s' := by
      show { s' with mems := m.store.mems.map MMem.abs } = s'
      rw [← MStore.abs_mems, ← hmem]
    refine ⟨hi, sim_one rfl ?_⟩
    rw [hc, hst]
    simpa [List.append_assoc] using step_instr rest hstep hv

theorem step_invoke_inner {S : Store} {f : Frame} {stk : List Val} {rest : List AInstr} {a : Nat}
    {dt : DefType} {ft : FuncType} {inst : ModuleInst} {code : Func}
    (hf : S.funcs[a]? = some (.wasm dt inst code)) (hft : dt.expand = some ft)
    (hk : ft.params.length ≤ stk.length) :
    Ref.step ⟨S, f, vals stk.reverse ++ .invoke a :: rest⟩ = some ⟨S, f,
      vals (stk.drop ft.params.length).reverse ++ [.frame ft.results.length
        ⟨(stk.take ft.params.length).reverse.map some ++ code.localDefaults, inst⟩
        [.label ft.results.length [] (code.body.map .plain)]] ++ rest⟩ := by
  apply step_focus rfl
  simp only [Ref.atInstr, hf, hft, MMem.blt_false hk, Bool.cond_false]

/-- Contract U26 T1: every machine step is `k` reference steps between the abstractions, and
keeps the machine invariant. -/
theorem step_sim {m m' : MState} (hi : m.Inv) (h : m.step = some m') :
    m'.Inv ∧ Sim m m' := by
  rcases m with ⟨st, f, stk, code, ctl⟩
  cases code with
  | cons e rest =>
    cases hv : Ref.toVal e with
    | some v =>
      simp only [MState.step, hv, Option.some.injEq] at h
      subst h
      refine ⟨hi, Sim.zero ?_⟩
      have he := Ref.eq_instr_of_toVal hv
      subst he
      simp only [stepN, abs_eq_wrapC, vals_cons_reverse, List.append_assoc, List.singleton_append]
    | none =>
      cases e with
      | plain i =>
        simp only [MState.step, hv] at h
        exact stepPlain_sim hi rfl hv h
      | invoke a =>
        simp only [MState.step, hv, MState.invoke] at h
        split at h
        · next dt inst fcode hf =>
          cases hft : dt.expand with
          | none => simp [hft] at h
          | some ft =>
            simp only [hft, Option.bind_some] at h
            cases hlt : Nat.blt stk.length ft.params.length
            · simp only [hlt, Bool.cond_false, Option.some.injEq] at h
              subst h
              refine ⟨hi, Sim.one ?_⟩
              rw [abs_eq_wrapC, abs_eq_wrapC]
              apply stepN_one
              exact step_wrap ctl (step_invoke_inner (S := st.abs) (f := f) (rest := rest) hf hft
                (le_of_blt_false hlt))
            · simp [hlt] at h
        · contradiction
      | trap =>
        simp only [MState.step, hv] at h
        cases hb : (ctl.isEmpty && stk.isEmpty && rest.isEmpty)
        · simp only [hb, Bool.cond_false, Option.some.injEq] at h
          subst h
          refine ⟨hi, ?_⟩
          obtain ⟨k, hk⟩ := trap_collapse st.abs ctl f stk rest
          refine Sim.notUnique (by rw [abs_eq_wrapC]; exact hk) fun fits => ?_
          rw [abs_eq_wrapC, uniqueStep_wrapC]
          simp only [Ref.uniqueStep, Ref.seqUnique_vals, List.reverse_reverse, List.append_nil]
          rfl
        · simp [hb] at h
      | _ => simp [MState.step, hv] at h
  | nil =>
    cases ctl with
    | nil => simp [MState.step] at h
    | cons c ctl =>
      cases c with
      | label n cont saved rest =>
        simp only [MState.step, Option.some.injEq] at h
        subst h
        refine ⟨hi, Sim.one ?_⟩
        rw [abs_eq_wrapC, abs_eq_wrapC]
        apply stepN_one
        simp only [wrapC, wrap_cons, Ref.step, List.append_nil]
        rw [seq_wrap_step ctl (seq_layer_final_label (S := st.abs) (f := f) (stk := stk) n cont
          saved rest)]
      | frame n caller saved rest =>
        simp only [MState.step] at h
        cases hb : Nat.beq stk.length n
        · simp [hb] at h
        · simp only [hb, Bool.cond_true, Option.some.injEq] at h
          subst h
          refine ⟨hi, Sim.one ?_⟩
          rw [abs_eq_wrapC, abs_eq_wrapC]
          apply stepN_one
          simp only [wrapC, wrap_cons, Ref.step, List.append_nil]
          rw [seq_wrap_step ctl (seq_layer_final_frame (S := st.abs) (f := f) (stk := stk) n caller
            saved rest (Nat.eq_of_beq_eq_true hb))]

/-! ## Final states (contract U26 T2) -/

theorem abs_returned {m : MState} {vs : List Val} (h : m.ending = .returned vs) :
    Final m.abs (.returned m.store.abs vs) := by
  simp only [MState.ending] at h
  split at h
  · next stk hc hcode =>
    simp only [MState.Ending.returned.injEq] at h
    subst h
    simp [Final, abs_eq_wrapC, wrapC, wrap, hc, hcode]
  · contradiction
  · contradiction

theorem abs_trapped {m : MState} (h : m.ending = .trapped) :
    Final m.abs (.trapped m.store.abs) := by
  simp only [MState.ending] at h
  split at h
  · contradiction
  · next hc hcode hstk => simp [Final, abs_eq_wrapC, wrapC, wrap, hc, hcode, hstk]
  · contradiction

/-! ## Runs and the instantiation boundary (contract U26 T4) -/

theorem stepN_steps {H : HostSem} : ∀ {k : Nat} {c c' : Config}, stepN k c = some c' →
    Steps H c c'
  | 0, c, c', h => by
    simp only [stepN, Option.some.injEq] at h
    subst h
    exact .refl
  | k + 1, c, c', h => by
    simp only [stepN] at h
    cases hs : Ref.step c with
    | none => simp [hs] at h
    | some c₁ =>
      rw [hs, Option.bind_some] at h
      exact Relation.ReflTransGen.head (Ref.step_sound hs) (stepN_steps h)

theorem run_sim : ∀ (n : Nat) {m m' : MState} {b : Bool}, m.Inv → m.run n = (m', b) →
    m'.Inv ∧ ∃ k, stepN k m.abs = some m'.abs
  | 0, m, m', b, hi, h => by
    simp only [MState.run, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hi, 0, rfl⟩
  | n + 1, m, m', b, hi, h => by
    simp only [MState.run] at h
    cases hs : m.step with
    | none =>
      rw [hs] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hi, 0, rfl⟩
    | some m₁ =>
      rw [hs] at h
      obtain ⟨hi₁, k₁, hk₁, -⟩ := step_sim hi hs
      obtain ⟨hi', k₂, hk₂⟩ := run_sim n hi₁ h
      exact ⟨hi', k₁ + k₂, by rw [stepN_add, hk₁, Option.bind_some, hk₂]⟩

theorem abs_ofInvoke (s : MStore) (a : Nat) (args : List Val) :
    (MState.ofInvoke s a args).abs = invokeConfig s.abs a args := by
  simp [MState.ofInvoke, abs_eq_wrapC, wrapC, wrap, invokeConfig]

theorem alloc_abs (s : MStore) (m : Module) (imports : List ExternVal) (gvals : List Val)
    (trefs : List Ref) (erefs : List (List Ref)) :
    (s.alloc m imports gvals trefs erefs).1.abs =
        (allocModule s.abs m imports gvals trefs erefs).1 ∧
      (s.alloc m imports gvals trefs erefs).2 =
        (allocModule s.abs m imports gvals trefs erefs).2 := by
  refine ⟨?_, rfl⟩
  simp only [MStore.alloc, MStore.abs, List.map_append, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro lim _
  exact MMem.alloc_abs _ _

theorem alloc_inv {s : MStore} (hi : s.Inv) {m : Module} (hm : ∀ lim ∈ m.mems, lim.min ≤ 2 ^ 16)
    (imports : List ExternVal) (gvals : List Val) (trefs : List Ref) (erefs : List (List Ref)) :
    (s.alloc m imports gvals trefs erefs).1.Inv := by
  intro mm hmm
  simp only [MStore.alloc, List.mem_append, List.mem_map] at hmm
  rcases hmm with hmm | ⟨lim, hlim, rfl⟩
  · exact hi mm hmm
  · exact MMem.alloc_inv _ _ (hm lim hlim)

/-- Contract U26 T4: a successful machine instantiation is the spec's `Instantiated`. -/
theorem instantiate_sound {H : HostSem} {fuel : Nat} {s s' : MStore} {m : Module}
    {imports : List ExternVal} {inst : ModuleInst} (hi : s.Inv)
    (hmem : ∀ lim ∈ m.mems, lim.min ≤ 2 ^ 16) (hm : ImportsMatch s.abs m imports)
    (h : instantiate fuel s m imports = some (s', inst)) :
    Instantiated H m s.abs imports s'.abs inst := by
  simp only [instantiate, initRun, bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨m', ex⟩, hrun, hfin⟩
  rcases hrun with ⟨gvals, hg0, trefs, ht0, erefs, he0, gvals₁, hg, trefs₁, ht, erefs₁, he, u, hu,
    hr⟩
  cases u
  simp only [guard] at hu
  split at hu
  · rename_i heq
    simp only [Bool.and_eq_true, beq_iff_eq] at heq
    rcases heq with ⟨⟨hgv, htr⟩, her⟩
    subst gvals₁ trefs₁ erefs₁
    simp only [Option.some.injEq] at hr
    obtain ⟨hs₁, hinst⟩ := alloc_abs s m imports gvals trefs erefs
    set s₁ := (s.alloc m imports gvals trefs erefs).1
    set inst₁ := (s.alloc m imports gvals trefs erefs).2
    have hi₁ : s₁.Inv := alloc_inv hi hmem imports gvals trefs erefs
    cases ex with
    | true => simp at hfin
    | false =>
      simp only at hfin
      split at hfin
      · next vs hend =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hfin
        obtain ⟨rfl, rfl⟩ := hfin
        obtain ⟨-, k, hk⟩ := run_sim fuel
          (m := MState.mk s₁ ⟨[], inst₁⟩ [] ((initCode m).map .plain) []) hi₁ hr
        have hsteps := stepN_steps (H := H) hk
        have hfr := Ref.steps_frame_shape hsteps
        simp only [MState.ending] at hend
        split at hend
        · next stk heqc =>
          simp only [MState.Ending.returned.injEq] at hend
          have hstk : m'.stack = [] := List.reverse_eq_nil_iff.mp hend
          have habs' : m'.abs = ⟨m'.store.abs, m'.frame, []⟩ := by
            simp [abs_eq_wrapC, wrapC, stk, heqc, hstk, wrap]
          have habs₀ : (MState.mk s₁ ⟨[], inst₁⟩ [] ((initCode m).map .plain) []).abs =
              ⟨s₁.abs, ⟨[], inst₁⟩, (initCode m).map .plain⟩ := by
            simp [abs_eq_wrapC, wrapC, wrap]
          rw [habs₀, habs'] at hsteps
          have hfr' := Ref.steps_frame_shape hsteps
          have hframe : m'.frame = ⟨[], inst₁⟩ := by
            obtain ⟨hi1, hl1⟩ := hfr'
            rcases hf : m'.frame with ⟨locs, fi⟩
            rw [hf] at hi1 hl1
            simp only [List.length_nil, List.length_eq_zero_iff] at hl1
            simp_all
          rw [hframe] at hsteps ⊢
          refine ⟨hm, gvals, trefs, erefs, s₁.abs, ?_, ?_, ?_, ?_, hsteps⟩
          · rw [hs₁, hinst]
          · apply (Ref.forall₂_mapM hg).imp
            intro g v hv
            exact Ref.evalConst_sound hv
          · apply (Ref.forall₂_mapM ht).imp
            intro t r hex
            simp only [Option.bind_eq_some_iff] at hex
            rcases hex with ⟨v, hv, hvr⟩
            cases v <;> simp only [Ref.asRef, reduceCtorEq, Option.some.injEq] at hvr
            subst r
            exact Ref.evalConst_sound hv
          · apply (Ref.forall₂_mapM he).imp
            intro e rs hers
            apply (Ref.forall₂_mapM hers).imp
            intro ex r hex
            simp only [Option.bind_eq_some_iff] at hex
            rcases hex with ⟨v, hv, hvr⟩
            cases v <;> simp only [Ref.asRef, reduceCtorEq, Option.some.injEq] at hvr
            subst r
            exact Ref.evalConst_sound hv
        · contradiction
        · contradiction
      · contradiction
  · contradiction

end FVA.Wasm.Exec.Machine
