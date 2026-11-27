import FVA.Impl.Exec.Process
import FVA.Proof.Exec.MachineSys
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Valid.InstantiateUnique

/-!
# Unique-step instantiation (contract U29b T3)

`instantiateU` succeeds only where `instantiate` does (`instantiateU_instantiate`: so
`instantiate_sound` gives `Instantiated`, T3(iii)), and its run of the initialization code is a
uniqueness certificate (T3(ii)): every step no choice point of `Step`, the relation
`Instantiated` uses, so `machineRun_must` makes its final store the only one. With the
initializer values unique (T3(i)), every `Instantiated` witness of a valid module ends in its
store with its instance (`instantiateU_unique`).
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

/-- A total-correctness proof covers every finished execution. -/
theorem _root_.FVA.Wasm.Exec.Must.final {H : HostSem} {Q : Outcome → Prop} {c c' : Config}
    {o : Outcome} (hm : Must H Q c) (hs : Steps H c c') (hf : Final c' o) : Q o := by
  revert hm
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hm
    cases hm with
    | done hf' hq => rw [Ref.final_unique hf hf']; exact hq
    | next hex _ =>
      obtain ⟨d, hd⟩ := hex
      exact absurd hd (Ref.no_step_final hf)
  | head hstep _ ih =>
    intro hm
    cases hm with
    | done hf' _ => exact absurd hstep (Ref.no_step_final hf')
    | next _ hall => exact ih (hall _ hstep)

/-- A state that has returned: no control entry, no code, its values on the stack. -/
theorem ending_returned {m : MState} {vs : List Val} (h : m.ending = .returned vs) :
    m.ctl = [] ∧ m.code = [] ∧ m.stack = vs.reverse := by
  unfold MState.ending at h
  split at h
  · rename_i hctl hcode
    simp only [MState.Ending.returned.injEq] at h
    exact ⟨hctl, hcode, by rw [← h, List.reverse_reverse]⟩
  all_goals cases h

/-- A state that has returned takes no step. -/
theorem step_none_of_ending {m : MState} {vs : List Val} (h : m.ending = .returned vs) :
    m.step = none := by
  obtain ⟨hctl, hcode, -⟩ := ending_returned h
  simp [MState.step, hcode, hctl]

/-- A unique-step run that stops where no step remains is the plain run. -/
theorem runU_run {fits : Bool} : ∀ (n : Nat) {m m' : MState}, m.runU fits n = (m', false) →
    m'.step = none → m.run n = (m', false)
  | 0, m, m', h, _ => by simp [MState.runU] at h
  | n + 1, m, m', h, hs => by
    unfold MState.runU at h
    cases hb : (m.uniq fits || m.admin)
    · simp only [hb, Bool.cond_false, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [MState.run, hs]
    · simp only [hb, Bool.cond_true] at h
      cases hst : m.step with
      | none =>
        simp only [hst, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp [MState.run, hst]
      | some m₁ =>
        simp only [hst] at h
        simp only [MState.run, hst]
        exact runU_run n h hs

/-- A unique-step run keeps the invariant. -/
theorem runU_inv {fits : Bool} : ∀ (n : Nat) {m m' : MState} {b : Bool}, m.Inv →
    m.runU fits n = (m', b) → m'.Inv
  | 0, m, m', b, hi, h => by
    simp only [MState.runU, Prod.mk.injEq] at h
    exact h.1 ▸ hi
  | n + 1, m, m', b, hi, h => by
    unfold MState.runU at h
    cases hb : (m.uniq fits || m.admin)
    · simp only [hb, Bool.cond_false, Prod.mk.injEq] at h
      exact h.1 ▸ hi
    · simp only [hb, Bool.cond_true] at h
      cases hst : m.step with
      | none =>
        simp only [hst, Prod.mk.injEq] at h
        exact h.1 ▸ hi
      | some m₁ =>
        simp only [hst] at h
        exact runU_inv n (step_sim hi hst).1 h

/-- A pending host call is no unique or administrative step. -/
theorem hostCall_not_uniq {m : MState} {p : Nat × Nat × List AInstr} (h : m.hostCall = some p) :
    (m.uniq true || m.admin) = false := by
  obtain ⟨id, k, rest⟩ := p
  obtain ⟨a, dt, ft, hc, hf, -, -, -⟩ := hostCall_some h
  simp [MState.uniq, MState.admin, hc, hf, Ref.toVal]

/-- A live process's run takes the steps `runU true` takes, up to where it stops. -/
theorem sysRun_runU {St : Type} {exited : St → Option Nat}
    {X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)} {σ : St}
    (hl : exited σ = none) : ∀ (n : Nat) {m m₁ : MState}, m.runU true n = (m₁, false) →
      ∃ i, ∀ j, sysRun exited X (i + j) (σ, m) = sysRun exited X j (σ, m₁)
  | 0, m, m₁, h => by simp [MState.runU] at h
  | n + 1, m, m₁, h => by
    unfold MState.runU at h
    cases hb : (m.uniq true || m.admin)
    · simp only [hb, Bool.cond_false, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨0, fun j => by simp⟩
    · simp only [hb, Bool.cond_true] at h
      cases hs : m.step with
      | none =>
        simp only [hs, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨0, fun j => by simp⟩
      | some m' =>
        simp only [hs] at h
        obtain ⟨i, hi⟩ := sysRun_runU hl n h
        have hh : m.hostCall = none := by
          cases hc : m.hostCall with
          | none => rfl
          | some p => rw [hostCall_not_uniq hc] at hb; cases hb
        refine ⟨i + 1, fun j => ?_⟩
        rw [show i + 1 + j = (i + j) + 1 by omega]
        simp only [sysRun, hl, hh, hb, Bool.cond_true, hs]
        exact hi j

/-- `SysMust` moves forward over unique steps of a live process. -/
theorem sysMust_forward_stepNU {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    (hl : W.exited σ = none) : ∀ {k : Nat} {c c' : Config}, stepNU fits k c = some c' →
      SysMust W fits Q (σ, c) → SysMust W fits Q (σ, c')
  | 0, c, c', h, hm => by
    simp only [stepNU, Option.some.injEq] at h
    exact h ▸ hm
  | k + 1, c, c', h, hm => by
    simp only [stepNU] at h
    cases hu : Ref.uniqueStep fits c
    · simp [hu] at h
    · simp only [hu, Bool.cond_true] at h
      cases hs : Ref.step c with
      | none => simp [hs] at h
      | some c₁ =>
        simp only [hs, Option.bind_some] at h
        exact sysMust_forward_stepNU hl h
          (hm.forward (sysStep_iff.mpr ⟨hl, .inl ⟨stepP_of_step hs hu, rfl⟩⟩))

/-- `SysMust` moves forward over a unique machine step of a live process. -/
theorem sysMust_forward_uniq {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {m m' : MState} (hl : W.exited σ = none) (hi : m.Inv) (hu : m.uniq fits = true)
    (hs : m.step = some m') (hm : SysMust W fits Q (σ, m.abs)) : SysMust W fits Q (σ, m'.abs) := by
  obtain ⟨-, k, hk⟩ := step_simU hi hu hs
  exact sysMust_forward_stepNU hl hk hm

/-- The pieces of a successful `instantiateU`. -/
theorem instantiateU_some {fuel : Nat} {s ms : MStore} {m : Module} {imports : List ExternVal}
    {inst : ModuleInst} (h : instantiateU fuel s m imports = some (ms, inst)) :
    ∃ g t e m', Ref.initCandidates fuel s.abs m imports = some (g, t, e) ∧
      Ref.initAgrees fuel s.abs m imports g t e = true ∧
      MState.runU false fuel
        { store := (s.alloc m imports g t e).1, frame := ⟨[], (s.alloc m imports g t e).2⟩,
          stack := [], code := (initCode m).map .plain, ctl := [] } = (m', false) ∧
      m'.ending = .returned [] ∧ ms = m'.store ∧ inst = m'.frame.inst := by
  unfold instantiateU at h
  cases hc : Ref.initCandidates fuel s.abs m imports with
  | none => simp [hc] at h
  | some p =>
  obtain ⟨g, t, e⟩ := p
  cases ha : Ref.initAgrees fuel s.abs m imports g t e with
  | false => simp [hc, ha, guard] at h
  | true =>
  simp [hc, ha, guard] at h
  split at h
  · rename_i m' hr
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rename_i hend
      exact ⟨g, t, e, m', rfl, ha, hr, hend, rfl, rfl⟩
    · cases h
  · cases h

/-- T3(iii): `instantiateU` succeeds only where `instantiate` does, with its result. -/
theorem instantiateU_instantiate {fuel : Nat} {s ms : MStore} {m : Module}
    {imports : List ExternVal} {inst : ModuleInst}
    (h : instantiateU fuel s m imports = some (ms, inst)) :
    instantiate fuel s m imports = some (ms, inst) := by
  obtain ⟨g, t, e, m', hc, ha, hr, hend, rfl, rfl⟩ := instantiateU_some h
  have hrun := runU_run fuel hr (step_none_of_ending hend)
  simp [instantiate, initRun, hc, ha, guard, hrun, hend]

/-- A unique-step instantiation keeps the store invariant. -/
theorem instantiateU_inv {fuel : Nat} {s ms : MStore} {m : Module} {imports : List ExternVal}
    {inst : ModuleInst} (hi : s.Inv) (hmem : ∀ lim ∈ m.mems, lim.min ≤ 2 ^ 16)
    (h : instantiateU fuel s m imports = some (ms, inst)) : ms.Inv := by
  obtain ⟨g, t, e, m', -, -, hr, -, rfl, -⟩ := instantiateU_some h
  exact runU_inv fuel (m := MState.mk (s.alloc m imports g t e).1
    ⟨[], (s.alloc m imports g t e).2⟩ [] ((initCode m).map .plain) [])
    (alloc_inv hi hmem imports g t e) hr

/-- A valid module's memories fit 2^16 pages. -/
theorem mems_fit {m : Module} (hv : Valid.ModuleValid m) : ∀ lim ∈ m.mems, lim.min ≤ 2 ^ 16 :=
  fun lim hlim => (hv.mems lim hlim).1

/-- Contract U29b T3: a unique-step instantiation of a valid module is the only one — every
`Instantiated` witness ends in its store, with its instance. -/
theorem instantiateU_unique {H : HostSem} {fuel : Nat} {s ms : MStore} {m : Module}
    {imports : List ExternVal} {inst : ModuleInst} (hi : s.Inv) (hv : Valid.ModuleValid m)
    (h : instantiateU fuel s m imports = some (ms, inst)) {s' : Store} {inst' : ModuleInst}
    (h' : Instantiated H m s.abs imports s' inst') : s' = ms.abs ∧ inst' = inst := by
  have hmem := mems_fit hv
  obtain ⟨hm, g', t', e', s₁', halloc', hg', ht', he', hsteps'⟩ := h'
  obtain ⟨rfl, rfl⟩ : (allocModule s.abs m imports g' t' e').1 = s₁' ∧
      (allocModule s.abs m imports g' t' e').2 = inst' :=
    ⟨congrArg Prod.fst halloc', congrArg Prod.snd halloc'⟩
  have hsound := instantiate_sound (H := H) hi hmem hm (instantiateU_instantiate h)
  obtain ⟨g, t, e, m', -, ha, hr, hend, rfl, rfl⟩ := instantiateU_some h
  obtain ⟨rfl, rfl, rfl⟩ := Valid.InitProof.init_values_unique hv hm
    (Ref.initAgrees_sound (H := H) ha) ⟨hg', ht', he'⟩
  obtain ⟨-, g₂, t₂, e₂, s₂, halloc₂, -⟩ := hsound
  have hinst : m'.frame.inst = (allocModule s.abs m imports g t e).2 :=
    (congrArg Prod.snd halloc₂).symm.trans (Valid.InitProof.alloc_inst_eq _ _ _ _ _ _ _ _ _)
  refine ⟨?_, hinst.symm⟩
  obtain ⟨hs₁, hinst₁⟩ := alloc_abs s m imports g t e
  have hi₀ : MState.Inv (MState.mk (s.alloc m imports g t e).1
      ⟨[], (s.alloc m imports g t e).2⟩ [] ((initCode m).map .plain) []) :=
    alloc_inv hi hmem imports g t e
  have hfin : Final m'.abs (.returned m'.store.abs []) := by
    obtain ⟨hctl, hcode, hstk⟩ := ending_returned hend
    refine ⟨rfl, ?_⟩
    simp [abs_eq_wrapC, wrapC, wrap, hctl, hcode, hstk]
  have hmust := machineRun_must (H := H) (Q := (· = .returned m'.store.abs [])) hi₀ hr hfin rfl
  have habs₀ : (MState.mk (s.alloc m imports g t e).1 ⟨[], (s.alloc m imports g t e).2⟩ []
      ((initCode m).map .plain) []).abs =
      ⟨(allocModule s.abs m imports g t e).1, ⟨[], (allocModule s.abs m imports g t e).2⟩,
        (initCode m).map .plain⟩ := by
    rw [← hs₁, ← hinst₁]
    simp [abs_eq_wrapC, wrapC, wrap]
  rw [habs₀] at hmust
  have hq := hmust.final hsteps' (o := .returned s' []) ⟨rfl, rfl⟩
  simp only [Outcome.returned.injEq, and_true] at hq
  exact hq

end FVA.Wasm.Exec.Machine
