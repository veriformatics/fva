import FVA.Proof.Exec.Machine
import FVA.Proof.Exec.System

/-!
# Machine runs and process claims (contract U27 T5)

`runU fits` steps the machine while each step is no choice point under `fits` (reference steps,
each the spec's only successor: `step_simU`) or an administrative throw step (a choice point
whose every choice reaches the same handler, or the top, with the same exception: `must_admin`,
`sysMust_admin`, contract U28d T3), so `Must` (`fits = false`) and `SysMust` (the world kept)
transfer back over it (`runU_must`, `runU_sysMust`; `machineRun_must`,
`machineSegment_sysMust`). Fuel exhaustion and a choice point both end a run as a prefix,
never as termination.
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

theorem step_simU {fits : Bool} {m m' : MState} (hi : m.Inv) (hu : m.uniq fits = true)
    (h : m.step = some m') : m'.Inv ∧ ∃ k, stepNU fits k m.abs = some m'.abs := by
  obtain ⟨hi', k, -, hU⟩ := step_sim hi h
  refine ⟨hi', ?_⟩
  rcases m with ⟨st, f, stk, code, ctl⟩
  cases code with
  | cons e rest =>
    cases hv : Ref.toVal e with
    | some v =>
      simp only [MState.step, hv, Option.some.injEq] at h
      subst h
      refine ⟨0, ?_⟩
      have he := Ref.eq_instr_of_toVal hv
      subst he
      simp only [stepNU, abs_eq_wrapC, vals_cons_reverse, List.append_assoc,
        List.singleton_append]
    | none =>
      refine ⟨k, hU fits ?_⟩
      rw [abs_eq_wrapC, uniqueStep_wrapC]
      simp only [Ref.uniqueStep, Ref.seqUnique_vals, List.reverse_reverse, List.append_nil,
        Ref.seqUnique, hv]
      simp only [MState.uniq, hv] at hu
      cases e with
      | plain i =>
        by_cases ht : i = .throwRef
        · subst ht
          simp only [Ref.atUnique]
          revert hu
          rcases stk with _ | ⟨v, stk⟩
          · simp
          · cases v with
            | ref r => cases r <;> simp
            | _ => simp
        · simpa [Ref.atUnique_plain ht] using hu
      | invoke a =>
        simp only [Ref.atUnique, MStore.abs]
        cases hf : st.base.funcs[a]? with
        | none => simp [hf] at hu
        | some fi => cases fi <;> simp_all
      | returnInvoke a => simp [Ref.atUnique]
      | _ => simp at hu
  | nil =>
    refine ⟨k, hU fits ?_⟩
    rw [abs_eq_wrapC, uniqueStep_wrapC]
    simp only [Ref.uniqueStep, List.append_nil]
    have := Ref.seqUnique_vals fits st.abs f [] stk.reverse []
    simp only [List.append_nil] at this
    rw [this]
    rfl

theorem sysMust_of_stepNU {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    (hl : W.exited σ = none) : ∀ {k : Nat} {c c' : Config}, stepNU fits k c = some c' →
      SysMust W fits Q (σ, c') → SysMust W fits Q (σ, c)
  | 0, c, c', h, hm => by
    simp only [stepNU, Option.some.injEq] at h
    subst h
    exact hm
  | k + 1, c, c', h, hm => by
    simp only [stepNU] at h
    cases hu : Ref.uniqueStep fits c
    · simp [hu] at h
    · simp only [hu, Bool.cond_true] at h
      cases hs : Ref.step c with
      | none => simp [hs] at h
      | some c₁ =>
        simp only [hs, Option.bind_some] at h
        exact sysMust_of_step hl hs hu (sysMust_of_stepNU hl h hm)

theorem must_of_stepNU {H : HostSem} {Q : Outcome → Prop} : ∀ {k : Nat} {c c' : Config},
    stepNU false k c = some c' → Must H Q c' → Must H Q c
  | 0, c, c', h, hm => by
    simp only [stepNU, Option.some.injEq] at h
    subst h
    exact hm
  | k + 1, c, c', h, hm => by
    simp only [stepNU] at h
    cases hu : Ref.uniqueStep false c
    · simp [hu] at h
    · simp only [hu, Bool.cond_true] at h
      cases hs : Ref.step c with
      | none => simp [hs] at h
      | some c₁ =>
        simp only [hs, Option.bind_some] at h
        exact Ref.must_of_step hs hu (must_of_stepNU h hm)

theorem isThrowing_layer (vs : List Val) {e : AInstr} (rest : List AInstr)
    (he : ∀ a, e ≠ .refExnAddr a) (he' : e ≠ .plain .throwRef) :
    Ref.isThrowing (vals vs ++ e :: rest) = false := by
  cases h : Ref.isThrowing (vals vs ++ e :: rest)
  · rfl
  · obtain ⟨a, ha⟩ := Ref.isThrowing_eq_true.mp h
    have hm : e ∈ throwing a := ha ▸ (by simp)
    simp only [throwing, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm
    · exact absurd hm (he a)
    · exact absurd hm he'

theorem seqThrow_layer {es : List AInstr} (c : Ctl) (f : Frame) (hr : Ref.seqThrow [] es ≠ none)
    (hn : Ref.isThrowing es = false) :
    Ref.seqThrow [] (layer c f es).2 ≠ none ∧ Ref.isThrowing (layer c f es).2 = false := by
  cases c with
  | label n cont saved rest =>
    have hn' := isThrowing_layer saved.reverse (e := .label n cont es) rest
      (fun _ h => by cases h) (fun h => by cases h)
    refine ⟨?_, by simpa only [layer, List.append_assoc, List.singleton_append] using hn'⟩
    simp only [layer, List.append_assoc, Ref.seqThrow_vals, List.singleton_append, Ref.seqThrow,
      Ref.toVal, Ref.atThrow]
    cases h : Ref.seqThrow [] es with
    | none => exact absurd h hr
    | some r => cases r <;> simp
  | frame n caller saved rest =>
    have hn' := isThrowing_layer saved.reverse (e := .frame n f es) rest
      (fun _ h => by cases h) (fun h => by cases h)
    refine ⟨?_, by simpa only [layer, List.append_assoc, List.singleton_append] using hn'⟩
    simp only [layer, List.append_assoc, Ref.seqThrow_vals, List.singleton_append, Ref.seqThrow,
      Ref.toVal, Ref.atThrow]
    cases h : Ref.seqThrow [] es with
    | none => exact absurd h hr
    | some r => cases r <;> simp
  | handler n cs saved rest =>
    have hn' := isThrowing_layer saved.reverse (e := .handler n cs es) rest
      (fun _ h => by cases h) (fun h => by cases h)
    refine ⟨?_, by simpa only [layer, List.append_assoc, List.singleton_append] using hn'⟩
    simp only [layer, List.append_assoc, Ref.seqThrow_vals, List.singleton_append, Ref.seqThrow,
      Ref.toVal, Ref.atThrow]
    cases h : Ref.seqThrow [] es with
    | none => exact absurd h hr
    | some r => cases r <;> simp [hn]

/-- A pending throw that is not alone in its block stays pending through every control
entry: each layer passes it out, a handler turns it into its boundary (`Ref.seqThrow`). -/
theorem seqThrow_wrap : ∀ (ctl : List Ctl) (f : Frame) (es : List AInstr),
    Ref.seqThrow [] es ≠ none → Ref.isThrowing es = false →
    Ref.seqThrow [] (wrap ctl f es).2 ≠ none
  | [], _, _, h, _ => h
  | c :: ctl, f, es, hr, hn => by
    rw [wrap_cons]
    obtain ⟨hr', hn'⟩ := seqThrow_layer c f hr hn
    exact seqThrow_wrap ctl _ _ hr' hn'

theorem admin_parts {m : MState} (ha : m.admin = true) :
    ∃ a stk rest, m.code = .plain .throwRef :: rest ∧ m.stack = .ref (.exn a) :: stk ∧
      (stk.isEmpty && rest.isEmpty) = false := by
  unfold MState.admin at ha
  split at ha
  · next rest a stk hc hs =>
    refine ⟨a, stk, rest, hc, hs, ?_⟩
    cases hb : (stk.isEmpty && rest.isEmpty) <;> simp_all
  · simp at ha

/-- An administrative throw step: one reference step from a configuration with a pending throw,
the store kept. -/
theorem admin_step {m m' : MState} (ha : m.admin = true) (h : m.step = some m') :
    m'.store = m.store ∧ Ref.step m.abs = some m'.abs ∧
      ∃ r, Ref.seqThrow [] m.abs.instrs = some r := by
  obtain ⟨a, stk, rest, hc, hs, hb⟩ := admin_parts ha
  have hm' : m' = m.cont [.ref (.exn a)] [.plain .throwRef] [] := by
    simp only [MState.step, hc, Ref.toVal, MState.stepPlain, hs, hb, Bool.cond_false,
      Option.some.injEq] at h
    exact h.symm
  subst hm'
  refine ⟨rfl, step_admin hc hs hb, ?_⟩
  rw [abs_eq_wrapC, ← Option.ne_none_iff_exists']
  apply seqThrow_wrap
  · rw [hs, hc, Ref.seqThrow_vals]
    simp [Ref.seqThrow, Ref.toVal, Ref.atThrow]
  · cases h : Ref.isThrowing (vals m.stack.reverse ++ m.code)
    · rfl
    · obtain ⟨a', ha'⟩ := Ref.isThrowing_eq_true.mp h
      have hl := congrArg List.length ha'
      rw [hs, hc] at hl
      simp only [List.length_append, vals, List.length_map, List.length_reverse, List.length_cons,
        throwing, List.length_nil] at hl
      have : stk = [] ∧ rest = [] := ⟨List.length_eq_zero_iff.mp (by omega),
        List.length_eq_zero_iff.mp (by omega)⟩
      obtain ⟨rfl, rfl⟩ := this
      simp at hb

/-- Contract U28d T3: `Must` after an administrative throw step gives `Must` before it. -/
theorem must_admin {H : HostSem} {Q : Outcome → Prop} {m m' : MState} (ha : m.admin = true)
    (h : m.step = some m') (hm : Must H Q m'.abs) : Must H Q m.abs := by
  obtain ⟨-, hstep, r, hr⟩ := admin_step ha h
  exact Ref.must_of_throwStep (Ref.step_sound hstep) hr hm

/-- Contract U28d T3: `SysMust` after an administrative throw step of a live process gives
`SysMust` before it, under either growth policy. -/
theorem sysMust_admin {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {m m' : MState} (hl : W.exited σ = none) (ha : m.admin = true) (h : m.step = some m')
    (hm : SysMust W fits Q (σ, m'.abs)) : SysMust W fits Q (σ, m.abs) := by
  obtain ⟨-, hstep, r, hr⟩ := admin_step ha h
  exact sysMust_of_throwStep hl (Ref.step_sound hstep) hr hm

/-- A run that stops at a choice point, a final state or exhausted fuel transfers `Must` from
where it stops back to its start (unique steps + administrative throw steps). -/
theorem runU_must {H : HostSem} {Q : Outcome → Prop} : ∀ (n : Nat) {m m' : MState} {b : Bool},
    m.Inv → m.runU false n = (m', b) → Must H Q m'.abs → Must H Q m.abs
  | 0, m, m', b, _, h, hm => by
    simp only [MState.runU, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hm
  | n + 1, m, m', b, hi, h, hm => by
    simp only [MState.runU] at h
    cases hs : m.step with
    | none =>
      have h' : (m, false) = (m', b) := by
        cases m.uniq false || m.admin <;> simpa [hs] using h
      cases h'
      exact hm
    | some m₁ =>
      have hi₁ := (step_sim hi hs).1
      cases hu : m.uniq false
      · cases ha : m.admin
        · simp only [hu, ha, Bool.or_self, Bool.cond_false, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact hm
        · simp only [hu, ha, Bool.or_true, Bool.cond_true, hs] at h
          exact must_admin ha hs (runU_must n hi₁ h hm)
      · simp only [hu, Bool.true_or, Bool.cond_true, hs] at h
        obtain ⟨-, k₁, hk₁⟩ := step_simU hi hu hs
        exact must_of_stepNU hk₁ (runU_must n hi₁ h hm)

/-- A segment of a live process (unique steps + administrative throw steps) transfers `SysMust`
from where it stops back to its start, the world kept. -/
theorem runU_sysMust {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    (hl : W.exited σ = none) : ∀ (n : Nat) {m m' : MState} {b : Bool},
      m.Inv → m.runU fits n = (m', b) → SysMust W fits Q (σ, m'.abs) →
      SysMust W fits Q (σ, m.abs)
  | 0, m, m', b, _, h, hm => by
    simp only [MState.runU, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hm
  | n + 1, m, m', b, hi, h, hm => by
    simp only [MState.runU] at h
    cases hs : m.step with
    | none =>
      have h' : (m, false) = (m', b) := by
        cases m.uniq fits || m.admin <;> simpa [hs] using h
      cases h'
      exact hm
    | some m₁ =>
      have hi₁ := (step_sim hi hs).1
      cases hu : m.uniq fits
      · cases ha : m.admin
        · simp only [hu, ha, Bool.or_self, Bool.cond_false, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact hm
        · simp only [hu, ha, Bool.or_true, Bool.cond_true, hs] at h
          exact sysMust_admin hl ha hs (runU_sysMust hl n hi₁ h hm)
      · simp only [hu, Bool.true_or, Bool.cond_true, hs] at h
        obtain ⟨-, k₁, hk₁⟩ := step_simU hi hu hs
        exact sysMust_of_stepNU hl hk₁ (runU_sysMust hl n hi₁ h hm)

/-- Contract U27 T5 (U26 T3): a machine run that finishes, each step no choice point, gives
total correctness of its starting configuration. -/
theorem machineRun_must {H : HostSem} {Q : Outcome → Prop} {m m' : MState} {n : Nat} {b : Bool}
    {o : Outcome} (hi : m.Inv) (h : m.runU false n = (m', b)) (hf : Final m'.abs o) (hq : Q o) :
    Must H Q m.abs :=
  runU_must n hi h (.done hf hq)

/-- A machine segment of a live process: `SysMust` at its end transfers to its start, the world
kept (a segment stops at a host call, a trap, a final state or a choice point). -/
theorem machineSegment_sysMust {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop}
    {σ : W.St} {m m' : MState} {n : Nat} {b : Bool} (hi : m.Inv) (hl : W.exited σ = none)
    (h : m.runU fits n = (m', b)) (hm : SysMust W fits Q (σ, m'.abs)) :
    SysMust W fits Q (σ, m.abs) :=
  runU_sysMust hl n hi h hm

/-! ## Host calls on the machine -/

/-- The host-call context one control entry adds (`layer`'s). -/
def layerK : Ctl → Frame → Ref.HCtx → Ref.HCtx
  | .label n cont saved rest, _, K => .seq saved.reverse (.label n cont K) rest
  | .frame n _ saved rest, f, K => .seq saved.reverse (.frame n f K) rest
  | .handler n cs saved rest, _, K => .seq saved.reverse (.handler n cs K) rest

theorem layer_fst (c : Ctl) (f : Frame) (es es' : List AInstr) :
    (layer c f es).1 = (layer c f es').1 := by
  cases c <;> rfl

theorem layerK_fill (c : Ctl) (f : Frame) (K : Ref.HCtx) (es : List AInstr) :
    (layerK c f K).fill es = (layer c f (K.fill es)).2 := by
  cases c <;> simp [layerK, layer, Ref.HCtx.fill, List.append_assoc]

theorem seq_layer_host {S : Store} {f : Frame} {es : List AInstr} {a : Nat} {args : List Val}
    {K : Ref.HCtx} (c : Ctl) (h : Ref.seq S f [] es = .host a args K) :
    Ref.seq S (layer c f es).1 [] (layer c f es).2 = .host a args (layerK c f K) := by
  cases c with
  | label n cont saved rest =>
    simp only [layer, layerK, List.append_assoc, Ref.seq_vals, List.append_nil,
      List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h, List.reverse_reverse]
  | frame n caller saved rest =>
    simp only [layer, layerK, List.append_assoc, Ref.seq_vals, List.append_nil,
      List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h, List.reverse_reverse]
  | handler n cs saved rest =>
    simp only [layer, layerK, List.append_assoc, Ref.seq_vals, List.append_nil,
      List.singleton_append, Ref.seq, Ref.toVal, Ref.atInstr, h, List.reverse_reverse]

/-- The host-call context through the whole control stack. -/
def wrapK : List Ctl → Frame → Ref.HCtx → Ref.HCtx
  | [], _, K => K
  | c :: ctl, f, K => wrapK ctl (layer c f []).1 (layerK c f K)

theorem wrap_fst (ctl : List Ctl) (f : Frame) (es es' : List AInstr) :
    (wrap ctl f es).1 = (wrap ctl f es').1 := by
  induction ctl generalizing f es es' with
  | nil => rfl
  | cons c ctl ih =>
    rw [wrap_cons, wrap_cons, layer_fst c f es es']
    exact ih _ _ _

theorem wrapK_fill (ctl : List Ctl) (f : Frame) (K : Ref.HCtx) (es : List AInstr) :
    (wrapK ctl f K).fill es = (wrap ctl f (K.fill es)).2 := by
  induction ctl generalizing f K with
  | nil => rfl
  | cons c ctl ih =>
    simp only [wrapK, wrap_cons]
    rw [ih, layerK_fill, layer_fst c f [] (K.fill es)]

theorem seq_wrap_host {S : Store} {f : Frame} {es : List AInstr} {a : Nat} {args : List Val}
    {K : Ref.HCtx} (ctl : List Ctl) (h : Ref.seq S f [] es = .host a args K) :
    Ref.seq S (wrap ctl f es).1 [] (wrap ctl f es).2 = .host a args (wrapK ctl f K) := by
  induction ctl generalizing f es K with
  | nil => simpa [wrap, wrapK] using h
  | cons c ctl ih =>
    rw [wrap_cons, layer_fst c f es []]
    have h' := seq_layer_host c h
    rw [layer_fst c f es []] at h'
    exact ih h'

/-- At a host call the stepper's focus is that call in the machine's contexts, and each
outcome's continuation is the resumed machine's abstraction (contract U27 T5). -/
theorem abs_host {m : MState} {a : Nat} {rest : List AInstr} {dt : DefType} {ft : FuncType}
    {id : Nat} (hc : m.code = .invoke a :: rest) (hf : m.store.base.funcs[a]? = some (.host dt id))
    (hft : dt.expand = some ft) (hk : ft.params.length ≤ m.stack.length) :
    ∃ K, Ref.seq m.abs.store m.abs.frame [] m.abs.instrs =
        .host a (m.stack.take ft.params.length).reverse K ∧
      ∀ (ms : MStore) (out : List AInstr),
        (m.hostResume ms out rest ft.params.length).abs = ⟨ms.abs, m.abs.frame, K.fill out⟩ := by
  have hS : m.store.abs.funcs[a]? = some (.host dt id) := hf
  have hin : Ref.seq m.store.abs m.frame [] (vals m.stack.reverse ++ m.code) =
      .host a (m.stack.take ft.params.length).reverse
        (.seq (m.stack.drop ft.params.length).reverse .hole rest) := by
    rw [hc, seq_focus _ _ _ _ rfl]
    simp only [Ref.atInstr, hS, hft, MMem.blt_false hk, Bool.cond_false]
  refine ⟨wrapK m.ctl m.frame (.seq (m.stack.drop ft.params.length).reverse .hole rest), ?_,
    fun ms out => ?_⟩
  · rw [abs_eq_wrapC]
    exact seq_wrap_host m.ctl hin
  · simp only [MState.hostResume, abs_eq_wrapC, wrapC, wrapK_fill, Ref.HCtx.fill,
      List.append_assoc]
    rw [wrap_fst m.ctl m.frame _ (vals m.stack.reverse ++ m.code)]

theorem hostCall_some {m : MState} {id k : Nat} {rest : List AInstr}
    (h : m.hostCall = some (id, k, rest)) :
    ∃ a dt ft, m.code = .invoke a :: rest ∧ m.store.base.funcs[a]? = some (.host dt id) ∧
      dt.expand = some ft ∧ k = ft.params.length ∧ k ≤ m.stack.length := by
  unfold MState.hostCall at h
  split at h
  · next a rest' hc =>
    split at h
    · next dt id' hf =>
      cases hft : dt.expand with
      | none => simp [hft] at h
      | some ft =>
        simp only [hft, Option.bind_some] at h
        cases hb : Nat.blt m.stack.length ft.params.length
        · simp only [hb, Bool.cond_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨a, dt, ft, hc, hf, hft, rfl, le_of_blt_false hb⟩
        · simp [hb] at h
    · simp at h
  · simp at h

/-- `X` = an executable host for world `W`: on an invariant store its result keeps the
invariant, is allowed, and is the only allowed (world, outcome) pair. -/
def HostOK (W : World) (X : W.St → Nat → MStore → List Val → Option (W.St × MStore × MHostOut)) :
    Prop :=
  ∀ σ id s args τ ms r, X σ id s args = some (τ, ms, r) → s.Inv →
    ms.Inv ∧ W.host σ τ id s.abs args (r.spec ms) ∧
    ∀ τ' o, W.host σ τ' id s.abs args o → τ' = τ ∧ o = r.spec ms

/-- Contract U27 T5: a process run on the machine with a host whose every result is the only
allowed one transfers `SysMust` from where it stops (a finished, exited or trapping state, or any
prefix) back to its start (fitting growth granted). -/
theorem machineRun_sysMust {W : World} {Q : SysOutcome W.St → Prop}
    {X : W.St → Nat → MStore → List Val → Option (W.St × MStore × MHostOut)} (hX : HostOK W X) :
    ∀ (n : Nat) {σ σ' : W.St} {m m' : MState} {b : Bool}, m.Inv →
      sysRun W.exited X n (σ, m) = (σ', m', b) → SysMust W true Q (σ', m'.abs) →
      SysMust W true Q (σ, m.abs)
  | 0, σ, σ', m, m', b, _, h, hend => by
    simp only [sysRun, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact hend
  | n + 1, σ, σ', m, m', b, hi, h, hend => by
    cases he : W.exited σ with
    | some k =>
      simp only [sysRun, he, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact hend
    | none =>
      cases hh : m.hostCall with
      | some p =>
        obtain ⟨id, k, rest⟩ := p
        cases hx : X σ id m.store (m.stack.take k).reverse with
        | none =>
          simp only [sysRun, he, hh, hx, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact hend
        | some r =>
          obtain ⟨τ, ms, out⟩ := r
          simp only [sysRun, he, hh, hx] at h
          obtain ⟨a, dt, ft, hc, hfn, hft, rfl, hk⟩ := hostCall_some hh
          obtain ⟨hinv, hok, hsingle⟩ := hX σ id m.store _ τ ms out hx hi
          obtain ⟨K, hq', hcont⟩ := abs_host hc hfn hft hk
          have hfa : m.abs.store.funcs[a]? = some (.host dt id) := hfn
          refine sysMust_host hq' hfa he ⟨τ, out.spec ms, hok⟩ fun τ' o' hW => ?_
          obtain ⟨rfl, rfl⟩ := hsingle τ' o' hW
          have heq : (⟨Ref.hostStore m.abs.store (out.spec ms), m.abs.frame,
              K.result a (m.stack.take ft.params.length).reverse (out.spec ms)⟩ : Config) =
              (m.hostResume ms out.out rest ft.params.length).abs := by
            rw [hcont]
            cases out <;> rfl
          rw [heq]
          exact machineRun_sysMust hX n hinv h hend
      | none =>
        cases hs : m.step with
        | none =>
          have h' : (σ, m, false) = (σ', m', b) := by
            cases m.uniq true || m.admin <;> simpa [sysRun, he, hh, hs] using h
          cases h'
          exact hend
        | some m₁ =>
          have hi₁ := (step_sim hi hs).1
          cases hu : m.uniq true
          · cases ha : m.admin
            · simp only [sysRun, he, hh, hu, ha, Bool.or_self, Bool.cond_false,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, -⟩ := h
              exact hend
            · simp only [sysRun, he, hh, hu, ha, Bool.or_true, Bool.cond_true, hs] at h
              exact sysMust_admin he ha hs (machineRun_sysMust hX n hi₁ h hend)
          · simp only [sysRun, he, hh, hu, Bool.true_or, Bool.cond_true, hs] at h
            obtain ⟨-, k₁, hk₁⟩ := step_simU hi hu hs
            exact sysMust_of_stepNU he hk₁ (machineRun_sysMust hX n hi₁ h hend)

end FVA.Wasm.Exec.Machine
