import FVA.Proof.Exec.Machine
import FVA.Proof.Exec.System

/-!
# Machine runs and process claims (contract U27 T5)

`runU fits` steps the machine while each step is no choice point under `fits`; such a run is
reference steps that are each the spec's only successor (`runU_sim`), so `Must` (`fits = false`)
and `SysMust` (the world kept) transfer back over it (`machineRun_must`,
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
          simp [MState.step, hv, MState.stepPlain, Ref.instrStep] at h
        · simpa [Ref.atUnique_plain ht] using hu
      | invoke a =>
        simp only [Ref.atUnique, MStore.abs]
        cases hf : st.base.funcs[a]? with
        | none => simp [hf] at hu
        | some fi => cases fi <;> simp_all
      | _ => simp at hu
  | nil =>
    refine ⟨k, hU fits ?_⟩
    rw [abs_eq_wrapC, uniqueStep_wrapC]
    simp only [Ref.uniqueStep, List.append_nil]
    have := Ref.seqUnique_vals fits st.abs f [] stk.reverse []
    simp only [List.append_nil] at this
    rw [this]
    rfl

/-- A run that stops at a choice point, a final state or exhausted fuel = unique reference
steps between the abstractions. -/
theorem runU_sim {fits : Bool} : ∀ (n : Nat) {m m' : MState} {b : Bool}, m.Inv →
    m.runU fits n = (m', b) → m'.Inv ∧ ∃ k, stepNU fits k m.abs = some m'.abs
  | 0, m, m', b, hi, h => by
    simp only [MState.runU, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hi, 0, rfl⟩
  | n + 1, m, m', b, hi, h => by
    simp only [MState.runU] at h
    cases hu : m.uniq fits
    · simp only [hu, Bool.cond_false, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hi, 0, rfl⟩
    · simp only [hu, Bool.cond_true] at h
      cases hs : m.step with
      | none =>
        simp only [hs, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hi, 0, rfl⟩
      | some m₁ =>
        simp only [hs] at h
        obtain ⟨hi₁, k₁, hk₁⟩ := step_simU hi hu hs
        obtain ⟨hi', k₂, hk₂⟩ := runU_sim n hi₁ h
        exact ⟨hi', k₁ + k₂, by rw [stepNU_add, hk₁, Option.bind_some, hk₂]⟩

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

/-- Contract U27 T5 (U26 T3): a machine run that finishes, each step no choice point, gives
total correctness of its starting configuration. -/
theorem machineRun_must {H : HostSem} {Q : Outcome → Prop} {m m' : MState} {n : Nat} {b : Bool}
    {o : Outcome} (hi : m.Inv) (h : m.runU false n = (m', b)) (hf : Final m'.abs o) (hq : Q o) :
    Must H Q m.abs := by
  obtain ⟨-, k, hk⟩ := runU_sim n hi h
  exact must_of_stepNU hk (.done hf hq)

/-- A machine segment of a live process: `SysMust` at its end transfers to its start, the world
kept (a segment stops at a host call, a trap, a final state or a choice point). -/
theorem machineSegment_sysMust {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop}
    {σ : W.St} {m m' : MState} {n : Nat} {b : Bool} (hi : m.Inv) (hl : W.exited σ = none)
    (h : m.runU fits n = (m', b)) (hm : SysMust W fits Q (σ, m'.abs)) :
    SysMust W fits Q (σ, m.abs) := by
  obtain ⟨-, k, hk⟩ := runU_sim n hi h
  exact sysMust_of_stepNU hl hk hm

/-! ## Host calls on the machine -/

/-- The host-call context one control entry adds (`layer`'s). -/
def layerK : Ctl → Frame → Ref.HCtx → Ref.HCtx
  | .label n cont saved rest, _, K => .seq saved.reverse (.label n cont K) rest
  | .frame n _ saved rest, f, K => .seq saved.reverse (.frame n f K) rest

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
        cases hu : m.uniq true
        · simp only [sysRun, he, hh, hu, Bool.cond_false, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact hend
        · cases hs : m.step with
          | none =>
            simp only [sysRun, he, hh, hu, hs, Bool.cond_true, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact hend
          | some m₁ =>
            simp only [sysRun, he, hh, hu, hs, Bool.cond_true] at h
            obtain ⟨hi₁, k₁, hk₁⟩ := step_simU hi hu hs
            exact sysMust_of_stepNU he hk₁ (machineRun_sysMust hX n hi₁ h hend)

end FVA.Wasm.Exec.Machine
