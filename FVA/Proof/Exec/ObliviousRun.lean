import FVA.Proof.Exec.ObliviousStep
import FVA.Proof.Wasi.Host

/-!
# Data-oblivious framing: a certified run (contract U28g F1 `sysRun_put`)

A `trun` certificate over `n` transitions of `sysRun` with the executable WASI host transfers
`SysMust` from the patched end state back to the patched start state: every state alike the
patched one runs the same transitions (`step_put`, `host_put`), its world identical.
-/

namespace FVA.Wasm.Exec.Machine.Oblivious

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- Patches riding positions `ps` with values `vs`: each present position with its value. -/
def ride : List (Option Pos) → List TVal → List (Pos × TVal)
  | some p :: ps, v :: vs => (p, v) :: ride ps vs
  | none :: ps, _ :: vs => ride ps vs
  | _, _ => []

theorem ride_bind (F : PMap) : ∀ (ps : List (Option Pos)) (vs : List TVal),
    ride (ps.map (·.bind F)) vs = move F (ride ps vs)
  | [], _ => rfl
  | some p :: _, [] => by simp only [List.map_cons, Option.bind_some]; cases F p <;> rfl
  | none :: _, [] => rfl
  | none :: ps, _ :: vs => by simp only [List.map_cons, Option.bind_none, ride, ride_bind F ps vs]
  | some p :: ps, v :: vs => by
    have ih := ride_bind F ps vs
    rw [show ride (some p :: ps) (v :: vs) = (p, v) :: ride ps vs from rfl, move_cons, ← ih]
    simp only [List.map_cons, Option.bind_some]
    cases F p <;> rfl

theorem ride_mem : ∀ {ps : List (Option Pos)} {vs : List TVal} {t : Pos × TVal},
    t ∈ ride ps vs → t.1 ∈ ps.filterMap id
  | some p :: ps, v :: vs, t, h => by
    simp only [ride, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · simp only [List.filterMap_cons, id, List.mem_cons]; exact .inr (ride_mem h)
  | none :: ps, _ :: vs, t, h => by
    simp only [ride] at h
    simp only [List.filterMap_cons, id]; exact ride_mem h
  | [], _, _, h | some _ :: _, [], _, h | none :: _, [], _, h => by simp [ride] at h

theorem ride_val_mem : ∀ {ps : List (Option Pos)} {vs : List TVal} {t : Pos × TVal},
    t ∈ ride ps vs → t.2 ∈ vs
  | some p :: ps, v :: vs, t, h => by
    simp only [ride, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ride_val_mem h)
  | none :: ps, _ :: vs, t, h => by
    simp only [ride] at h; exact List.mem_cons_of_mem _ (ride_val_mem h)
  | [], _, _, h | some _ :: _, [], _, h | none :: _, [], _, h => by simp [ride] at h

/-- Every byte value is a byte. -/
def ValsOK (vs : List TVal) : Prop := ∀ b, TVal.byte b ∈ vs → b < 256

theorem bytesOK_of_posOK {m : MState} {ps : List (Option Pos)} {vs : List TVal} (hv : ValsOK vs)
    (h : (ps.filterMap id).all (posOK m) = true) : BytesOK (ride ps vs) m.store.mems := by
  intro mi a b ht
  have hp := List.all_eq_true.mp h _ (ride_mem ht)
  refine ⟨hv b (ride_val_mem ht), ?_⟩
  simp only [posOK] at hp
  split at hp
  · rename_i mm hmm
    exact ⟨mm, hmm, by simpa [Nat.blt_eq] using hp⟩
  · simp at hp

theorem ctlBound_of_posOK {m : MState} {ps : List (Option Pos)} {vs : List TVal}
    (h : (ps.filterMap id).all (posOK m) = true) : CtlBound (ride ps vs) m.ctl.length := by
  intro t ht k hk
  have hp := List.all_eq_true.mp h _ (ride_mem ht)
  obtain ⟨p, v⟩ := t
  cases p <;> simp only [Pos.ctlIdx, reduceCtorEq, Option.some.injEq] at hk <;> subst hk <;>
    simpa [posOK, Nat.blt_eq] using hp

/-! ## Alike states run alike -/

theorem memEqv_refl (mm : MMem) : MemEqv mm mm := ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem eqv_refl (m : MState) : Eqv m m := by
  refine ⟨?_, rfl⟩
  induction m.store.mems with
  | nil => exact .nil
  | cons a l ih => exact .cons (memEqv_refl a) ih

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    l₁.map f = l₂.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hr => by simp only [List.map_cons, hfg _ _ h, forall₂_map_eq hfg hr]

theorem eqv_abs {P Q : MState} (h : Eqv P Q) : P.abs = Q.abs := by
  have hm := forall₂_map_eq (f := MMem.abs) (g := MMem.abs)
    (fun a b (e : MemEqv a b) => MMem.abs_ext e.1 e.2.1 e.2.2.2) h.1
  rw [eqv_iff] at h
  obtain ⟨-, hb, hf, hs, hc, hk⟩ := h
  have hst : P.store.abs = Q.store.abs := by
    simp only [MStore.abs, hm]
    exact base_congr hb _
  simp only [MState.abs, hst, hf, hs, hc, hk]

theorem put_inv {m : MState} {ts : List (Pos × TVal)} (hi : m.Inv) (hok : BytesOK ts m.store.mems) :
    (put ts m).Inv := by
  rw [put_eq]
  exact (putMems_spec ts m.store.mems hi hok).1

theorem hostCall_put (ts : List (Pos × TVal)) (m : MState) : (put ts m).hostCall = m.hostCall := by
  rw [put_eq]; rfl

theorem uniq_eqv {m P : MState} {ts : List (Pos × TVal)} (hP : Eqv P (put ts m)) (fits : Bool) :
    P.uniq fits = m.uniq fits ∧ P.admin = m.admin := by
  rw [put_eq, eqv_iff] at hP
  obtain ⟨-, hPb, -, hPs, hPc, -⟩ := hP
  have hfuncs : P.store.base.funcs = m.store.base.funcs := by simpa using congrArg Store.funcs hPb
  simp only at hPs hPc
  exact ⟨by simp only [MState.uniq, hPc, hPs, hfuncs], by simp only [MState.admin, hPc, hPs]⟩

/-- `sysRun_put`'s core (contract F1): over a `trun`-certified run, a state alike the patched
start runs to a state alike the patched end, through the same worlds. -/
theorem run_put {md : Module} {mem : Nat} : ∀ (n : Nat) {σ : State} {m P : MState}
    {ps qs : List (Option Pos)} {vs : List TVal}, trun md mem ps n (σ, m) = some qs →
    m.Inv → P.Inv → ValsOK vs → Eqv P (put (ride ps vs) m) →
    (sysRun State.exited (wasiHost md mem none) n (σ, P)).1 =
        (sysRun State.exited (wasiHost md mem none) n (σ, m)).1 ∧
      Eqv (sysRun State.exited (wasiHost md mem none) n (σ, P)).2.1
        (put (ride qs vs) (sysRun State.exited (wasiHost md mem none) n (σ, m)).2.1)
  | 0, σ, m, P, ps, qs, vs, ht, _, _, _, hP => by
    simp only [trun, Option.some.injEq] at ht
    subst ht
    exact ⟨rfl, hP⟩
  | n + 1, σ, m, P, ps, qs, vs, ht, hi, hPi, hv, hP => by
    have hPh := hostCall_eqv hP
    have hPstk : P.stack = m.stack := by
      have := hP; rw [put_eq, eqv_iff] at this; simpa using this.2.2.2.1
    cases hex : σ.exited with
    | some k => simp [trun, hex] at ht
    | none =>
      simp only [trun, hex] at ht
      cases hpos : (ps.filterMap id).all (posOK m) with
      | false => simp only [hpos, Bool.not_false, Bool.cond_true, reduceCtorEq] at ht
      | true =>
        simp only [hpos, Bool.not_true, Bool.cond_false] at ht
        have hok := bytesOK_of_posOK hv hpos
        have hb := ctlBound_of_posOK (vs := vs) hpos
        have hsup : ∀ t ∈ ride ps vs, t.1 ∈ ps.filterMap id := fun _ ht => ride_mem ht
        cases hh : m.hostCall with
        | some c =>
          obtain ⟨id, k, rest⟩ := c
          simp only [hh] at ht
          cases hmap : hostMap md mem σ id m.store ((m.stack.take k).reverse) with
          | none => simp [hmap] at ht
          | some f =>
            cases hw : wasiHost md mem none σ id m.store ((m.stack.take k).reverse) with
            | none => simp [hmap, hw] at ht
            | some res =>
              obtain ⟨τ, ms, r⟩ := res
              simp only [hmap, hw] at ht
              obtain ⟨msP, hwP, hE⟩ := host_put (rest := rest) hP hi hPi hok hmap hw
              have hmi' : (m.hostResume ms r.out rest k).Inv :=
                ((wasiHost_ok md mem) σ id m.store _ τ ms r hw hi).1
              have hPi' : (P.hostResume msP r.out rest k).Inv :=
                ((wasiHost_ok md mem) σ id P.store _ τ msP r hwP hPi).1
              have ih := run_put n ht hmi' hPi' hv (by rw [ride_bind]; exact hE)
              rw [hPstk] at hwP
              simp only [sysRun, hex, hh, hw, hPh, hPstk, hwP]
              exact ih
        | none =>
          simp only [hh] at ht
          cases hu : (m.uniq true || m.admin) with
          | false => simp [hu] at ht
          | true =>
            simp only [hu, Bool.cond_true] at ht
            cases htF : tstep (ps.filterMap id) m with
            | none => simp only [htF] at ht; simp at ht
            | some F =>
              cases hs : m.step with
              | none => simp only [htF, hs] at ht; simp at ht
              | some m' =>
                simp only [htF, hs] at ht
                obtain ⟨P', hPs', hE⟩ := step_put hP hi hPi hok hb hsup htF hs
                have hm' := (step_sim hi hs).1
                have hP'i := (step_sim hPi hPs').1
                have ih := run_put n ht hm' hP'i hv (by rw [ride_bind]; exact hE)
                obtain ⟨hu1, hu2⟩ := uniq_eqv hP true
                have hPu : (P.uniq true || P.admin) = true := by rw [hu1, hu2]; exact hu
                simp only [sysRun, hex, hh, hPh, hu, hPu, Bool.cond_true, hs, hPs']
                exact ih

/-- `sysRun_put` (contract F1): a `trun` certificate over `n` transitions transfers `SysMust`
under the restricted WASI world from the patched end state back to the patched start state. -/
theorem sysMust_put {md : Module} {mem : Nat}
    {Q : SysOutcome ((world md mem).restrict (E md mem)).St → Prop} {n : Nat} {σ σ' : State}
    {m m' : MState} {b : Bool} {ps qs : List (Option Pos)} {vs : List TVal}
    (ht : trun md mem ps n (σ, m) = some qs) (hi : m.Inv) (hv : ValsOK vs)
    (hok : BytesOK (ride ps vs) m.store.mems)
    (hr : sysRun State.exited (wasiHost md mem none) n (σ, m) = (σ', m', b))
    (hend : SysMust ((world md mem).restrict (E md mem)) true Q (σ', (put (ride qs vs) m').abs)) :
    SysMust ((world md mem).restrict (E md mem)) true Q (σ, (put (ride ps vs) m).abs) := by
  have hPi := put_inv hi hok
  obtain ⟨h1, h2⟩ := run_put n ht hi hPi hv (eqv_refl _)
  rw [hr] at h1 h2
  simp only at h1 h2
  refine machineRun_sysMust (wasiHost_ok md mem) n hPi
    (σ' := σ') (m' := (sysRun State.exited (wasiHost md mem none) n
      (σ, put (ride ps vs) m)).2.1) (b := (sysRun State.exited (wasiHost md mem none) n
      (σ, put (ride ps vs) m)).2.2) ?_ ?_
  · show sysRun State.exited (wasiHost md mem none) n (σ, put (ride ps vs) m) = _
    rw [← h1]
    rfl
  · rw [eqv_abs h2]
    exact hend

end FVA.Wasm.Exec.Machine.Oblivious
