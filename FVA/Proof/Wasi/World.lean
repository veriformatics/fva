import FVA.Spec.Wasi.World
import FVA.Proof.Valid.Updates

/-!
# WASI world: typing, `E ⊆ W`, determinism + progress under `E` (U29a T2, T3, T4, T8)

T4's equation form is U29b's seam: the executable host computes `exec … {}` and `HostOK` needs
that outcome to be the restricted world's only one (`FVA/Proof/Exec/MachineSys.lean`).
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec

/-- The `none` choice is always admissible. -/
theorem choiceOK_none (σ : State) (r : Req) (b : Bytes) : ChoiceOK σ r { bytes := b } := by
  simp [ChoiceOK]

/-- `decode` keeps the call. -/
@[simp] theorem decode_call (c : Call) (m : MemInst) (a : List Nat) : (decode c m a).call = c :=
  rfl

/-- Only `random_get` reads the random bytes. -/
theorem run_bytes (σ : State) (r : Req) (b : Bytes) (h : r.call ≠ .randomGet) :
    run σ r { bytes := b } = run σ r {} := by
  rcases r with ⟨c, a, iovs, data, path⟩
  cases c <;> first | rfl | exact absurd rfl h

theorem step_bytes (σ : State) (r : Req) (b : Bytes) (h : r.call ≠ .randomGet) :
    step σ r { bytes := b } = step σ r {} := by
  unfold step; rw [run_bytes σ r b h]

theorem exec_bytes (σ : State) {c : Call} (s : Store) (mem : Nat) (vs : List Val) (b : Bytes)
    (h : c ≠ .randomGet) : exec σ c s mem vs { bytes := b } = exec σ c s mem vs {} := by
  unfold exec
  split
  · rw [step_bytes _ _ b (by simpa using h)]
  · rfl

/-- `writeBytes` keeps a memory's size and maximum. -/
theorem writes_extends (m : MemInst) (ws : List (Nat × Bytes)) :
    m.Extends (ws.foldl (fun m w => writeBytes m w.1 w.2) m) := by
  induction ws generalizing m with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons w ws ih =>
    have := ih (writeBytes m w.1 w.2)
    exact ⟨this.1, this.2⟩

/-- `step` answers `exit` exactly for `proc_exit`. -/
theorem step_exit_iff (σ : State) (r : Req) (ch : Choice) :
    (∃ k, (step σ r ch).2 = .exit k) ↔ r.call = .procExit := by
  unfold step
  by_cases h : r.call = .procExit
  · simp [h]
  · simp only [h, ↓reduceIte]
    split
    · simp
    · split <;> simp

/-- W's injected failure (`err = some e`, every call but `proc_exit`) returns its errno with the
world + store unchanged (or the argument-decoding trap). -/
theorem exec_err {σ : State} {c : Call} {s : Store} {mem : Nat} {vs : List Val} {ch : Choice}
    {e : Nat} (h : ch.err = some e) (hc : c ≠ .procExit) :
    exec σ c s mem vs ch = (σ, .returned s [.i32 (BitVec.ofNat 32 e)]) ∨
      exec σ c s mem vs ch = (σ, .trapped s) := by
  unfold exec
  split
  · simp [step, hc, h]
  · simp

/-- T2: every outcome of `exec` is allowed for the call's result types. -/
theorem exec_allowed (σ : State) (c : Call) (s : Store) (mem : Nat) (vs : List Val)
    (ch : Choice) : (exec σ c s mem vs ch).2.Allowed s c.sig.results := by
  unfold exec
  split
  · rename_i m a hm _
    have hx := step_exit_iff σ (decode c m a) ch
    split
    · rename_i τ ws hs
      have hc : c ≠ .procExit := fun h => by
        have := (hx.mpr (by simpa using h)); rw [hs] at this; simp at this
      refine ⟨⟨(Store.Extends.refl s).1, (Store.Extends.refl s).2.1,
        Valid.listExtends_set (fun x => ⟨rfl, Nat.le_refl _⟩) hm (writes_extends m ws),
        (Store.Extends.refl s).2.2.2⟩, ?_⟩
      simp [Call.sig, hc, Val.HasType]
    · rename_i τ e hs
      have hc : c ≠ .procExit := fun h => by
        have := (hx.mpr (by simpa using h)); rw [hs] at this; simp at this
      exact ⟨Store.Extends.refl s, by simp [Call.sig, hc, Val.HasType]⟩
    · exact Store.Extends.refl s
  · exact Store.Extends.refl s

/-- T3 (totality): every call the world allows an outcome for keeps one under `E`. -/
theorem env_total (m : Module) (mem : Nat) : Env.Total (world m mem) (E m mem) := by
  intro σ id s vs ⟨τ, o, h⟩
  show ∃ τ o, (world m mem).host σ τ id s vs o ∧ E m mem σ τ id s vs o
  cases hb : bind m id with
  | none => exact ⟨τ, o, h, by simp [E, hb]⟩
  | some c =>
    simp only [world, E, hb]
    by_cases hp : inProfile σ c s mem vs = true
    · exact ⟨(exec σ c s mem vs {}).1, (exec σ c s mem vs {}).2,
        Or.inr (Or.inl ⟨hp, {}, choiceOK_none _ _ [], rfl⟩), fun _ => ⟨[], rfl⟩⟩
    · exact ⟨σ, .trapped s, Or.inr (Or.inr ⟨by simpa using hp, rfl, by simp,
        Store.Extends.refl s⟩), fun h => absurd h hp⟩

/-- T4: under `E`, a bound in-profile call other than `random_get` has exactly the outcome
`exec … {}`. -/
theorem restrict_host_iff {m : Module} {mem id : Nat} {c : Call} (hb : bind m id = some c)
    (hc : c ≠ .randomGet) {σ τ : State} {s : Store} {vs : List Val} {o : HostOutcome}
    (hp : inProfile σ c s mem vs = true) :
    ((world m mem).restrict (E m mem)).host σ τ id s vs o ↔ (τ, o) = exec σ c s mem vs {} := by
  show (world m mem).host σ τ id s vs o ∧ E m mem σ τ id s vs o ↔ _
  simp only [world, E, hb]
  constructor
  · rintro ⟨-, he⟩
    obtain ⟨b, h⟩ := he hp
    rw [h, exec_bytes σ s mem vs b hc]
  · intro h
    exact ⟨Or.inr (Or.inl ⟨hp, {}, choiceOK_none _ _ [], h⟩), fun _ => ⟨[], h⟩⟩

/-- T4 for `random_get`: the outcomes under `E` are those of every byte string. -/
theorem restrict_host_random {m : Module} {mem id : Nat} (hb : bind m id = some .randomGet)
    {σ τ : State} {s : Store} {vs : List Val} {o : HostOutcome}
    (hp : inProfile σ .randomGet s mem vs = true) :
    ((world m mem).restrict (E m mem)).host σ τ id s vs o ↔
      ∃ b, (τ, o) = exec σ .randomGet s mem vs { bytes := b } := by
  show (world m mem).host σ τ id s vs o ∧ E m mem σ τ id s vs o ↔ _
  simp only [world, E, hb]
  constructor
  · rintro ⟨-, he⟩
    exact he hp
  · rintro ⟨b, h⟩
    exact ⟨Or.inr (Or.inl ⟨hp, { bytes := b }, choiceOK_none _ _ b, h⟩), fun _ => ⟨b, h⟩⟩

/-- T8: under `E`, no bound in-profile call diverges. -/
theorem restrict_no_diverge {m : Module} {mem id : Nat} {c : Call} (hb : bind m id = some c)
    {σ τ : State} {s : Store} {vs : List Val} (hp : inProfile σ c s mem vs = true) :
    ¬ ((world m mem).restrict (E m mem)).host σ τ id s vs .diverged := by
  rintro ⟨-, he⟩
  simp only [E, hb] at he
  obtain ⟨b, h⟩ := he hp
  exact exec_ne_diverged σ c s mem vs { bytes := b } (congrArg Prod.snd h).symm

/-- Outside the profile `E` keeps divergence: no total-correctness claim passes such a call
(`host_diverged_not_must`). -/
theorem restrict_diverges_outside {m : Module} {mem id : Nat} {c : Call}
    (hb : bind m id = some c) {σ : State} {s : Store} {vs : List Val}
    (hp : inProfile σ c s mem vs = false) :
    ((world m mem).restrict (E m mem)).host σ σ id s vs .diverged := by
  show (world m mem).host σ σ id s vs .diverged ∧ E m mem σ σ id s vs .diverged
  simp only [world, E, hb, hp]
  simp

end FVA.Wasi
