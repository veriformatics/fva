import FVA.Impl.Exec.WasiHost
import FVA.Proof.Wasi.World
import FVA.Proof.Exec.MachineSys

/-!
# The executable WASI host answers as `E` does (U29b H2, T1, T2)

H2: the host's trie writes denote `exec`'s store (`writeAll_spec`). T1 (`wasiHost_ok`): without
random bytes, every answer is the restricted world's only outcome (`HostOK`), so
`machineRun_sysMust` turns a machine run into `SysMust` under `E`. T2 (`wasiHost_sound`): with
bytes, every answer is one of its outcomes — soundness alone: `E` lets every `random_get` call
return any bytes (`restrict_host_random`), so a run answered with fixed bytes proves no `E` claim.
`answerHost_sysStep`: a driver's answered call is a step of the process.
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine

/-- H2: bytes stored inside the trie's reach denote the spec's `writeBytes`. -/
theorem abs_writeBytes {mm : MMem} (hw : mm.WF) {dst : Nat} {bs : Bytes}
    (hk : dst + bs.length ≤ 2 ^ (mm.depth + Machine.W)) :
    (mm.writeBytes dst (bs.map UInt8.toNat)).abs = writeBytes mm.abs dst bs := by
  obtain ⟨hp, hm, -⟩ := MMem.writeBytes_fields mm dst (bs.map UInt8.toNat)
  simp only [MMem.abs, writeBytes, hp, hm]
  congr 1
  funext a
  rw [MMem.byte_writeBytes hw (by simpa using hk)
    (fun b hb => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt)]
  simp only [List.length_map]
  split
  · cases h : bs[a - dst]? <;> simp [List.getD_eq_getElem?_getD, h]
  · rfl

/-- H2: `writeAll` inside the memory keeps the invariant and denotes `exec`'s writes. -/
theorem writeAll_spec {mm : MMem} (hi : mm.Inv) {ws : List (Nat × Bytes)}
    (hw : ∀ w ∈ ws, w.1 + w.2.length ≤ mm.size) :
    (writeAll mm ws).Inv ∧
      (writeAll mm ws).abs = ws.foldl (fun m w => writeBytes m w.1 w.2) mm.abs := by
  induction ws generalizing mm with
  | nil => exact ⟨hi, rfl⟩
  | cons w ws ih =>
    have hw₀ := hw w (List.mem_cons_self ..)
    have hb : ∀ b ∈ w.2.map UInt8.toNat, b < 256 := fun b hb => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
      exact x.toNat_lt
    have hi' := MMem.writeBytes_inv hi (by simpa using hw₀) hb
    have hsz : (mm.writeBytes w.1 (w.2.map UInt8.toNat)).size = mm.size := by
      rw [MMem.size, MMem.size, (MMem.writeBytes_fields mm w.1 (w.2.map UInt8.toNat)).1]
    obtain ⟨h₁, h₂⟩ := ih hi' fun w' hw' => by
      rw [hsz]; exact hw w' (List.mem_cons_of_mem _ hw')
    refine ⟨h₁, ?_⟩
    have hc : w.1 + w.2.length ≤ 2 ^ (mm.depth + Machine.W) := le_trans hw₀ hi.2.1
    simp only [List.foldl_cons, ← abs_writeBytes hi.1 hc]
    exact h₂

/-- The machine store with memory `mem` replaced denotes the spec store with it replaced. -/
theorem abs_setMem (ms : MStore) (mem : Nat) (mm : MMem) :
    ({ ms with mems := ms.mems.set mem mm } : MStore).abs = ms.abs.setMem mem mm.abs := by
  simp [MStore.abs, Store.setMem, List.map_set]

/-- An answer of `wasiHost` = `exec` on the abstract store, with the bytes it used. -/
theorem wasiHost_exec {m : Module} {mem : Nat} {rand : Option Bytes} {σ τ : State} {id : Nat}
    {ms ms' : MStore} {vs : List Val} {r : MHostOut} (hi : ms.Inv)
    (h : wasiHost m mem rand σ id ms vs = some (τ, ms', r)) :
    ∃ c b, bind m id = some c ∧ inProfile σ c ms.abs mem vs = true ∧
      callBytes c rand = some b ∧ ms'.Inv ∧
      (τ, r.spec ms') = exec σ c ms.abs mem vs { bytes := b } := by
  unfold wasiHost at h
  cases hb : bind m id with
  | none => simp [hb] at h
  | some c =>
  cases hmm : ms.mems[mem]? with
  | none => simp [hb, hmm] at h
  | some mm =>
  cases ha : c.args vs with
  | none => simp [hb, hmm, ha] at h
  | some a =>
  cases hp : inProfile σ c ms.abs mem vs with
  | false => simp [hb, hmm, ha, hp] at h
  | true =>
  cases hr : callBytes c rand with
  | none => simp [hb, hmm, ha, hp, hr] at h
  | some b =>
  have habs : ms.abs.mems[mem]? = some mm.abs := by simp [MStore.abs, hmm]
  refine ⟨c, b, rfl, hp, hr, ?_⟩
  simp only [hb, hmm, ha, hp, hr, Option.bind_eq_bind, Option.bind_some, guard,
    ite_true] at h
  simp only [exec, habs, ha]
  split at h
  · rename_i τ₀ ws hs
    split at h
    · rename_i hw
      simp only [Option.pure_def, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hw' : ∀ w ∈ ws, w.1 + w.2.length ≤ mm.size := fun w hw₁ =>
        of_decide_eq_true (List.all_eq_true.mp hw w hw₁)
      obtain ⟨hinv, hspec⟩ := writeAll_spec (hi mm (List.mem_of_getElem? hmm)) hw'
      refine ⟨?_, ?_⟩
      · intro mm' hm'
        rcases List.mem_or_eq_of_mem_set hm' with hm' | rfl
        · exact hi mm' hm'
        · exact hinv
      · rw [hs]
        simp only [MHostOut.spec, abs_setMem, hspec]
    · simp at h
  · rename_i τ₀ e hs
    simp only [Option.pure_def] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hi, by rw [hs]; rfl⟩
  · rename_i τ₀ k hs
    simp only [Option.pure_def] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hi, by rw [hs]; rfl⟩

/-- `proc_exit k` on a bound id: the world records exit `k`, the store stays, the call traps. -/
theorem wasiHost_procExit {m : Module} {mem id : Nat} {rand : Option Bytes} {σ : State}
    {ms : MStore} {mm : MMem} {k : BitVec 32} (hb : bind m id = some .procExit)
    (hmm : ms.mems[mem]? = some mm) :
    wasiHost m mem rand σ id ms [.i32 k] =
      some ({ σ with exited := some k.toNat }, ms, .trapped) := by
  simp [wasiHost, hb, hmm, Call.args, Call.info, inProfile, MStore.abs, Call.regions,
    Call.valuesOk, callBytes, step, decode, guard]

/-- T1: without random bytes the host's every answer keeps the invariant and is the restricted
world's only outcome. -/
theorem wasiHost_ok (m : Module) (mem : Nat) :
    HostOK ((world m mem).restrict (E m mem)) (wasiHost m mem none) := by
  intro σ id s vs τ ms r h hi
  obtain ⟨c, b, hb, hp, hrb, hi', heq⟩ := wasiHost_exec hi h
  have hc : c ≠ .randomGet := by rintro rfl; simp [callBytes] at hrb
  have hb0 : b = [] := by simpa [callBytes, hc] using hrb.symm
  subst hb0
  have hiff := fun τ' o => restrict_host_iff (σ := σ) (τ := τ') (o := o) hb hc hp
  refine ⟨hi', (hiff τ _).mpr heq, fun τ' o ho => ?_⟩
  exact Prod.mk.inj (((hiff τ' o).mp ho).trans heq.symm)

/-- T2: with bytes `b` for `random_get`, every answer keeps the invariant and is an outcome the
restricted world allows (soundness only). -/
theorem wasiHost_sound {m : Module} {mem : Nat} {b : Bytes} {σ τ : State} {id : Nat}
    {s ms : MStore} {vs : List Val} {r : MHostOut}
    (h : wasiHost m mem (some b) σ id s vs = some (τ, ms, r)) (hi : s.Inv) :
    ms.Inv ∧ ((world m mem).restrict (E m mem)).host σ τ id s.abs vs (r.spec ms) := by
  obtain ⟨c, b', hb, hp, hrb, hi', heq⟩ := wasiHost_exec hi h
  refine ⟨hi', ?_⟩
  by_cases hc : c = .randomGet
  · subst hc
    exact (restrict_host_random hb hp).mpr ⟨b', heq⟩
  · have hb0 : b' = [] := by simpa [callBytes, hc] using hrb.symm
    subst hb0
    exact (restrict_host_iff hb hc hp).mpr heq

/-- T2 (driver): a host call answered by a sound host is a step of the live process. -/
theorem answerHost_sysStep {W : World} {fits : Bool}
    {X : W.St → Nat → MStore → List Val → Option (W.St × MStore × MHostOut)}
    (hX : ∀ σ id s args τ ms r, X σ id s args = some (τ, ms, r) → s.Inv →
      ms.Inv ∧ W.host σ τ id s.abs args (r.spec ms))
    {σ τ : W.St} {m m' : MState} (hi : m.Inv) (hl : W.exited σ = none)
    (h : answerHost X (σ, m) = some (τ, m')) :
    m'.Inv ∧ SysStep W fits (σ, m.abs) (τ, m'.abs) := by
  unfold answerHost at h
  cases hh : m.hostCall with
  | none => simp [hh] at h
  | some p =>
  obtain ⟨id, k, rest⟩ := p
  cases hx : X σ id m.store (m.stack.take k).reverse with
  | none => simp [hh, hx] at h
  | some q =>
  obtain ⟨τ₀, ms, out⟩ := q
  simp only [hh, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨a, dt, ft, hc, hfn, hft, rfl, hk⟩ := hostCall_some hh
  obtain ⟨hinv, hok⟩ := hX σ id m.store _ _ ms out hx hi
  obtain ⟨K, hq, hcont⟩ := abs_host hc hfn hft hk
  have hfa : m.abs.store.funcs[a]? = some (.host dt id) := hfn
  have hst := Ref.host_step (fits := fits) (stk := []) hq hfa hok
  refine ⟨hinv, sysStep_iff.mpr ⟨hl, .inr ⟨?_, host_no_free hq⟩⟩⟩
  have heq : (⟨Ref.hostStore m.abs.store (out.spec ms), m.abs.frame,
      K.result a (m.stack.take ft.params.length).reverse (out.spec ms)⟩ : Config) =
      (m.hostResume ms out.out rest ft.params.length).abs := by
    rw [hcont]
    cases out <;> rfl
  rw [← heq]
  simpa using hst

end FVA.Wasi
