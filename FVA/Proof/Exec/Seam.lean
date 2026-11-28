import FVA.Proof.Exec.ObliviousRun

/-!
# Seams between certified segments (contract U28g F2)

A seam = the few transitions where an input value leaves the positions `trun` follows (read onto
the operand stack, computed on, stored back). Its transitions run symbolically: the twin's state
at the seam start is exposed as a skeleton (a structure literal over opaque parts, one kernel
fact), and these equations step it for every input value.
-/

namespace FVA.Wasm.Exec.Machine.Oblivious

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

section Run

variable {St : Type} {exited : St → Option Nat}
  {X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)}

/-- One `sysRun` transition: `none` where `sysRun` stops. -/
def sysNext (exited : St → Option Nat)
    (X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)) :
    St × MState → Option (St × MState)
  | (σ, m) => match exited σ with
    | some _ => none
    | none => match m.hostCall with
      | some (id, k, rest) => match X σ id m.store (m.stack.take k).reverse with
        | some (τ, ms, r) => some (τ, m.hostResume ms r.out rest k)
        | none => none
      | none => bif m.uniq true || m.admin then m.step.map (σ, ·) else none

theorem sysRun_succ (n : Nat) (s : St × MState) :
    sysRun exited X (n + 1) s = match sysNext exited X s with
      | some s' => sysRun exited X n s'
      | none => (s.1, s.2, false) := by
  obtain ⟨σ, m⟩ := s
  simp only [sysRun, sysNext]
  cases exited σ with
  | some _ => rfl
  | none =>
    simp only
    cases hh : m.hostCall with
    | some p =>
      obtain ⟨id, k, rest⟩ := p
      simp only
      cases X σ id m.store (m.stack.take k).reverse with
      | some r => obtain ⟨τ, ms, r⟩ := r; rfl
      | none => rfl
    | none =>
      simp only
      cases m.uniq true || m.admin
      · rfl
      · simp only [Bool.cond_true]
        cases m.step <;> rfl

/-- Runs compose: a run that spends all its fuel continues as the longer run. -/
theorem sysRun_add : ∀ (a b : Nat) {s : St × MState} {σ : St} {m : MState},
    sysRun exited X a s = (σ, m, true) → sysRun exited X (a + b) s = sysRun exited X b (σ, m)
  | 0, b, s, σ, m, h => by
    obtain ⟨σ₀, m₀⟩ := s
    simp only [sysRun, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    simp
  | a + 1, b, s, σ, m, h => by
    rw [sysRun_succ] at h
    rw [show a + 1 + b = (a + b) + 1 by omega, sysRun_succ]
    cases hn : sysNext exited X s with
    | none => simp [hn] at h
    | some s' =>
      simp only [hn] at h ⊢
      exact sysRun_add a b h

end Run

theorem sysNext_inv {W : World}
    {X : W.St → Nat → MStore → List Val → Option (W.St × MStore × MHostOut)} (hX : HostOK W X)
    {s s' : W.St × MState} (hi : s.2.Inv) (h : sysNext W.exited X s = some s') : s'.2.Inv := by
  obtain ⟨σ, m⟩ := s
  simp only [sysNext] at h
  cases he : W.exited σ with
  | some _ => simp [he] at h
  | none =>
    simp only [he] at h
    cases hh : m.hostCall with
    | some p =>
      obtain ⟨id, k, rest⟩ := p
      simp only [hh] at h
      cases hx : X σ id m.store (m.stack.take k).reverse with
      | none => simp [hx] at h
      | some r =>
        obtain ⟨τ, ms, r⟩ := r
        simp only [hx, Option.some.injEq] at h
        subst h
        exact (hX σ id m.store _ τ ms r hx hi).1
    | none =>
      simp only [hh] at h
      cases hb : (m.uniq true || m.admin) <;> simp only [hb, Bool.cond_false, Bool.cond_true] at h
      · cases h
      · cases hs : m.step with
        | none => simp [hs] at h
        | some m₁ =>
          simp only [hs, Option.map_some, Option.some.injEq] at h
          subst h
          exact (step_sim hi hs).1

/-- A run with a host whose results keep the invariant keeps it. -/
theorem sysRun_inv {W : World}
    {X : W.St → Nat → MStore → List Val → Option (W.St × MStore × MHostOut)} (hX : HostOK W X) :
    ∀ (n : Nat) {s : W.St × MState} {σ' : W.St} {m' : MState} {b : Bool}, s.2.Inv →
      sysRun W.exited X n s = (σ', m', b) → m'.Inv
  | 0, s, σ', m', b, hi, h => by
    obtain ⟨σ, m⟩ := s
    simp only [sysRun, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact hi
  | n + 1, s, σ', m', b, hi, h => by
    rw [sysRun_succ] at h
    cases hn : sysNext W.exited X s with
    | none =>
      simp only [hn, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact hi
    | some s' =>
      simp only [hn] at h
      exact sysRun_inv hX n (sysNext_inv hX hi hn) h

/-! ## Memory patches over a 4-byte cell -/

section Mem

open MMem

theorem byte_writeByte {m : MMem} (hw : m.WF) {d b : Nat} (hd : d < 2 ^ (m.depth + W))
    (hb : b < 256) (a : Nat) : (m.writeBytes d [b]).byte a = if a = d then b else m.byte a := by
  rw [byte_writeBytes hw (by simpa using hd) (by simpa using hb)]
  by_cases h : a = d
  · subst h; simp
  · have h' : ¬ (d ≤ a ∧ a < d + [b].length) := by simp only [List.length_singleton]; omega
    simp only [h, h', ↓reduceIte]

/-- Bytes `b₀…b₃` patched one by one at `ea…ea+3` (`put`'s byte patches, in order). -/
def patch4 (m : MMem) (ea b₀ b₁ b₂ b₃ : Nat) : MMem :=
  ((((m.writeBytes ea [b₀]).writeBytes (ea + 1) [b₁]).writeBytes (ea + 2) [b₂]).writeBytes
    (ea + 3) [b₃])

theorem patch4_fields (m : MMem) (ea b₀ b₁ b₂ b₃ : Nat) :
    (patch4 m ea b₀ b₁ b₂ b₃).pages = m.pages ∧ (patch4 m ea b₀ b₁ b₂ b₃).max = m.max ∧
      (patch4 m ea b₀ b₁ b₂ b₃).depth = m.depth := by
  simp only [patch4, writeBytes_fields, and_self]

theorem byte_patch4 {m : MMem} (hw : m.WF) {ea : Nat} (hk : ea + 4 ≤ 2 ^ (m.depth + W))
    {b₀ b₁ b₂ b₃ : Nat} (h₀ : b₀ < 256) (h₁ : b₁ < 256) (h₂ : b₂ < 256) (h₃ : b₃ < 256) (a : Nat) :
    (patch4 m ea b₀ b₁ b₂ b₃).byte a =
      if a = ea then b₀ else if a = ea + 1 then b₁ else if a = ea + 2 then b₂
      else if a = ea + 3 then b₃ else m.byte a := by
  have w₁ := writeBytes_wf hw ea [b₀]
  have w₂ := writeBytes_wf w₁ (ea + 1) [b₁]
  have w₃ := writeBytes_wf w₂ (ea + 2) [b₂]
  have d₁ := (writeBytes_fields m ea [b₀]).2.2
  have d₂ := (writeBytes_fields (m.writeBytes ea [b₀]) (ea + 1) [b₁]).2.2
  have d₃ := (writeBytes_fields ((m.writeBytes ea [b₀]).writeBytes (ea + 1) [b₁]) (ea + 2) [b₂]).2.2
  simp only [patch4]
  rw [byte_writeByte w₃ (by rw [d₃, d₂, d₁]; omega) h₃,
    byte_writeByte w₂ (by rw [d₂, d₁]; omega) h₂, byte_writeByte w₁ (by rw [d₁]; omega) h₁,
    byte_writeByte hw (by omega) h₀]
  by_cases e₀ : a = ea
  · subst e₀; simp
  · by_cases e₁ : a = ea + 1
    · subst e₁; simp
    · by_cases e₂ : a = ea + 2
      · subst e₂; simp
      · simp [e₀, e₁, e₂]

/-- The little-endian bytes of a 32-bit value. -/
theorem bytes32 (v : Nat) (hv : v < 2 ^ 32) :
    v % 256 + 256 * (v / 256 % 256 + 256 * (v / 65536 % 256 + 256 * (v / 16777216 % 256))) = v := by
  omega

/-- Patching the bytes of `v` over a cell holding `w` = writing `v`. -/
theorem memEqv_patch4 {m : MMem} (hi : m.Inv) {ea : Nat} (hk : ea + 4 ≤ m.size) (v w : Nat) :
    MemEqv (m.write ea 4 v)
      (patch4 (m.write ea 4 w) ea (v % 256) (v / 256 % 256) (v / 65536 % 256)
        (v / 16777216 % 256)) := by
  obtain ⟨hw, hc, -, -⟩ := hi
  have hk' : ea + 4 ≤ 2 ^ (m.depth + W) := by simp only [Cover, size] at hc hk; omega
  obtain ⟨pv, mv, dv⟩ := write_fields m ea 4 v
  obtain ⟨pw, mw, dw⟩ := write_fields m ea 4 w
  obtain ⟨pp, mp, dp⟩ := patch4_fields (m.write ea 4 w) ea (v % 256) (v / 256 % 256)
    (v / 65536 % 256) (v / 16777216 % 256)
  refine ⟨by rw [pv, pp, pw], by rw [mv, mp, mw], by rw [dv, dp, dw], fun a => ?_⟩
  rw [byte_patch4 (write_wf hw ea 4 w) (by rw [dw]; exact hk') (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    byte_write hw hk' v a, byte_write hw hk' w a]
  by_cases e₀ : a = ea
  · subst e₀; simp
  · by_cases e₁ : a = ea + 1
    · subst e₁; simp
    · by_cases e₂ : a = ea + 2
      · subst e₂; simp
      · by_cases e₃ : a = ea + 3
        · subst e₃; simp
        · have h : ¬ (ea ≤ a ∧ a < ea + 4) := by omega
          simp [e₀, e₁, e₂, e₃, h]

/-- A 4-byte read over patched bytes reads them. -/
theorem read_patch4 {m : MMem} (hw : m.WF) {ea : Nat} (hk : ea + 4 ≤ 2 ^ (m.depth + W))
    {b₀ b₁ b₂ b₃ : Nat} (h₀ : b₀ < 256) (h₁ : b₁ < 256) (h₂ : b₂ < 256) (h₃ : b₃ < 256) :
    (patch4 m ea b₀ b₁ b₂ b₃).read ea 4 = b₀ + 256 * (b₁ + 256 * (b₂ + 256 * b₃)) := by
  simp only [MMem.read, Nat.add_assoc, Nat.reduceAdd, byte_patch4 hw hk h₀ h₁ h₂ h₃]
  simp

end Mem

end FVA.Wasm.Exec.Machine.Oblivious
