import Isqrt

set_option autoImplicit false

/-! Fixed-width, expression-for-expression model of isqrt.c. -/
namespace Isqrt.Machine

structure State where
  lo : UInt32
  hi : UInt32
  deriving DecidableEq, Repr

def initial : State := ⟨0, 65536⟩
def decode (s : State) : Isqrt.State := ⟨s.lo.toNat, s.hi.toNat⟩

def guard (s : State) : Prop := s.hi - s.lo > 1
instance (s : State) : Decidable (guard s) := UInt32.decLt 1 (s.hi - s.lo)

def mid (s : State) : UInt32 := s.lo + (s.hi - s.lo) / 2

def step (n : UInt32) (s : State) : State :=
  let m := mid s
  if m.toUInt64 * m.toUInt64 ≤ n.toUInt64 then ⟨m, s.hi⟩ else ⟨s.lo, m⟩

inductive Executes (n : UInt32) : State → UInt32 → Nat → Prop where
  | done (s : State) (h : ¬ guard s) : Executes n s s.lo 0
  | step (s : State) (h : guard s) {r : UInt32} {k : Nat}
      (tail : Executes n (step n s) r k) : Executes n s r (k + 1)

theorem sub_refines (a b : UInt32) :
    (a - b).toNat = sub32 a.toNat b.toNat := by
  rw [UInt32.toNat_sub]
  unfold sub32
  change (U32 - b.toNat + a.toNat) % U32 = (a.toNat + U32 - b.toNat) % U32
  congr 1
  have hb : b.toNat < U32 := b.toNat_lt
  omega

theorem mid_refines (s : State) : (mid s).toNat = cMid (decode s) := by
  unfold mid cMid add32 decode
  rw [UInt32.toNat_add, UInt32.toNat_div, sub_refines]
  rfl

theorem guard_refines (s : State) : guard s ↔ cGuard (decode s) := by
  change ((1 : UInt32) < s.hi - s.lo) ↔ (1 < sub32 s.hi.toNat s.lo.toNat)
  rw [UInt32.lt_iff_toNat_lt, sub_refines]
  rfl

theorem widen_refines (n : UInt32) : n.toUInt64.toNat = cast64 n.toNat := by
  rw [UInt32.toNat_toUInt64, cast64_exact (Nat.lt_trans n.toNat_lt (by decide))]

theorem square_refines (m : UInt32) :
    (m.toUInt64 * m.toUInt64).toNat = square64 m.toNat := by
  rw [UInt64.toNat_mul, widen_refines]
  rfl

/-- A simulation theorem for the body, valid even outside the loop invariant. -/
theorem step_refines (n : UInt32) (s : State) :
    decode (step n s) = cStep n.toNat (decode s) := by
  unfold step cStep
  simp only [UInt64.le_iff_toNat_le, square_refines, widen_refines, mid_refines]
  split <;> simp only [decode, mid_refines]

/-- Reachability includes every loop header, including the final one. -/
inductive Reaches (n : UInt32) : State → Prop where
  | start : Reaches n initial
  | step {s : State} (prior : Reaches n s) (hg : guard s) : Reaches n (step n s)

theorem reachable_refines {n : UInt32} {s : State} (hr : Reaches n s) :
    Isqrt.Reaches n.toNat (decode s) := by
  induction hr with
  | start => exact Isqrt.Reaches.start
  | step _ hg ih =>
    rw [step_refines]
    exact Isqrt.Reaches.step ih ((guard_refines _).mp hg)

/-- All source arithmetic is in range at every reachable fixed-width state.
    Isqrt.mid denotes the UNBOUNDED addition and division, before any wrapping. -/
theorem no_overflow {n : UInt32} {s : State} (hr : Reaches n s) :
    s.lo.toNat ≤ s.hi.toNat ∧ s.hi.toNat < U32 ∧
    s.hi.toNat - s.lo.toNat < U32 ∧ Isqrt.mid (decode s) < U32 ∧
    Isqrt.mid (decode s) * Isqrt.mid (decode s) < U64 ∧ n.toNat < U64 :=
  reachable_arithmetic_safe n.toNat_lt (reachable_refines hr)

/-- Every finite fixed-width execution has exactly the modeled arithmetic behavior. -/
theorem execution_refines {n : UInt32} {s : State} {r : UInt32} {k : Nat}
    (he : Executes n s r k) : Isqrt.Executes n.toNat (decode s) r.toNat k := by
  induction he with
  | done s hg =>
    exact Isqrt.Executes.done (decode s) (fun h => hg ((guard_refines s).mpr h))
  | step s hg tail ih =>
    apply Isqrt.Executes.step (decode s) ((guard_refines s).mp hg)
    rw [← step_refines]
    exact ih

/-- Total correctness of the fixed-width C model, with no assumed fuel limit. -/
theorem total_correct (n : UInt32) (s : State) (h : Inv n.toNat (decode s)) :
    ∃ r k, Executes n s r k ∧ IsRoot n.toNat r.toNat := by
  have hn : n.toNat < U32 := n.toNat_lt
  by_cases hg : guard s
  · have hi : Inv n.toNat (decode (step n s)) := by
      rw [step_refines]
      exact step_inv hn h ((guard_refines s).mp hg)
    obtain ⟨r, k, he, hr⟩ := total_correct n (step n s) hi
    exact ⟨r, k + 1, Executes.step s hg he, hr⟩
  · exact ⟨s.lo, 0, Executes.done s hg,
      exit_correct h (fun hp => hg ((guard_refines s).mpr hp))⟩
termination_by s.hi.toNat - s.lo.toNat
decreasing_by
  change (decode (step n s)).hi - (decode (step n s)).lo <
    (decode s).hi - (decode s).lo
  rw [step_refines]
  exact step_decreases hn h ((guard_refines s).mp hg)

/-- No nondeterministic choice of result or iteration count is hidden in Executes. -/
theorem deterministic {n : UInt32} {s : State} {r₁ r₂ : UInt32} {k₁ k₂ : Nat}
    (h₁ : Executes n s r₁ k₁) (h₂ : Executes n s r₂ k₂) : r₁ = r₂ ∧ k₁ = k₂ := by
  induction h₁ generalizing r₂ k₂ with
  | done s hg =>
    cases h₂ with
    | done => exact ⟨rfl, rfl⟩
    | step _ hg' => exact False.elim (hg hg')
  | step s hg tail ih =>
    cases h₂ with
    | done _ hg' => exact False.elim (hg' hg)
    | step _ _ tail' =>
      obtain ⟨hr, hk⟩ := ih tail'
      exact ⟨hr, congrArg (· + 1) hk⟩

/-- R1 and R2 for every input of the actual fixed-width type. -/
theorem requirements (n : UInt32) :
    ∃ r k, Executes n initial r k ∧ IsRoot n.toNat r.toNat :=
  total_correct n initial (initial_inv n.toNat n.toNat_lt)

/-- Every possible execution returns the largest root, in at most 16 iterations. -/
theorem every_execution_correct {n : UInt32} {r : UInt32} {k : Nat}
    (he : Executes n initial r k) : IsRoot n.toNat r.toNat ∧ k ≤ 16 := by
  have he' := execution_refines he
  exact ⟨execution_correct n.toNat_lt (initial_inv n.toNat n.toNat_lt) he',
    at_most_16 n.toNat_lt he'⟩

/-- Consolidated statement of R1, R2, the iteration bound, and uniqueness. -/
theorem verified (n : UInt32) :
    ∃ r k, Executes n initial r k ∧ IsRoot n.toNat r.toNat ∧ k ≤ 16 ∧
      ∀ r' k', Executes n initial r' k' → r' = r ∧ k' = k := by
  obtain ⟨r, k, he, hr⟩ := requirements n
  exact ⟨r, k, he, hr, (every_execution_correct he).2,
    fun _ _ he' => deterministic he' he⟩

end Isqrt.Machine
