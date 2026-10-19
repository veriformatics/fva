import Std

set_option autoImplicit false

/-!
A total-correctness proof for isqrt.c on the README's wasm32 target.
All specification arithmetic is Nat arithmetic, hence cannot overflow.
The C-level model below uses explicit unsigned modular operations.
-/
namespace Isqrt

abbrev U32 : Nat := 4294967296
abbrev U64 : Nat := 18446744073709551616
abbrev upper : Nat := 65536

structure State where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

/-- Unsigned 32-bit subtraction on represented (in-range) operands. -/
def sub32 (a b : Nat) : Nat := (a + U32 - b) % U32
/-- Unsigned 32-bit addition. -/
def add32 (a b : Nat) : Nat := (a + b) % U32
/-- Widening to unsigned long long (identity for all uint32 values). -/
def cast64 (a : Nat) : Nat := a % U64
/-- Unsigned 64-bit multiplication, after the explicit C cast. -/
def square64 (a : Nat) : Nat := (cast64 a * cast64 a) % U64

/-- C: lo + (hi - lo) / 2. -/
def cMid (s : State) : Nat := add32 s.lo (sub32 s.hi s.lo / 2)
/-- C: hi - lo > 1. -/
def cGuard (s : State) : Prop := sub32 s.hi s.lo > 1
instance (s : State) : Decidable (cGuard s) := Nat.decLt 1 (sub32 s.hi s.lo)
/-- The body, including the 64-bit comparison and the two assignments. -/
def cStep (n : Nat) (s : State) : State :=
  let mid := cMid s
  if square64 mid ≤ cast64 n then ⟨mid, s.hi⟩ else ⟨s.lo, mid⟩

/-- Big-step semantics of the actual while loop; k counts body executions. -/
inductive Executes (n : Nat) : State → Nat → Nat → Prop where
  | done (s : State) (h : ¬ cGuard s) : Executes n s s.lo 0
  | step (s : State) (h : cGuard s) {r k : Nat}
      (tail : Executes n (cStep n s) r k) : Executes n s r (k + 1)

/-- Binary-search invariant. -/
structure Inv (n : Nat) (s : State) : Prop where
  ordered : s.lo < s.hi
  bounded : s.hi ≤ upper
  lower : s.lo * s.lo ≤ n
  upperBound : n < s.hi * s.hi

def initial : State := ⟨0, upper⟩

/-- R1, with maximality over ALL natural numbers, not just uint32 values. -/
def IsRoot (n r : Nat) : Prop :=
  r * r ≤ n ∧ ∀ q : Nat, q * q ≤ n → q ≤ r

theorem initial_inv (n : Nat) (hn : n < U32) : Inv n initial := by
  constructor
  · decide
  · decide
  · exact Nat.zero_le n
  · exact hn

theorem sub32_exact {a b : Nat} (hba : b ≤ a) (ha : a < U32) :
    sub32 a b = a - b := by
  unfold sub32
  have heq : a + U32 - b = (a - b) + U32 := by omega
  rw [heq, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (show a - b < U32 by omega)]

theorem guard_exact {n : Nat} {s : State} (h : Inv n s) :
    cGuard s ↔ 1 < s.hi - s.lo := by
  unfold cGuard
  rw [sub32_exact (Nat.le_of_lt h.ordered)
    (Nat.lt_of_le_of_lt h.bounded (by decide))]

def mid (s : State) : Nat := s.lo + (s.hi - s.lo) / 2

theorem mid_bounds {n : Nat} {s : State} (h : Inv n s)
    (hg : 1 < s.hi - s.lo) : s.lo < mid s ∧ mid s < s.hi := by
  unfold mid
  have := h.ordered
  omega

theorem midpoint_exact {n : Nat} {s : State} (h : Inv n s) :
    cMid s = mid s := by
  unfold cMid add32 mid
  rw [sub32_exact (Nat.le_of_lt h.ordered)
    (Nat.lt_of_le_of_lt h.bounded (by decide))]
  apply Nat.mod_eq_of_lt
  have hm : s.lo + (s.hi - s.lo) / 2 ≤ upper := by
    have := h.ordered
    have := h.bounded
    omega
  exact Nat.lt_of_le_of_lt hm (by decide)

theorem cast64_exact {a : Nat} (ha : a < U64) : cast64 a = a :=
  Nat.mod_eq_of_lt ha

theorem square64_exact {a : Nat} (ha : a ≤ upper) : square64 a = a * a := by
  unfold square64
  rw [cast64_exact (Nat.lt_of_le_of_lt ha (by decide))]
  apply Nat.mod_eq_of_lt
  have hm := Nat.mul_self_le_mul_self ha
  have hc : upper * upper < U64 := by decide
  exact Nat.lt_of_le_of_lt hm hc

theorem step_exact {n : Nat} {s : State} (hn : n < U32) (h : Inv n s) :
    cStep n s =
      if mid s * mid s ≤ n then ⟨mid s, s.hi⟩ else ⟨s.lo, mid s⟩ := by
  have hm : mid s ≤ upper := by
    unfold mid
    have := h.ordered
    have := h.bounded
    omega
  simp only [cStep, midpoint_exact h, square64_exact hm,
    cast64_exact (Nat.lt_trans hn (by decide))]

theorem step_inv {n : Nat} {s : State} (hn : n < U32) (h : Inv n s)
    (hg : cGuard s) : Inv n (cStep n s) := by
  have hb := mid_bounds h ((guard_exact h).mp hg)
  rw [step_exact hn h]
  split
  next ht =>
    exact ⟨hb.2, h.bounded, ht, h.upperBound⟩
  next ht =>
    exact ⟨hb.1, Nat.le_trans (Nat.le_of_lt hb.2) h.bounded,
      h.lower, Nat.lt_of_not_ge ht⟩

theorem step_decreases {n : Nat} {s : State} (hn : n < U32) (h : Inv n s)
    (hg : cGuard s) :
    (cStep n s).hi - (cStep n s).lo < s.hi - s.lo := by
  have hb := mid_bounds h ((guard_exact h).mp hg)
  rw [step_exact hn h]
  split <;> simp only <;> omega

theorem exit_correct {n : Nat} {s : State} (h : Inv n s)
    (hg : ¬ cGuard s) : IsRoot n s.lo := by
  have hgap : s.hi = s.lo + 1 := by
    have := h.ordered
    have : ¬ (1 < s.hi - s.lo) := fun hp => hg ((guard_exact h).mpr hp)
    omega
  constructor
  · exact h.lower
  · intro q hq
    have hlt : q < s.hi := by
      apply Nat.lt_of_not_ge
      intro hge
      have hm := Nat.mul_self_le_mul_self hge
      have := h.upperBound
      omega
    omega

/-- R2 and R1 together: finite execution exists and returns the specified root. -/
theorem total_correct (n : Nat) (hn : n < U32) (s : State) (h : Inv n s) :
    ∃ r k, Executes n s r k ∧ IsRoot n r := by
  by_cases hg : cGuard s
  · obtain ⟨r, k, he, hr⟩ := total_correct n hn (cStep n s) (step_inv hn h hg)
    exact ⟨r, k + 1, Executes.step s hg he, hr⟩
  · exact ⟨s.lo, 0, Executes.done s hg, exit_correct h hg⟩
termination_by s.hi - s.lo
decreasing_by exact step_decreases hn h hg

/-- The README requirements, for every one of the 2^32 possible inputs. -/
theorem requirements (n : Nat) (hn : n < U32) :
    ∃ r k, Executes n initial r k ∧ IsRoot n r :=
  total_correct n hn initial (initial_inv n hn)

/-- Partial correctness for every execution, not only the witness of total_correct. -/
theorem execution_correct {n : Nat} (hn : n < U32) {s : State} {r k : Nat}
    (h : Inv n s) (he : Executes n s r k) : IsRoot n r := by
  induction he with
  | done s hg => exact exit_correct h hg
  | step s hg tail ih => exact ih (step_inv hn h hg)

/-- Each iteration cuts the interval size to at most its rounded-up half. -/
theorem step_halves {n : Nat} {s : State} (hn : n < U32) (h : Inv n s) :
    2 * ((cStep n s).hi - (cStep n s).lo) ≤ s.hi - s.lo + 1 := by
  have := h.ordered
  rw [step_exact hn h]
  split <;> dsimp [mid] <;> omega

theorem execution_bound (fuel : Nat) {n : Nat} (hn : n < U32)
    {s : State} {r k : Nat} (h : Inv n s) (he : Executes n s r k)
    (hspan : s.hi - s.lo ≤ 2 ^ fuel) : k ≤ fuel := by
  induction fuel generalizing s r k with
  | zero =>
    cases he with
    | done => exact Nat.le_refl 0
    | step s hg tail =>
      have := (guard_exact h).mp hg
      simp only [Nat.pow_zero] at hspan
      omega
  | succ fuel ih =>
    cases he with
    | done => exact Nat.zero_le _
    | step s hg tail =>
      have hh := step_halves hn h
      rw [Nat.pow_succ] at hspan
      have hb : (cStep n s).hi - (cStep n s).lo ≤ 2 ^ fuel := by omega
      have hk := ih (step_inv hn h hg) tail hb
      omega

theorem at_most_16 {n r k : Nat} (hn : n < U32) (he : Executes n initial r k) :
    k ≤ 16 :=
  execution_bound 16 hn (initial_inv n hn) he (by decide)

/-- All loop headers reachable from the C initialization. -/
inductive Reaches (n : Nat) : State → Prop where
  | start : Reaches n initial
  | step {s : State} (prior : Reaches n s) (hg : cGuard s) :
      Reaches n (cStep n s)

theorem reachable_inv {n : Nat} (hn : n < U32) {s : State} (hr : Reaches n s) :
    Inv n s := by
  induction hr with
  | start => exact initial_inv n hn
  | step _ hg ih => exact step_inv hn ih hg

/-- No underflow in subtraction, no overflow in addition, widening, or multiplication.
    Division is always by the nonzero literal 2. Bounds hold even at an exit header. -/
theorem arithmetic_safe {n : Nat} {s : State} (hn : n < U32) (h : Inv n s) :
    s.lo ≤ s.hi ∧ s.hi < U32 ∧ s.hi - s.lo < U32 ∧
    mid s < U32 ∧ mid s * mid s < U64 ∧ n < U64 := by
  have hi32 : s.hi < U32 := Nat.lt_of_le_of_lt h.bounded (by decide)
  have hm : mid s ≤ upper := by
    unfold mid
    have := h.ordered
    have := h.bounded
    omega
  have hm32 : mid s < U32 := Nat.lt_of_le_of_lt hm (by decide)
  have hprod : mid s * mid s < U64 :=
    Nat.lt_of_le_of_lt (Nat.mul_self_le_mul_self hm) (by decide)
  exact ⟨Nat.le_of_lt h.ordered, hi32, by omega, hm32, hprod,
    Nat.lt_trans hn (by decide)⟩

theorem reachable_arithmetic_safe {n : Nat} (hn : n < U32) {s : State}
    (hr : Reaches n s) :
    s.lo ≤ s.hi ∧ s.hi < U32 ∧ s.hi - s.lo < U32 ∧
    mid s < U32 ∧ mid s * mid s < U64 ∧ n < U64 :=
  arithmetic_safe hn (reachable_inv hn hr)

end Isqrt
