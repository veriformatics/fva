import FVA.Proof.Numerics.Round

/-!
# Executable float operations: classification, decomposition, NaN choice, rounding

Facts every operator proof uses: the `Bool` tests decide the spec's predicates, a number's value
is `±sig·2^ex` (and `units` on any finer grid), `nanOf` picks an element of `nans`, and
`roundDyadic` returns the spec's rounding of its exact input.
-/

namespace FVA.Wasm.Num

open FVal Impl

variable {F : FloatFormat}

@[simp] theorem isNaN_iff {z : FVal} : isNaN z = true ↔ z.IsNaN := by
  cases z <;> simp [isNaN, IsNaN]

@[simp] theorem isInf_iff {z : FVal} : isInf z = true ↔ z.IsInf := by
  cases z <;> simp [isInf, IsInf]

@[simp] theorem isZero_iff {z : FVal} : isZero z = true ↔ z.IsZero := by
  cases z with
  | subnormal s m => cases m <;> simp [isZero, IsZero]
  | _ => simp [isZero, IsZero]

theorem toReal_eq_sig (z : FVal) (hz : z.IsNum) :
    z.toReal F = (if z.neg then -1 else 1) * ((sig F z : ℝ) * 2 ^ ex F z) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  cases z with
  | normal s m e =>
    simp only [toReal, FVal.neg, sig, ex]
    rw [zpow_sub₀ h2, zpow_neg, zpow_natCast]
    push_cast
    field_simp
    cases s <;> simp
  | subnormal s m =>
    simp only [toReal, FVal.neg, sig, ex]
    rw [zpow_sub₀ h2, zpow_neg, zpow_natCast]
    field_simp
    cases s <;> simp
  | inf _ | nan _ _ => simp [IsNum] at hz

theorem toReal_eq_units (z : FVal) (hz : z.IsNum) {e : ℤ} (he : e ≤ ex F z) :
    z.toReal F = (units F z e : ℝ) * 2 ^ e := by
  have h2 : (2 : ℝ) ^ ex F z = ((2 ^ (ex F z - e).toNat : ℕ) : ℝ) * 2 ^ e := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      ← zpow_add₀ two_ne_zero]
    ring_nf
  rw [toReal_eq_sig z hz, h2]
  unfold units
  cases z.neg <;> simp <;> ring

theorem sig_pos {z : FVal} (hz : z.IsNum) (h0 : ¬ z.IsZero) : 0 < sig F z := by
  cases z with
  | normal s m e => simp only [sig]; positivity
  | subnormal s m => cases m <;> simp_all [sig, IsZero]
  | inf _ | nan _ _ => simp [IsNum] at hz

theorem nanOf_cons {z : FVal} {zs : List FVal} (h : ¬ z.IsNaN) :
    nanOf F (z :: zs) = nanOf F zs := by
  cases z <;> first | rfl | simp [IsNaN] at h

theorem nans_cons {z : FVal} {zs : List FVal} (h : ¬ z.IsNaN) : nans F (z :: zs) = nans F zs := by
  unfold nans
  have : (∀ y ∈ z :: zs, ∀ s n, y = nan s n → n = F.canon) ↔
      (∀ y ∈ zs, ∀ s n, y = nan s n → n = F.canon) := by
    constructor
    · intro hall y hy; exact hall y (List.mem_cons_of_mem _ hy)
    · intro hall y hy s n hyn
      rcases List.mem_cons.1 hy with rfl | hy
      · subst hyn; simp [IsNaN] at h
      · exact hall y hy s n hyn
  by_cases hc : ∀ y ∈ zs, ∀ s n, y = nan s n → n = F.canon
  · simp only [eq_true (this.2 hc), eq_true hc, ↓reduceIte]
  · simp only [eq_false (mt this.1 hc), eq_false hc, ↓reduceIte]

/-- `nanOf` returns an element of `nans`. -/
theorem nanOf_mem (hF : 1 ≤ F.M) {zs : List FVal} (hwf : ∀ z ∈ zs, z.WF F) :
    nanOf F zs ∈ nans F zs := by
  have hc : F.canon < 2 ^ F.M := by
    unfold FloatFormat.canon; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  induction zs with
  | nil => simp [nanOf, nans]
  | cons z zs ih =>
    have ih' := ih fun y hy => hwf y (List.mem_cons_of_mem _ hy)
    by_cases hz : z.IsNaN
    · cases z with
      | nan s n =>
        have hn : n < 2 ^ F.M := (hwf _ List.mem_cons_self).2
        have hlt : Nat.lor n F.canon < 2 ^ F.M := Nat.or_lt_two_pow hn hc
        unfold nans
        split
        · rename_i hall
          have : n = F.canon := hall _ List.mem_cons_self s n rfl
          subst this
          simp [nanOf, Nat.or_self]
        · exact ⟨s, _, rfl, Nat.right_le_or, hlt⟩
      | _ => simp [IsNaN] at hz
    · rw [nanOf_cons hz, nans_cons hz]; exact ih'

/-- The rounder returns the spec's rounding of `±(n / d)·2^e`. -/
theorem roundDyadic_mem (hF : F.Sane) (s : Bool) {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (e : ℤ) :
    roundDyadic F s n d e ∈ ieee F ((if s then -1 else 1) * ((n : ℝ) / d * 2 ^ e)) := by
  rw [roundDyadic_eq F s hn hd e]
  exact (ieee_iff_grid hF _ _).2 rfl

end FVA.Wasm.Num
