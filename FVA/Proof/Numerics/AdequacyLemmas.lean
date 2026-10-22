import FVA.Proof.Numerics.Basic

/-! # Auxiliary facts for float-spec adequacy -/

namespace FVA.Wasm.Num.Adequacy

open FVal

variable {F : FloatFormat}

theorem nans_isNaN {zs : List FVal} {v : FVal} (hv : v ∈ nans F zs) : v.IsNaN := by
  unfold nans at hv
  split at hv
  · rcases hv with ⟨s, rfl⟩
    trivial
  · rcases hv with ⟨s, n, rfl, _, _⟩
    trivial

theorem canon_bounds (hF : F.Sane) : 1 ≤ F.canon ∧ F.canon < 2 ^ F.M := by
  constructor
  · exact Nat.one_le_pow _ _ (by decide)
  · exact Nat.pow_lt_pow_right (by decide) (by have := hF.hM; omega)

theorem rectify_wf {r z : ℝ} {v : FVal} (hv : Rectify F r z v) : v.WF F := by
  rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, hw, _, _⟩
  · trivial
  · trivial
  · exact Nat.two_pow_pos _
  · exact hw

theorem num_nonzero {z : FVal} (hz : z.WF F) (hn : z.IsNum) (h0 : ¬ z.IsZero) :
    z.toReal F ≠ 0 := by
  intro he
  have heq := num_zero_eq hz hn he
  rw [heq] at h0
  exact h0 trivial

theorem num_of_not_nan_inf {z : FVal} (hn : ¬ z.IsNaN) (hi : ¬ z.IsInf) : z.IsNum := by
  cases z <;> simp_all [IsNaN, IsInf, IsNum]

theorem field_layout {P Q e m : ℕ} (hP : 0 < P) (he : e < Q)
    (hm : m < P) (s : Bool) :
    let n := (if s then Q * P else 0) + e * P + m
    n < 2 * (Q * P) ∧ decide (Q * P ≤ n) = s ∧ n / P % Q = e ∧ n % P = m := by
  have hlow : e * P + m < Q * P := by
    calc e * P + m < e * P + P := Nat.add_lt_add_left hm _
      _ = (e + 1) * P := by ring
      _ ≤ Q * P := Nat.mul_le_mul_right P he
  have hdiv : (e * P + m) / P = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hm, Nat.zero_add]
  have hmod : (e * P + m) % P = m := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    exact ⟨by omega, by simp [Nat.not_le_of_gt hlow], by rw [hdiv, Nat.mod_eq_of_lt he], hmod⟩
  · simp only [↓reduceIte]
    have hd : (Q * P + e * P + m) / P = Q + e := by
      rw [show Q * P + e * P + m = m + (Q + e) * P by ring,
        Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hm, Nat.zero_add]
    refine ⟨by omega, by simp only [decide_eq_true_eq]; omega, ?_, ?_⟩
    · rw [hd, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt he]
    · rw [show Q * P + e * P + m = m + (Q + e) * P by ring,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]

theorem field_reassemble {P Q n : ℕ} (hP : 0 < P) (hQ : 0 < Q)
    (hn : n < 2 * (Q * P)) :
    (if decide (Q * P ≤ n) then Q * P else 0) + (n / P % Q) * P + n % P = n := by
  have hpq : 0 < Q * P := Nat.mul_pos hQ hP
  have hq : n / (Q * P) < 2 := (Nat.div_lt_iff_lt_mul hpq).2 hn
  have hraw := Nat.div_add_mod' n (Q * P)
  have hrem := Nat.mod_lt n hpq
  have hexp := Nat.div_add_mod' (n / P) Q
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm P Q] at hexp
  have hreassemble : n = n / (Q * P) * (Q * P) + (n / P % Q) * P + n % P := by
    calc n = (n / P) * P + n % P := (Nat.div_add_mod' n P).symm
      _ = (n / (Q * P) * Q + n / P % Q) * P + n % P := by rw [hexp]
      _ = _ := by ring
  have hcases := Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.le_of_lt_succ hq)
  rcases hcases with hzero | hone
  · rw [hzero] at hraw hreassemble
    simp only [Nat.zero_mul, Nat.zero_add] at hraw hreassemble
    have hs : ¬ Q * P ≤ n := by omega
    simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact hreassemble.symm
  · rw [hone] at hraw hreassemble
    simp only [Nat.one_mul] at hraw hreassemble
    have hs : Q * P ≤ n := by omega
    simp only [hs, decide_true, ↓reduceIte]
    exact hreassemble.symm

theorem float_width (F : FloatFormat) :
    2 ^ F.N = 2 * (2 ^ F.E * 2 ^ F.M) := by
  simp [FloatFormat.N, Nat.pow_add, Nat.mul_assoc]

theorem float_layout (s : Bool) {e m : ℕ} (he : e < 2 ^ F.E) (hm : m < 2 ^ F.M) :
    let b := BitVec.ofNat F.N
      ((if s then 2 ^ (F.E + F.M) else 0) + e * 2 ^ F.M + m)
    decide (2 ^ (F.E + F.M) ≤ b.toNat) = s ∧
      b.toNat / 2 ^ F.M % 2 ^ F.E = e ∧ b.toNat % 2 ^ F.M = m := by
  have hl := field_layout (Nat.two_pow_pos F.M) he hm s
  have hb : (if s then 2 ^ (F.E + F.M) else 0) + e * 2 ^ F.M + m < 2 ^ F.N := by
    rw [float_width F]
    simpa only [Nat.pow_add] using hl.1
  simp only [← Nat.pow_add] at hl
  dsimp only
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  exact hl.2

theorem float_reassemble (b : BitVec F.N) :
    (if decide (2 ^ (F.E + F.M) ≤ b.toNat) then 2 ^ (F.E + F.M) else 0) +
      (b.toNat / 2 ^ F.M % 2 ^ F.E) * 2 ^ F.M + b.toNat % 2 ^ F.M = b.toNat := by
  have hb := b.isLt
  rw [float_width F] at hb
  simpa only [Nat.pow_add] using
    field_reassemble (Nat.two_pow_pos F.M) (Nat.two_pow_pos F.E) hb

theorem exponent_span (hF : F.Sane) :
    F.emin + F.emax = 1 ∧ ((2 ^ F.E : ℕ) : ℤ) = 2 * F.emax + 2 := by
  have he : F.E = (F.E - 1) + 1 := by have := hF.hE; omega
  constructor
  · simp [FloatFormat.emin, FloatFormat.emax]
  · rw [Nat.cast_pow, Nat.cast_ofNat, he, pow_succ]
    simp only [FloatFormat.emax]
    ring

theorem exponent_field_bounds (hF : F.Sane) {e : ℤ}
    (hl : F.emin ≤ e) (hu : e ≤ F.emax) :
    1 ≤ (e + F.emax).toNat ∧ (e + F.emax).toNat < 2 ^ F.E - 1 := by
  obtain ⟨hs, hp⟩ := exponent_span hF
  have he : 0 ≤ e + F.emax := by omega
  have ht := Int.toNat_of_nonneg he
  have hp' : (2 ^ F.E : ℕ) > 0 := Nat.two_pow_pos _
  omega

theorem ceil_nonzero {r : ℝ} (hr : r ≠ 0) (h : ¬ (-1 < r ∧ r < 0)) :
    (⌈r⌉ : ℝ) ≠ 0 := by
  intro hz
  have he : ⌈r⌉ = 0 := by exact_mod_cast hz
  have hb := Int.ceil_eq_zero_iff.1 he
  exact h ⟨hb.1, lt_of_le_of_ne hb.2 hr⟩

theorem floor_nonzero {r : ℝ} (hr : r ≠ 0) (h : ¬ (0 < r ∧ r < 1)) :
    (⌊r⌋ : ℝ) ≠ 0 := by
  intro hz
  have he : ⌊r⌋ = 0 := by exact_mod_cast hz
  have hb := Int.floor_eq_zero_iff.1 he
  exact h ⟨lt_of_le_of_ne hb.1 hr.symm, hb.2⟩

theorem roundEven_zero_bounds {r : ℝ} (hz : roundEven r = 0) :
    -1 / 2 ≤ r ∧ r ≤ 1 / 2 := by
  have hf := Int.floor_le r
  have hc := Int.le_ceil r
  have hfc : (⌈r⌉ : ℝ) ≤ (⌊r⌋ : ℝ) + 1 := by
    exact_mod_cast Int.ceil_le_floor_add_one r
  unfold roundEven at hz
  split at hz
  · have he : (⌊r⌋ : ℝ) = 0 := by exact_mod_cast hz
    constructor <;> linarith
  · split at hz
    · have he : (⌈r⌉ : ℝ) = 0 := by exact_mod_cast hz
      constructor <;> linarith
    · split at hz
      · have he : (⌊r⌋ : ℝ) = 0 := by exact_mod_cast hz
        constructor <;> linarith
      · have he : (⌈r⌉ : ℝ) = 0 := by exact_mod_cast hz
        constructor <;> linarith

end FVA.Wasm.Num.Adequacy
