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

theorem ltNum_iff {z₁ z₂ : FVal} (h₁ : z₁.IsNum) (h₂ : z₂.IsNum) :
    ltNum F z₁ z₂ = true ↔ z₁.toReal F < z₂.toReal F := by
  have hp : (0 : ℝ) < 2 ^ min (ex F z₁) (ex F z₂) := zpow_pos (by norm_num) _
  unfold ltNum
  rw [toReal_eq_units z₁ h₁ (min_le_left _ _), toReal_eq_units z₂ h₂ (min_le_right _ _),
    decide_eq_true_iff, mul_lt_mul_iff_left₀ hp]
  exact_mod_cast Iff.rfl

theorem leNum_iff {z₁ z₂ : FVal} (h₁ : z₁.IsNum) (h₂ : z₂.IsNum) :
    leNum F z₁ z₂ = true ↔ z₁.toReal F ≤ z₂.toReal F := by
  unfold leNum
  rw [Bool.not_eq_true', ← Bool.not_eq_true, ltNum_iff h₂ h₁, not_lt]

/-- Formats whose integers up to `2^(M+1)` are exact (f32, f64). -/
structure FloatFormat.Wide (F : FloatFormat) : Prop extends F.Sane where
  /-- `M + 1 ≤ emax`. -/
  hEM : (F.M : ℤ) + 1 ≤ F.emax

theorem f32fmt_wide : f32fmt.Wide := ⟨f32fmt_sane, by decide⟩
theorem f64fmt_wide : f64fmt.Wide := ⟨f64fmt_sane, by decide⟩

/-- A grid value `±k·2^e` with `k < 2^(M+1)`, `e ≥ emin − M` and binade `≤ emax` is exact: the
rounder returns a well-formed number of that value and sign. -/
theorem roundDyadic_exact (hF : F.Sane) (s : Bool) {k : ℕ} {e : ℤ} (hk : 0 < k)
    (hk' : k < 2 ^ (F.M + 1)) (he : F.emin - F.M ≤ e) (hb : (Nat.log2 k : ℤ) + e ≤ F.emax) :
    (roundDyadic F s k 1 e).WF F ∧ (roundDyadic F s k 1 e).IsNum ∧
      (roundDyadic F s k 1 e).neg = s ∧
      (roundDyadic F s k 1 e).toReal F = (if s then -1 else 1) * ((k : ℝ) * 2 ^ e) := by
  set b := Nat.log2 k with hbdef
  have hk1 : 2 ^ b ≤ k := Nat.log2_self_le (by omega)
  have hk2 : k < 2 ^ (b + 1) := Nat.lt_log2_self
  have hbM : b ≤ F.M := by
    by_contra h
    have : 2 ^ (F.M + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  -- the representation `w` of `±k·2^e`
  obtain ⟨w, hw, hn, hs, hv⟩ : ∃ w : FVal, w.WF F ∧ w.IsNum ∧ w.neg = s ∧
      w.toReal F = (if s then -1 else 1) * ((k : ℝ) * 2 ^ e) := by
    by_cases hnorm : F.emin ≤ (b : ℤ) + e
    · refine ⟨normal s (k * 2 ^ (F.M - b) - 2 ^ F.M) (b + e), ⟨?_, hnorm, hb⟩, trivial, rfl, ?_⟩
      · have : k * 2 ^ (F.M - b) < 2 ^ (F.M + 1) := by
          calc k * 2 ^ (F.M - b) < 2 ^ (b + 1) * 2 ^ (F.M - b) :=
                Nat.mul_lt_mul_of_pos_right hk2 (Nat.two_pow_pos _)
            _ = 2 ^ (F.M + 1) := by rw [← Nat.pow_add]; congr 1; omega
        rw [Nat.pow_succ] at this; omega
      · have hge : 2 ^ F.M ≤ k * 2 ^ (F.M - b) := by
          calc 2 ^ F.M = 2 ^ b * 2 ^ (F.M - b) := by rw [← Nat.pow_add]; congr 1; omega
            _ ≤ k * 2 ^ (F.M - b) := Nat.mul_le_mul_right _ hk1
        simp only [toReal]
        rw [Nat.cast_sub hge]
        push_cast
        rw [zpow_add₀ h2, zpow_neg, zpow_natCast, zpow_natCast,
          show (2 : ℝ) ^ (F.M - b) = 2 ^ F.M / 2 ^ b by
            rw [eq_div_iff (by positivity), ← pow_add]; congr 1; omega]
        field_simp
        ring
    · push Not at hnorm
      have hexp : 0 ≤ e - (F.emin - F.M) := by omega
      refine ⟨subnormal s (k * 2 ^ (e - (F.emin - F.M)).toNat), ?_, trivial, rfl, ?_⟩
      · show k * 2 ^ (e - (F.emin - F.M)).toNat < 2 ^ F.M
        calc k * 2 ^ (e - (F.emin - F.M)).toNat < 2 ^ (b + 1) * 2 ^ (e - (F.emin - F.M)).toNat :=
              Nat.mul_lt_mul_of_pos_right hk2 (Nat.two_pow_pos _)
          _ = 2 ^ (b + 1 + (e - (F.emin - F.M)).toNat) := by rw [← Nat.pow_add]
          _ ≤ 2 ^ F.M := Nat.pow_le_pow_right (by norm_num) (by omega)
      · simp only [toReal]
        push_cast
        rw [← zpow_natCast, Int.toNat_of_nonneg hexp, zpow_neg, zpow_natCast]
        rw [show (2 : ℝ) ^ (e - (F.emin - F.M)) = 2 ^ e * 2 ^ (F.M : ℤ) / 2 ^ F.emin by
          rw [zpow_sub₀ h2, zpow_sub₀ h2]; field_simp]
        rw [zpow_natCast]
        field_simp
  have hr0 : (if s then -1 else 1) * ((k : ℝ) * 2 ^ e) ≠ 0 := by
    have : (0 : ℝ) < k * 2 ^ e := mul_pos (by exact_mod_cast hk) (zpow_pos (by norm_num) _)
    cases s <;> simp [this.ne']
  have hmem := roundDyadic_mem hF s hk Nat.one_pos e
  rw [Nat.cast_one, div_one] at hmem
  have heq : roundDyadic F s k 1 e = w := (ieee_exact_iff hw hn hv hr0).1 hmem
  rw [heq]
  exact ⟨hw, hn, hs, hv⟩

end FVA.Wasm.Num
