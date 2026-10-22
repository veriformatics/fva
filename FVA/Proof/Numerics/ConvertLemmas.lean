import FVA.Proof.Numerics.Basic

/-!
# Conversion proof support

Dyadic truncation, predicate reflection, NaN payloads and exact f32-to-f64 promotion.
-/

namespace FVA.Wasm.Num.ConvertLemmas

open FVal Impl Classical

lemma isNaN_decide (z : FVal) : isNaN z = decide z.IsNaN := by
  apply Bool.eq_iff_iff.mpr
  simp only [isNaN_iff, decide_eq_true_iff]

lemma isZero_decide (z : FVal) : isZero z = decide z.IsZero := by
  apply Bool.eq_iff_iff.mpr
  simp only [isZero_iff, decide_eq_true_iff]

lemma ltNum_decide {F : FloatFormat} {z₁ z₂ : FVal} (h₁ : z₁.IsNum) (h₂ : z₂.IsNum) :
    ltNum F z₁ z₂ = decide (z₁.toReal F < z₂.toReal F) := by
  apply Bool.eq_iff_iff.mpr
  simp only [ltNum_iff h₁ h₂, decide_eq_true_iff]

lemma leNum_decide {F : FloatFormat} {z₁ z₂ : FVal} (h₁ : z₁.IsNum) (h₂ : z₂.IsNum) :
    leNum F z₁ z₂ = decide (z₁.toReal F ≤ z₂.toReal F) := by
  apply Bool.eq_iff_iff.mpr
  simp only [leNum_iff h₁ h₂, decide_eq_true_iff]

lemma truncR_neg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : truncR (-x) = -⌊x⌋ := by
  by_cases h0 : x = 0
  · simp [h0, truncR]
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have hn : ¬ 0 ≤ -x := not_le.mpr (neg_neg_of_pos hp)
    simp [truncR, hn, Int.ceil_neg]

lemma truncR_signed (s : Bool) {x : ℝ} (hx : 0 ≤ x) :
    truncR ((if s then -1 else 1) * x) = if s then -⌊x⌋ else ⌊x⌋ := by
  cases s
  · simp [truncR, hx]
  · simpa using truncR_neg_of_nonneg hx

lemma floor_dyadic (n : Nat) (e : Int) :
    ⌊(n : ℝ) * 2 ^ e⌋ = ((match e with
      | .ofNat j => n * 2 ^ j
      | .negSucc j => n / 2 ^ (j + 1)) : Nat) := by
  cases e with
  | ofNat j =>
    change ⌊(n : ℝ) * 2 ^ (j : Int)⌋ = ((n * 2 ^ j : Nat) : Int)
    rw [zpow_natCast, show (n : ℝ) * 2 ^ j = ((n * 2 ^ j : Nat) : ℝ) by push_cast; rfl,
      Int.floor_natCast]
  | negSucc j =>
    change ⌊(n : ℝ) * 2 ^ (Int.negSucc j)⌋ = ((n / 2 ^ (j + 1) : Nat) : Int)
    rw [zpow_negSucc, ← div_eq_mul_inv,
      show (2 : ℝ) ^ (j + 1) = ((2 ^ (j + 1) : Nat) : ℝ) by push_cast; rfl,
      Int.floor_div_natCast, Int.floor_natCast, Int.natCast_ediv]

lemma ofInt_mem {F : FloatFormat} (hF : F.Sane) (i : Int) :
    Impl.ofInt F i ∈ ieee F i := by
  cases i with
  | ofNat n =>
    by_cases h0 : n = 0
    · subst n
      simp [Impl.ofInt, ieee, Ieee]
    · have h := roundDyadic_mem hF false (Nat.pos_of_ne_zero h0) Nat.one_pos 0
      simpa [Impl.ofInt, h0] using h
  | negSucc n =>
    have h := roundDyadic_mem hF true (Nat.succ_pos n) Nat.one_pos 0
    simpa [Impl.ofInt, Nat.cast_add, Int.cast_negSucc] using h

lemma nan_mem_nil (F : FloatFormat) (s : Bool) : nan s F.canon ∈ nans F [] := by
  simp [nans]

lemma nan_mem_noncanon {F : FloatFormat} (hc : 1 ≠ F.canon) {s : Bool} {n : Nat}
    (hn : F.canon ≤ n) (hn' : n < 2 ^ F.M) : nan s n ∈ nans F [nan false 1] := by
  have h : ¬ (∀ z ∈ [nan false 1], ∀ s n, z = nan s n → n = F.canon) := by
    intro hall
    exact hc (hall _ List.mem_cons_self false 1 rfl)
  simp only [nans, h, ↓reduceIte, Set.mem_ofPred_eq]
  exact ⟨s, n, rfl, hn, hn'⟩

lemma f32_sig_lt {z : FVal} (hz : z.WF f32fmt) : sig f32fmt z < 2 ^ 24 := by
  cases z <;> norm_num [WF, sig, f32fmt] at * <;> omega

lemma f32_ex_bounds {z : FVal} (hz : z.WF f32fmt) : -149 ≤ ex f32fmt z ∧ ex f32fmt z ≤ 104 := by
  cases z <;> norm_num [WF, ex, f32fmt, FloatFormat.emin, FloatFormat.emax] at *
  omega

lemma promote_num {z : FVal} (hz : z.WF f32fmt) (hn : z.IsNum) (h0 : ¬ z.IsZero) :
    (roundDyadic f64fmt z.neg (sig f32fmt z) 1 (ex f32fmt z)).WF f64fmt ∧
    (roundDyadic f64fmt z.neg (sig f32fmt z) 1 (ex f32fmt z)).IsNum ∧
    (roundDyadic f64fmt z.neg (sig f32fmt z) 1 (ex f32fmt z)).neg = z.neg ∧
    (roundDyadic f64fmt z.neg (sig f32fmt z) 1 (ex f32fmt z)).toReal f64fmt = z.toReal f32fmt := by
  have hp : 0 < sig f32fmt z := sig_pos hn h0
  have hl : Nat.log2 (sig f32fmt z) < 24 := (Nat.log2_lt hp.ne').mpr (f32_sig_lt hz)
  have hb := f32_ex_bounds hz
  have h := roundDyadic_exact f64fmt_sane z.neg hp
    (show sig f32fmt z < 2 ^ (f64fmt.M + 1) by
      have := f32_sig_lt hz
      norm_num [f64fmt] at *
      omega)
    (show f64fmt.emin - f64fmt.M ≤ ex f32fmt z by
      norm_num [f64fmt, FloatFormat.emin]
      omega)
    (show (Nat.log2 (sig f32fmt z) : Int) + ex f32fmt z ≤ f64fmt.emax by
      norm_num [f64fmt, FloatFormat.emax]
      omega)
  simpa only [toReal_eq_sig z hn] using h

lemma demote_num {z : FVal} (hn : z.IsNum) (h0 : ¬ z.IsZero) :
    roundDyadic f32fmt z.neg (sig f64fmt z) 1 (ex f64fmt z) ∈ ieee f32fmt (z.toReal f64fmt) := by
  rw [toReal_eq_sig z hn]
  simpa only [Nat.cast_one, div_one] using
    roundDyadic_mem f32fmt_sane z.neg (sig_pos hn h0) Nat.one_pos (ex f64fmt z)

end FVA.Wasm.Num.ConvertLemmas
