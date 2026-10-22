import FVA.Proof.Numerics.Grid
import FVA.Impl.Numerics.Float

/-!
# The executable rounder computes grid rounding

`roundDyadic F s n d e = gridRound F (±(n / d)·2^e)` for `n, d > 0`: the binade from `Nat.log2`,
the ulp exponent, the quotient + remainder tie test, and the overflow test each match their real
definitions.
-/

namespace FVA.Wasm.Num

open FVal Impl

theorem nblt_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by simp [Nat.blt_eq]
theorem nblt_false {a b : ℕ} : Nat.blt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, nblt_true]; exact Nat.not_lt

theorem two_zpow_eq_div (z : ℤ) : (2 : ℝ) ^ z = 2 ^ z.toNat / 2 ^ (-z).toNat := by
  rcases le_or_gt 0 z with hz | hz
  · rw [show (-z).toNat = 0 by omega, pow_zero, div_one, ← zpow_natCast, Int.toNat_of_nonneg hz]
  · rw [show z.toNat = 0 by omega, pow_zero, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      one_div, ← zpow_neg, neg_neg]

theorem int_log_two_eq {r : ℝ} {k : ℤ} (hr : 0 < r) (hlo : (2 : ℝ) ^ k ≤ r)
    (hhi : r < (2 : ℝ) ^ (k + 1)) : Int.log 2 r = k := by
  have h1 : k ≤ Int.log 2 r := (Int.zpow_le_iff_le_log (by norm_num) hr).1 (by exact_mod_cast hlo)
  have h2 : Int.log 2 r < k + 1 :=
    (Int.lt_zpow_iff_log_lt (by norm_num) hr).1 (by exact_mod_cast hhi)
  omega

/-- `log2Frac n d` is `⌊log₂(n / d)⌋`. -/
theorem log2Frac_spec {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (2 : ℝ) ^ log2Frac n d ≤ (n : ℝ) / d ∧ (n : ℝ) / d < (2 : ℝ) ^ (log2Frac n d + 1) := by
  set a := Nat.log2 n with ha
  set b := Nat.log2 d with hb
  have hn1 : 2 ^ a ≤ n := Nat.log2_self_le (by omega)
  have hn2 : n < 2 ^ (a + 1) := Nat.lt_log2_self
  have hd1 : 2 ^ b ≤ d := Nat.log2_self_le (by omega)
  have hd2 : d < 2 ^ (b + 1) := Nat.lt_log2_self
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- real forms of the Nat bounds
  have rn1 : (2 : ℝ) ^ a ≤ n := by exact_mod_cast hn1
  have rn2 : (n : ℝ) < 2 ^ (a + 1) := by exact_mod_cast hn2
  have rd1 : (2 : ℝ) ^ b ≤ d := by exact_mod_cast hd1
  have rd2 : (d : ℝ) < 2 ^ (b + 1) := by exact_mod_cast hd2
  unfold log2Frac
  simp only [← ha, ← hb]
  have hpow : ∀ x y : ℕ, (2 : ℝ) ^ ((x : ℤ) - y) = 2 ^ x / 2 ^ y := by
    intro x y; rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
  have hsplit : ((a : ℤ) - b).toNat = a - b ∧ (-((a : ℤ) - b)).toNat = b - a := by omega
  cases hT : Nat.blt (n * 2 ^ (b - a)) (d * 2 ^ (a - b))
  · -- n·2^(b∸a) ≥ d·2^(a∸b): the binade is a − b
    have hT' : (d : ℝ) * 2 ^ (a - b) ≤ n * 2 ^ (b - a) := by exact_mod_cast nblt_false.1 hT
    simp only [Bool.cond_false]
    constructor
    · rw [two_zpow_eq_div, hsplit.1, hsplit.2, div_le_div_iff₀ (by positivity) hdR]
      linarith
    · rw [show (a : ℤ) - b + 1 = ((a + 1 : ℕ) : ℤ) - b by push_cast; ring, hpow]
      calc (n : ℝ) / d ≤ n / 2 ^ b := by gcongr
        _ < 2 ^ (a + 1) / 2 ^ b := by gcongr
  · have hT' : (n : ℝ) * 2 ^ (b - a) < d * 2 ^ (a - b) := by exact_mod_cast nblt_true.1 hT
    simp only [Bool.cond_true]
    constructor
    · rw [show (a : ℤ) - b - 1 = (a : ℤ) - ((b + 1 : ℕ) : ℤ) by push_cast; ring, hpow]
      calc (2 : ℝ) ^ a / 2 ^ (b + 1) ≤ n / 2 ^ (b + 1) := by gcongr
        _ ≤ n / d := by gcongr
    · rw [show (a : ℤ) - b - 1 + 1 = (a : ℤ) - b by ring, two_zpow_eq_div, hsplit.1, hsplit.2,
        div_lt_div_iff₀ hdR (by positivity)]
      linarith
theorem floor_natDiv {num den : ℕ} (hden : 0 < den) :
    ⌊(num : ℝ) / den⌋ = ((num / den : ℕ) : ℤ) := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hdR]; push_cast; exact_mod_cast Nat.div_mul_le_self num den
  · rw [div_lt_iff₀ hdR]; push_cast
    have : num < (num / den + 1) * den := by
      have := Nat.div_add_mod num den
      have := Nat.mod_lt num hden
      rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega
    exact_mod_cast this

theorem frac_natDiv {num den : ℕ} (hden : 0 < den) :
    (num : ℝ) / den - ⌊(num : ℝ) / den⌋ = ((num % den : ℕ) : ℝ) / den := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have : ((num : ℕ) : ℝ) = den * (num / den : ℕ) + (num % den : ℕ) := by
    exact_mod_cast (Nat.div_add_mod num den).symm
  rw [floor_natDiv hden, Int.cast_natCast, eq_div_iff hdR.ne', sub_mul,
    div_mul_cancel₀ _ hdR.ne', this]
  ring

theorem ceil_natDiv {num den : ℕ} (hden : 0 < den) (hr : 0 < num % den) :
    ⌈(num : ℝ) / den⌉ = ((num / den : ℕ) : ℤ) + 1 := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [Int.ceil_eq_iff]
  have h1 : (num : ℝ) / den - ⌊(num : ℝ) / den⌋ > 0 := by
    rw [frac_natDiv hden]; exact div_pos (by exact_mod_cast hr) hdR
  have h2 : (num : ℝ) / den - ⌊(num : ℝ) / den⌋ < 1 := by
    rw [frac_natDiv hden, div_lt_one hdR]; exact_mod_cast Nat.mod_lt num hden
  rw [floor_natDiv hden] at h1 h2; push_cast at h1 h2 ⊢; constructor <;> linarith

/-- `rneDiv` rounds `num / den` half to even. -/
theorem roundEven_div {num den : ℕ} (hden : 0 < den) :
    roundEven ((num : ℝ) / den) = (rneDiv num den : ℤ) := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have hdiv := Nat.div_add_mod num den
  have hlt := Nat.mod_lt num hden
  have hfl := floor_natDiv (num := num) hden
  have hfrac := frac_natDiv (num := num) hden
  have hceil := ceil_natDiv (num := num) hden
  unfold roundEven
  dsimp only [rneDiv]
  rw [hfrac]
  cases h₁ : Nat.blt (2 * (num % den)) den
  · have h₁' := nblt_false.1 h₁
    have hr : 0 < num % den := by omega
    have hn : ¬ ((num % den : ℕ) : ℝ) / den < 1 / 2 := by
      rw [div_lt_div_iff₀ hdR (by norm_num)]; intro h
      have : ((2 * (num % den) : ℕ) : ℝ) < den := by push_cast; linarith
      exact absurd (by exact_mod_cast this) (Nat.not_lt.2 h₁')
    simp only [hn, ↓reduceIte]; simp only [Bool.cond_false]
    cases h₂ : Nat.blt den (2 * (num % den))
    · have h₂' := nblt_false.1 h₂
      have hng : ¬ ((num % den : ℕ) : ℝ) / den > 1 / 2 := by
        rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) hdR]; intro h
        have : (den : ℝ) < ((2 * (num % den) : ℕ) : ℝ) := by push_cast; linarith
        exact absurd (by exact_mod_cast this) (Nat.not_lt.2 h₂')
      simp only [hng, ↓reduceIte]; simp only [Bool.cond_false, hfl, hceil hr]
      split
      · rename_i heven
        have : num / den % 2 = 0 := by omega
        simp [this]
      · rename_i hodd
        have : num / den % 2 = 1 := by omega
        simp [this]
    · have h₂' := nblt_true.1 h₂
      have hg : ((num % den : ℕ) : ℝ) / den > 1 / 2 := by
        rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) hdR]
        have : (den : ℝ) < ((2 * (num % den) : ℕ) : ℝ) := by exact_mod_cast h₂'
        push_cast at this; linarith
      simp only [hg, ↓reduceIte]; simp only [Bool.cond_true, hceil hr]
      push_cast; ring
  · have h₁' := nblt_true.1 h₁
    have hl : ((num % den : ℕ) : ℝ) / den < 1 / 2 := by
      rw [div_lt_div_iff₀ hdR (by norm_num)]
      have : ((2 * (num % den) : ℕ) : ℝ) < den := by exact_mod_cast h₁'
      push_cast at this; linarith
    simp only [hl, ↓reduceIte]; simp only [Bool.cond_true, hfl]

/-- `limit_N ≤ m·2^q`, decided from `m` and `q` with natural-number operations. -/
theorem limit_le_iff (F : FloatFormat) (m : ℕ) (q : ℤ) :
    limit F ≤ (m : ℝ) * 2 ^ q ↔ 0 < m ∧ ((2 ^ (F.E - 1) : ℕ) : ℤ) ≤ q + (Nat.log2 m : ℤ) := by
  have hlim : limit F = (2 : ℝ) ^ (((2 ^ (F.E - 1) : ℕ) : ℤ)) := by
    unfold limit; rw [zpow_natCast]
  rw [hlim]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, zero_mul, lt_irrefl, false_and, iff_false, not_le]
    exact zpow_pos (by norm_num) _
  · set L : ℤ := ((2 ^ (F.E - 1) : ℕ) : ℤ)
    have hq2 : (0 : ℝ) < 2 ^ q := zpow_pos (by norm_num) _
    rw [← div_le_iff₀ hq2, ← zpow_sub₀ two_ne_zero]
    simp only [hm, true_and]
    constructor
    · intro h
      by_contra hc
      -- log2 m < L − q, so m < 2^(log2 m + 1) ≤ 2^(L − q)
      have h1 : (m : ℝ) < 2 ^ ((Nat.log2 m : ℤ) + 1) := by
        rw [zpow_add₀ two_ne_zero, zpow_one, zpow_natCast]
        exact_mod_cast (by have := @Nat.lt_log2_self m; rw [Nat.pow_succ] at this; exact this)
      have h2 : (2 : ℝ) ^ ((Nat.log2 m : ℤ) + 1) ≤ 2 ^ (L - q) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    · intro h
      calc (2 : ℝ) ^ (L - q) ≤ 2 ^ (Nat.log2 m : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ ≤ m := by rw [zpow_natCast]; exact_mod_cast Nat.log2_self_le (by omega)

theorem blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, nblt_true, decide_eq_true_iff]

/-- `encode` is the case split of `gridRound` after the significand is rounded. -/
theorem encode_eq (F : FloatFormat) (s : Bool) (m : ℕ) (q : ℤ) :
    encode F s m q =
      if limit F ≤ (m : ℝ) * 2 ^ q then inf s
      else if m < 2 ^ F.M then subnormal s m
      else if m < 2 ^ (F.M + 1) then normal s (m - 2 ^ F.M) (q + F.M)
      else normal s 0 (q + F.M + 1) := by
  unfold encode
  simp only [limit_le_iff, blt_eq_decide, ← Bool.decide_and, Bool.cond_decide]

theorem rneNat_dyadic (n : ℕ) {d : ℕ} (hd : 0 < d) (e q : ℤ) :
    rneNat ((n : ℝ) / d * 2 ^ e / 2 ^ q) =
      rneDiv (n * 2 ^ (e - q).toNat) (d * 2 ^ (-(e - q)).toNat) := by
  have hden : 0 < d * 2 ^ (-(e - q)).toNat := Nat.mul_pos hd (Nat.two_pow_pos _)
  have h : (n : ℝ) / d * 2 ^ e / 2 ^ q =
      ((n * 2 ^ (e - q).toNat : ℕ) : ℝ) / ((d * 2 ^ (-(e - q)).toNat : ℕ) : ℝ) := by
    rw [mul_div_assoc, ← zpow_sub₀ two_ne_zero, two_zpow_eq_div]
    push_cast
    rw [div_mul_div_comm]
  rw [rneNat, h, roundEven_div hden, Int.toNat_natCast]

/-- The executable rounder computes `gridRound` of `±(n / d)·2^e`. -/
theorem roundDyadic_eq (F : FloatFormat) (s : Bool) {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (e : ℤ) :
    roundDyadic F s n d e = gridRound F ((if s then -1 else 1) * ((n : ℝ) / d * 2 ^ e)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) _
  have hx : 0 < (n : ℝ) / d * 2 ^ e := mul_pos (div_pos hnR hdR) he
  obtain ⟨h1, h2⟩ := log2Frac_spec hn hd
  have hr0 : (if s then -1 else 1) * ((n : ℝ) / d * 2 ^ e) ≠ 0 := by
    cases s <;> simp [hx.ne']
  have habs : |(if s then -1 else 1) * ((n : ℝ) / d * 2 ^ e)| = (n : ℝ) / d * 2 ^ e := by
    cases s <;> simp [abs_of_pos hx]
  have hsgn : decide ((if s then -1 else 1) * ((n : ℝ) / d * 2 ^ e) < 0) = s := by
    cases s <;> simp [hx, hx.le]
  have hbin : binade ((if s then -1 else 1) * ((n : ℝ) / d * 2 ^ e)) = log2Frac n d + e := by
    unfold binade
    rw [habs]
    apply int_log_two_eq hx
    · rw [zpow_add₀ two_ne_zero]; exact mul_le_mul_of_nonneg_right h1 he.le
    · rw [show log2Frac n d + e + 1 = (log2Frac n d + 1) + e by ring, zpow_add₀ two_ne_zero]
      exact mul_lt_mul_of_pos_right h2 he
  unfold gridRound roundDyadic ulpExp
  simp only [hr0, ↓reduceIte, hbin, habs, hsgn, rneNat_dyadic n hd]
  rw [encode_eq]

end FVA.Wasm.Num
