import FVA.Proof.Numerics.Basic

/-!
# Arithmetic operators return allowed results

`Impl.fadd`, `fsub`, `fmul`, `fdiv`, `fmin`, `fmax` on well-formed operands return an element of
the spec's result set. Each proof splits both operands into constructors (`fval_cases`), where
the impl's `Bool` tests and the spec's predicates evaluate alike, then closes every case with a
NaN-choice, singleton or exact-arithmetic lemma (`fval_close`).
-/

namespace FVA.Wasm.Num

open FVal Impl

variable {F : FloatFormat}

@[simp] theorem isZero_subnormal_iff {s : Bool} {m : ℕ} : (subnormal s m).IsZero ↔ m = 0 := by
  cases m <;> simp [IsZero]
@[simp] theorem isZero_normal_iff {s : Bool} {m : ℕ} {e : ℤ} : (normal s m e).IsZero ↔ False := by
  simp [IsZero]
@[simp] theorem isZero_inf_iff {s : Bool} : (inf s).IsZero ↔ False := by simp [IsZero]
@[simp] theorem isZero_nan_iff {s : Bool} {n : ℕ} : (nan s n).IsZero ↔ False := by simp [IsZero]
@[simp] theorem isNum_normal {s : Bool} {m : ℕ} {e : ℤ} : (normal s m e).IsNum := trivial
@[simp] theorem isNum_subnormal {s : Bool} {m : ℕ} : (subnormal s m).IsNum := trivial

theorem nanOf_mem₀ (hM : 1 ≤ F.M) : nanOf F [] ∈ nans F [] := nanOf_mem hM (by simp)

theorem nanOf_mem₂ (hM : 1 ≤ F.M) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    nanOf F [z₁, z₂] ∈ nans F [z₁, z₂] :=
  nanOf_mem hM (by simp [h₁, h₂])

theorem sig_normal_pos {s : Bool} {m : ℕ} {e : ℤ} : 0 < sig F (normal s m e) :=
  Nat.add_pos_left (Nat.two_pow_pos _) _

/-- The exact sum on the grid of the smaller exponent: `+0` on cancellation, else rounded. -/
theorem addNum_mem (hF : F.Sane) {z₁ z₂ : FVal} (n₁ : z₁.IsNum) (n₂ : z₂.IsNum) :
    addNum F z₁ z₂ ∈ (if z₁.toReal F = -z₂.toReal F then ({posZero} : Set FVal)
      else ieee F (z₁.toReal F + z₂.toReal F)) := by
  have ht₁ := toReal_eq_units (F := F) z₁ n₁ (min_le_left (ex F z₁) (ex F z₂))
  have ht₂ := toReal_eq_units (F := F) z₂ n₂ (min_le_right (ex F z₁) (ex F z₂))
  have hcancel : z₁.toReal F = -z₂.toReal F ↔ z₁.toReal F + z₂.toReal F = 0 := by
    constructor <;> intro h <;> linarith
  have hsum : z₁.toReal F + z₂.toReal F =
      ((units F z₁ (min (ex F z₁) (ex F z₂)) + units F z₂ (min (ex F z₁) (ex F z₂)) : ℤ) : ℝ) *
        2 ^ min (ex F z₁) (ex F z₂) := by
    rw [ht₁, ht₂]; push_cast; ring
  simp only [hcancel, hsum]
  unfold addNum
  dsimp only
  generalize min (ex F z₁) (ex F z₂) = e
  generalize units F z₁ e + units F z₂ e = S
  have he : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) _
  cases S with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n =>
      have hc : ((Int.ofNat (n + 1) : ℤ) : ℝ) = (n : ℝ) + 1 := by
        rw [Int.ofNat_eq_natCast]; push_cast; ring
      have h0 : ((Int.ofNat (n + 1) : ℤ) : ℝ) * 2 ^ e ≠ 0 := by rw [hc]; positivity
      simp only [h0, ↓reduceIte]
      have := roundDyadic_mem hF false (Nat.succ_pos n) Nat.one_pos e
      simpa using this
  | negSucc n =>
    have h0 : ((Int.negSucc n : ℤ) : ℝ) * 2 ^ e ≠ 0 := by
      have : ((Int.negSucc n : ℤ) : ℝ) < 0 := by exact_mod_cast Int.negSucc_lt_zero n
      exact (mul_neg_of_neg_of_pos this he).ne
    simp only [h0, ↓reduceIte]
    have := roundDyadic_mem hF true (Nat.succ_pos n) Nat.one_pos e
    convert this using 2
    simp [Int.cast_negSucc]; ring

theorem addNum_cancel (hF : F.Sane) {z₁ z₂ : FVal} (n₁ : z₁.IsNum) (n₂ : z₂.IsNum)
    (h : z₁.toReal F = -z₂.toReal F) : addNum F z₁ z₂ = posZero := by
  have := addNum_mem hF n₁ n₂
  simpa only [h, ↓reduceIte, Set.mem_singleton_iff] using this

theorem addNum_ieee (hF : F.Sane) {z₁ z₂ : FVal} (n₁ : z₁.IsNum) (n₂ : z₂.IsNum)
    (h : ¬ z₁.toReal F = -z₂.toReal F) :
    addNum F z₁ z₂ ∈ ieee F (z₁.toReal F + z₂.toReal F) := by
  have := addNum_mem hF n₁ n₂
  simpa only [h, ↓reduceIte] using this

/-- The exact product, rounded. -/
theorem mulNum_mem (hF : F.Sane) {z₁ z₂ : FVal} (n₁ : z₁.IsNum) (n₂ : z₂.IsNum)
    (p₁ : 0 < sig F z₁) (p₂ : 0 < sig F z₂) :
    roundDyadic F (z₁.neg != z₂.neg) (sig F z₁ * sig F z₂) 1 (ex F z₁ + ex F z₂) ∈
      ieee F (z₁.toReal F * z₂.toReal F) := by
  have := roundDyadic_mem hF (z₁.neg != z₂.neg) (Nat.mul_pos p₁ p₂) Nat.one_pos
    (ex F z₁ + ex F z₂)
  convert this using 2
  rw [toReal_eq_sig z₁ n₁, toReal_eq_sig z₂ n₂, zpow_add₀ two_ne_zero]
  generalize z₁.neg = a
  generalize z₂.neg = b
  cases a <;> cases b <;> simp <;> ring

/-- The exact quotient, rounded. -/
theorem divNum_mem (hF : F.Sane) {z₁ z₂ : FVal} (n₁ : z₁.IsNum) (n₂ : z₂.IsNum)
    (p₁ : 0 < sig F z₁) (p₂ : 0 < sig F z₂) :
    roundDyadic F (z₁.neg != z₂.neg) (sig F z₁) (sig F z₂) (ex F z₁ - ex F z₂) ∈
      ieee F (z₁.toReal F / z₂.toReal F) := by
  have := roundDyadic_mem hF (z₁.neg != z₂.neg) p₁ p₂ (ex F z₁ - ex F z₂)
  convert this using 2
  have hs : (0 : ℝ) < sig F z₂ := by exact_mod_cast p₂
  rw [toReal_eq_sig z₁ n₁, toReal_eq_sig z₂ n₂, zpow_sub₀ two_ne_zero]
  generalize z₁.neg = a
  generalize z₂.neg = b
  cases a <;> cases b <;> simp <;> field_simp

/-- Split two operands into constructors; evaluate the impl's `Bool` tests and the spec's
predicates on them. -/
macro (name := fvalCases) "fval_cases " z₁:ident z₂:ident : tactic => `(tactic|
  (cases $z₁:ident <;> cases $z₂:ident <;> simp only [isNaN, isInf, isZero, IsNaN, IsInf,
    isZero_subnormal_iff, isZero_normal_iff, isZero_inf_iff, isZero_nan_iff, FVal.neg,
    FVal.inf.injEq, isNum_normal, isNum_subnormal, Bool.or_false, Bool.or_true, Bool.false_or,
    Bool.and_false, Bool.false_and,
    Bool.and_true, Bool.true_and, Bool.cond_true, Bool.cond_false, Bool.not_true,
    Bool.not_false, or_false, false_or, or_true, true_or, and_false, false_and, and_true,
    true_and, and_assoc, ↓reduceIte, cond_eq_ite, Bool.and_eq_true, Bool.or_eq_true,
    bne_iff_ne, Nat.beq_eq, ne_eq, leNum_iff, ge_iff_le, reduceCtorEq]))

/-- `0 < sig` of a number left by `fval_cases` (a subnormal one carries `m ≠ 0`). -/
macro (name := sigPos) "sig_pos" : tactic => `(tactic|
  first | exact sig_normal_pos | (simp only [sig]; omega))

/-- Close one case: NaN results, singletons, or an exact-arithmetic lemma. -/
macro (name := fvalClose) "fval_close" : tactic => `(tactic|
  first
    | exact nanOf_mem₂ ‹_› ‹_› ‹_›
    | exact nanOf_mem₀ ‹_›
    | exact Set.mem_singleton _
    | exact Set.mem_singleton_iff.2 (addNum_cancel ‹_› trivial trivial ‹_›)
    | exact addNum_ieee ‹_› trivial trivial ‹_›
    | exact mulNum_mem ‹_› trivial trivial (by sig_pos) (by sig_pos)
    | exact divNum_mem ‹_› trivial trivial (by sig_pos) (by sig_pos)
    | (simp_all; done))

theorem fadd_mem (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    Impl.fadd F z₁ z₂ ∈ fadd F z₁ z₂ := by
  have hM := hF.hM
  unfold Impl.fadd fadd
  fval_cases z₁ z₂
  all_goals first | fval_close | (split_ifs <;> fval_close)

theorem fmul_mem (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    Impl.fmul F z₁ z₂ ∈ fmul F z₁ z₂ := by
  have hM := hF.hM
  unfold Impl.fmul fmul
  fval_cases z₁ z₂
  all_goals first | fval_close | (split_ifs <;> fval_close)

theorem fdiv_mem (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    Impl.fdiv F z₁ z₂ ∈ fdiv F z₁ z₂ := by
  have hM := hF.hM
  unfold Impl.fdiv fdiv
  fval_cases z₁ z₂
  all_goals first | fval_close | (split_ifs <;> fval_close)

theorem fmin_mem (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    Impl.fmin F z₁ z₂ ∈ fmin F z₁ z₂ := by
  have hM := hF.hM
  unfold Impl.fmin fmin
  fval_cases z₁ z₂
  all_goals first | fval_close | (split_ifs <;> fval_close)

theorem fmax_mem (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    Impl.fmax F z₁ z₂ ∈ fmax F z₁ z₂ := by
  have hM := hF.hM
  unfold Impl.fmax fmax
  fval_cases z₁ z₂
  all_goals first | fval_close | (split_ifs <;> fval_close)

theorem toReal_neg_normal (s : Bool) (m : ℕ) (e : ℤ) :
    toReal F (normal (!s) m e) = -toReal F (normal s m e) := by
  cases s <;> simp [toReal] <;> ring

theorem toReal_neg_subnormal (s : Bool) (m : ℕ) :
    toReal F (subnormal (!s) m) = -toReal F (subnormal s m) := by
  cases s <;> simp [toReal]

theorem fneg_wf {z : FVal} (hz : z.WF F) : (fneg z).WF F := by
  cases z <;> exact hz

theorem nans_fneg (z₁ z₂ : FVal) : nans F [z₁, fneg z₂] = nans F [z₁, z₂] := by
  have hc : (∀ s n, fneg z₂ = nan s n → n = F.canon) ↔ (∀ s n, z₂ = nan s n → n = F.canon) := by
    cases z₂ with
    | nan t n =>
      simp only [fneg, FVal.withSign, FVal.neg, FVal.nan.injEq]
      constructor
      · rintro h s n' ⟨rfl, rfl⟩; exact h _ _ ⟨rfl, rfl⟩
      · rintro h s n' ⟨rfl, rfl⟩; exact h _ _ ⟨rfl, rfl⟩
    | _ => simp [fneg, FVal.withSign]
  have hiff : (∀ y ∈ [z₁, fneg z₂], ∀ s n, y = nan s n → n = F.canon) ↔
      (∀ y ∈ [z₁, z₂], ∀ s n, y = nan s n → n = F.canon) := by
    simp only [List.forall_mem_cons, hc]
  unfold nans
  by_cases h : ∀ y ∈ [z₁, z₂], ∀ s n, y = nan s n → n = F.canon
  · simp only [eq_true h, eq_true (hiff.2 h), ↓reduceIte]
  · simp only [eq_false h, eq_false (mt hiff.1 h), ↓reduceIte]

/-- The spec's `fsub` cases are `fadd`'s with the second operand negated. -/
theorem fsub_eq (z₁ z₂ : FVal) : fsub F z₁ z₂ = fadd F z₁ (fneg z₂) := by
  unfold fsub fadd
  rw [nans_fneg]
  cases z₁ <;> cases z₂ <;> simp [fneg, FVal.withSign, IsNaN, IsInf, FVal.neg,
    toReal_neg_normal, toReal_neg_subnormal, sub_eq_add_neg]
  all_goals (split_ifs <;> simp_all)

theorem fsub_mem (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    Impl.fsub F z₁ z₂ ∈ fsub F z₁ z₂ := by
  rw [fsub_eq]
  exact fadd_mem hF h₁ (fneg_wf h₂)

end FVA.Wasm.Num
