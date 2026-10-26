import FVATest.Subjects.Tmm.Exact
import FVATest.Subjects.Tmm.Check
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.List.GetD

/-! `RefutesExactAverageTMM`'s checker, proven sound (certificate convention `R.check`,
`R.check_sound`). The kernel never evaluates the relation where it is slow or stuck: order
statistics come from counts (`List.mergeSort` is well-founded recursion, which the kernel does not
unfold), ranks from natural-number cross products, logarithms from Mathlib's series bound; each
replacement is proven equal to, or a bound on, the relation's definition. The witness is one
sample's factor ratio to the reference: the centring cancels, so one weighted log sum decides. -/

namespace Subjects.Tmm

open FVA.Cert

/-! ## One reading per count file -/

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  unfold decimal
  split
  · simp
  · simpa using Nat.digits_ne_nil_iff_ne_zero.mpr ‹_›

theorem mem_row : ∀ {r : List Nat} {b : UInt8}, b ∈ List.intercalate [9] (r.map decimal) →
    b = 9 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57)
  | [], _, h => by simp at h
  | [_], _, h => by
    rw [List.map_cons, List.map_nil, List.intercalate_singleton] at h
    exact .inr (decimal_byte h)
  | a :: c :: m, b, h => by
    rw [List.map_cons, List.map_cons, List.intercalate_cons_cons] at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact .inr (decimal_byte h)
    · exact .inl (List.mem_singleton.mp h)
    · exact mem_row (r := c :: m) (by simpa using h)

theorem row_prefix (a : Nat) (m : List Nat) :
    ∃ t, List.intercalate [9] ((a :: m).map decimal) = decimal a ++ t := by
  cases m with
  | nil => exact ⟨[], by simp [List.intercalate_singleton]⟩
  | cons c m => exact ⟨_, by rw [List.map_cons, List.map_cons, List.intercalate_cons_cons,
      List.append_assoc]⟩

theorem row_inj : ∀ {r r' : List Nat},
    List.intercalate [9] (r.map decimal) = List.intercalate [9] (r'.map decimal) → r = r'
  | [], [], _ => rfl
  | [], b :: m, h => by
    obtain ⟨t, ht⟩ := row_prefix b m
    rw [ht] at h
    exact absurd (List.append_eq_nil_iff.mp h.symm).1 (decimal_ne_nil b)
  | a :: m, [], h => by
    obtain ⟨t, ht⟩ := row_prefix a m
    rw [ht] at h
    exact absurd (List.append_eq_nil_iff.mp h).1 (decimal_ne_nil a)
  | [a], [b], h => by
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton] at h
    rw [decimal_inj h]
  | [a], b :: d :: m, h => by
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton,
      List.intercalate_cons_cons] at h
    have : (9 : UInt8) ∈ decimal a := by rw [h]; simp
    exact absurd (decimal_byte this) (by decide)
  | a :: c :: m, [b], h => by
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton,
      List.intercalate_cons_cons] at h
    have : (9 : UInt8) ∈ decimal b := by rw [← h]; simp
    exact absurd (decimal_byte this) (by decide)
  | a :: c :: m, b :: d :: m', h => by
    rw [List.map_cons, List.map_cons, List.intercalate_cons_cons, List.map_cons, List.map_cons,
      List.intercalate_cons_cons, List.append_assoc, List.append_assoc, List.singleton_append,
      List.singleton_append] at h
    have h9 : ∀ n, (9 : UInt8) ∉ decimal n := fun n hn => absurd (decimal_byte hn) (by decide)
    obtain ⟨hab, hr⟩ := split_first (h9 a) (h9 b) h
    rw [decimal_inj hab, row_inj (r := c :: m) (r' := d :: m') (by simpa using hr)]

theorem countsText_inj : ∀ {rows rows' : List (List Nat)}, countsText rows = countsText rows' →
    rows = rows'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [countsText] at h
  | _ :: _, [], h => by simp [countsText] at h
  | r :: rs, r' :: rs', h => by
    simp only [countsText, List.flatMap_cons, List.append_assoc, List.singleton_append] at h
    have h10 : ∀ s : List Nat, (10 : UInt8) ∉ List.intercalate [9] (s.map decimal) :=
      fun s hs => by rcases mem_row hs with h | h <;> revert h <;> decide
    obtain ⟨h1, h2⟩ := split_first (h10 r) (h10 r') h
    rw [row_inj h1, countsText_inj (rows := rs) (rows' := rs') h2]

/-- Split at every tab (byte 9). -/
def cells : List UInt8 → List UInt8 → List (List UInt8)
  | [], cur => [cur.reverse]
  | b :: bs, cur => if b = 9 then cur.reverse :: cells bs [] else cells bs (b :: cur)

/-- A file read as rows of tab-separated numbers. -/
def parseCounts (bs : List UInt8) : Option (List (List Nat)) :=
  (lines bs []).mapM fun l => (cells l []).mapM natOf

/-! ## Order statistics by counting -/

/-- The least `v` from `v₀` on, within `f` more steps, with more than `i` entries of `xs` at most
`v`. -/
def kthGo (xs : List Nat) (i : Nat) : Nat → Nat → Nat
  | v, 0 => v
  | v, f + 1 => if i < xs.countP (· ≤ v) then v else kthGo xs i (v + 1) f

/-- Entry `i` of `xs` sorted ascending (`d` past the end), found by counting. -/
def sortedGetD (xs : List Nat) (i d : Nat) : Nat :=
  if i < xs.length then kthGo xs i 0 (xs.foldr max 0) else d

theorem lt_countP_iff : ∀ {s : List Nat} {i : Nat} (v : Nat), s.Pairwise (· ≤ ·) →
    (hi : i < s.length) → (i < s.countP (· ≤ v) ↔ s[i] ≤ v)
  | [], _, _, _, hi => absurd hi (by simp)
  | a :: t, i, v, hs, hi => by
    rw [List.pairwise_cons] at hs
    by_cases ha : a ≤ v
    · simp only [List.countP_cons, ha, decide_true, ↓reduceIte]
      cases i with
      | zero => simpa using ha
      | succ i =>
        simp only [List.getElem_cons_succ, Nat.add_lt_add_iff_right]
        exact lt_countP_iff v hs.2 (by simpa using hi)
    · have h0 : (a :: t).countP (· ≤ v) = 0 := by
        rw [List.countP_eq_zero]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simpa using ha
        · have := hs.1 b hb; simp; omega
      rw [h0]
      cases i with
      | zero => simpa using ha
      | succ i =>
        have := hs.1 _ (List.getElem_mem (l := t) (n := i) (by simpa using hi))
        simp only [List.getElem_cons_succ, Nat.not_lt_zero, false_iff]
        omega

theorem kthGo_eq {xs : List Nat} {i x : Nat} (hx : ∀ v, i < xs.countP (· ≤ v) ↔ x ≤ v) :
    ∀ (f v : Nat), v ≤ x → x ≤ v + f → kthGo xs i v f = x
  | 0, v, h1, h2 => by simp only [kthGo]; omega
  | f + 1, v, h1, h2 => by
    simp only [kthGo]
    split
    · rename_i h; have := (hx v).1 h; omega
    · rename_i h
      exact kthGo_eq hx f (v + 1) (by have := mt (hx v).2 h; omega) (by omega)

theorem le_foldr_max : ∀ {xs : List Nat} {x : Nat}, x ∈ xs → x ≤ xs.foldr max 0
  | [], _, h => absurd h (by simp)
  | a :: t, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max h).trans (le_max_right _ _)

theorem getD_mergeSort (xs : List Nat) (i d : Nat) :
    (xs.mergeSort (· ≤ ·)).getD i d = sortedGetD xs i d := by
  have hp := List.mergeSort_perm xs (fun a b => decide (a ≤ b))
  have hs : (xs.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) :=
    (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) xs).imp
      (by simp)
  unfold sortedGetD
  split
  · rename_i hi
    have hi' : i < (xs.mergeSort (· ≤ ·)).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hi']
    refine (kthGo_eq (fun v => ?_) _ 0 (Nat.zero_le _) ?_).symm
    · rw [← hp.countP_eq]; exact lt_countP_iff v hs hi'
    · simpa using le_foldr_max (hp.subset (List.getElem_mem hi'))
  · rename_i hi
    exact List.getD_eq_default _ _ (by simp; omega)

/-- `quantile7` with its order statistics found by counting. -/
def quantile7N (xs : List Nat) (p : ℚ) : ℚ :=
  let h := ((xs.length - 1 : Nat) : ℚ) * p
  let lo := h.floor.toNat
  sortedGetD xs lo 0 +
    (h - lo) * ((sortedGetD xs (lo + 1) (sortedGetD xs lo 0) : ℚ) - sortedGetD xs lo 0)

theorem quantile7_eq : quantile7 = quantile7N := by
  funext xs p
  simp only [quantile7, quantile7N, getD_mergeSort, List.length_mergeSort]

/-- `f75` by `quantile7N`. -/
def f75N (rows : List (List Nat)) (j : Nat) : ℚ := quantile7N (col rows j) (3 / 4) / lib rows j

theorem f75_eq : f75 = f75N := by
  funext rows j
  simp only [f75, f75N, quantile7_eq]

/-- `tmmRef` by `f75N`. -/
def tmmRefN (rows : List (List Nat)) (k : Nat) : Nat :=
  let mean : ℚ := ((List.range k).map (f75N rows)).sum / k
  (List.range k).foldl (fun b j => if |f75N rows j - mean| < |f75N rows b - mean| then j else b) 0

theorem tmmRef_eq : tmmRef = tmmRefN := by
  funext rows k
  simp only [tmmRef, tmmRefN, f75_eq]

/-- `Profile`, decided with `f75N`. -/
def profileB (rows : List (List Nat)) (k : Nat) : Bool :=
  decide (2 ≤ k) && rows.all (fun r => r.length == k && r.any (0 < ·)) &&
    (List.range k).all fun j => decide (0 < lib rows j) && decide (lib rows j < 2 ^ 53) &&
      decide (1 / 10 ^ 20 ≤ f75N rows j)

theorem profile_of {rows : List (List Nat)} {k : Nat} (h : profileB rows k = true) :
    Profile rows k := by
  unfold profileB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨hk, hrows⟩, hcols⟩ := h
  refine ⟨hk, fun r hr => ?_, fun j hj => ?_⟩
  · have := hrows r hr
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at this
    exact this
  · have := hcols j (List.mem_range.mpr hj)
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq] at this
    rw [f75_eq]
    exact ⟨this.1.1, this.1.2, this.2⟩

/-- edgeR's A cutoff (`Acutoff = -1e10`) drops no gene of a `Profile` matrix: a counted gene's
`A = (log₂ (o / nO) + log₂ (r / nR)) / 2` is at least −53 when both libraries are below 2⁵³
reads. -/
theorem acutoff_inactive {nO nR : Nat} (hO : nO < 2 ^ 53) (hR : nR < 2 ^ 53) {x : Nat × Nat}
    (hx1 : 0 < x.1) (hx2 : 0 < x.2) :
    -10 ^ 10 < (Real.logb 2 (x.1 / nO) + Real.logb 2 (x.2 / nR)) / 2 := by
  have hlow : ∀ (c n : Nat), 0 < c → n < 2 ^ 53 → (-53 : ℝ) ≤ Real.logb 2 (c / n) := by
    intro c n hc hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hq : (1 : ℝ) / 2 ^ 53 ≤ c / n := by
      rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hn0)]
      have : (n : ℝ) < 2 ^ 53 := by exact_mod_cast hn
      have : (1 : ℝ) ≤ c := by exact_mod_cast hc
      nlinarith
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hq
    rw [one_div, Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    norm_num at this
    exact this
  have := hlow _ _ hx1 hO
  have := hlow _ _ hx2 hR
  linarith

/-! ## Ranks by cross products -/

/-- `tmmKeep` in natural numbers: doubled average ranks, M compared by cross products, A by
products (the library sizes cancel). -/
def keepN (obs ref : List Nat) : List (Nat × Nat) :=
  let g := tmmGenes obs ref
  let n := g.length
  let loL := n * 3 / 10 + 1
  let loS := n / 20 + 1
  g.filter fun x =>
    let m := 2 * g.countP (fun y => y.1 * x.2 < x.1 * y.2) +
      g.countP (fun y => y.1 * x.2 = x.1 * y.2) + 1
    let a := 2 * g.countP (fun y => y.1 * y.2 < x.1 * x.2) +
      g.countP (fun y => y.1 * y.2 = x.1 * x.2) + 1
    decide (2 * loL ≤ m ∧ m ≤ 2 * (n + 1 - loL) ∧ 2 * loS ≤ a ∧ a ≤ 2 * (n + 1 - loS))

theorem pos_of_mem_genes {obs ref : List Nat} {x : Nat × Nat} (h : x ∈ tmmGenes obs ref) :
    0 < x.1 ∧ 0 < x.2 := by
  simpa [tmmGenes] using (List.mem_filter.mp h).2

theorem tmmM_lt_iff {nO nR : Nat} (hO : 0 < nO) (hR : 0 < nR) {x y : Nat × Nat} (hx : 0 < x.2)
    (hy : 0 < y.2) : tmmM nO nR y < tmmM nO nR x ↔ y.1 * x.2 < x.1 * y.2 := by
  unfold tmmM
  rw [div_lt_div_iff₀ (by positivity) (by positivity), ← Nat.cast_lt (α := ℚ)]
  push_cast
  constructor <;> intro h
  · have : (0 : ℚ) < nR * nO := by positivity
    nlinarith
  · nlinarith [mul_lt_mul_of_pos_left h (by positivity : (0 : ℚ) < nR * nO)]

theorem tmmM_eq_iff {nO nR : Nat} (hO : 0 < nO) (hR : 0 < nR) {x y : Nat × Nat} (hx : 0 < x.2)
    (hy : 0 < y.2) : tmmM nO nR y = tmmM nO nR x ↔ y.1 * x.2 = x.1 * y.2 := by
  unfold tmmM
  rw [div_eq_div_iff (by positivity) (by positivity), ← Nat.cast_inj (R := ℚ)]
  push_cast
  constructor <;> intro h
  · have h0 : (nR * nO : ℚ) ≠ 0 := by positivity
    have : (nR * nO : ℚ) * (y.1 * x.2) = (nR * nO) * (x.1 * y.2) := by linear_combination h
    exact mul_left_cancel₀ h0 this
  · linear_combination (nR * nO : ℚ) * h

theorem tmmA_lt_iff {nO nR : Nat} (hO : 0 < nO) (hR : 0 < nR) (x y : Nat × Nat) :
    tmmA nO nR y < tmmA nO nR x ↔ y.1 * y.2 < x.1 * x.2 := by
  unfold tmmA
  rw [div_lt_div_iff_of_pos_right (by positivity), ← Nat.cast_lt (α := ℚ)]
  push_cast; rfl

theorem tmmA_eq_iff {nO nR : Nat} (hO : 0 < nO) (hR : 0 < nR) (x y : Nat × Nat) :
    tmmA nO nR y = tmmA nO nR x ↔ y.1 * y.2 = x.1 * x.2 := by
  unfold tmmA
  rw [div_left_inj' (by positivity), ← Nat.cast_inj (R := ℚ)]
  push_cast; rfl

theorem avgRank_map {g : List (Nat × Nat)} {f : Nat × Nat → ℚ} {x : Nat × Nat}
    {lt eq : Nat × Nat → Bool} (hlt : ∀ y ∈ g, f y < f x ↔ lt y) (heq : ∀ y ∈ g, f y = f x ↔ eq y) :
    avgRank (g.map f) (f x) = (g.countP lt : ℚ) + ((g.countP eq : ℚ) + 1) / 2 := by
  unfold avgRank
  have h1 : g.countP ((fun y => decide (y < f x)) ∘ f) = g.countP lt :=
    List.countP_congr fun y hy => by simpa using hlt y hy
  have h2 : g.countP ((fun y => decide (y = f x)) ∘ f) = g.countP eq :=
    List.countP_congr fun y hy => by simpa using heq y hy
  rw [List.filter_map, List.filter_map, List.length_map, List.length_map,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter, h1, h2]

theorem rank_lo_iff (lo c e : Nat) :
    (lo : ℚ) ≤ c + (e + 1) / 2 ↔ 2 * lo ≤ 2 * c + e + 1 := by
  rw [← Nat.cast_le (α := ℚ)]; push_cast; constructor <;> intro h <;> linarith

theorem rank_hi_iff (hi c e : Nat) :
    (c : ℚ) + (e + 1) / 2 ≤ hi ↔ 2 * c + e + 1 ≤ 2 * hi := by
  rw [← Nat.cast_le (α := ℚ)]; push_cast; constructor <;> intro h <;> linarith

theorem trim_floor (n d : Nat) : (⌊(n : ℚ) * d / 10⌋ : ℚ) + 1 = ((n * d / 10 + 1 : Nat) : ℚ) := by
  rw [show (n : ℚ) * d / 10 = ((n * d : Nat) : ℚ) / ((10 : Nat) : ℚ) by push_cast; ring,
    Rat.floor_natCast_div_natCast]
  push_cast; rfl

theorem tmmKeep_eq {obs ref : List Nat} {nO nR : Nat} (hO : 0 < nO) (hR : 0 < nR) :
    tmmKeep obs ref nO nR = keepN obs ref := by
  unfold tmmKeep keepN
  simp only
  apply List.filter_congr
  intro x hx
  have hx2 := (pos_of_mem_genes hx).2
  set g := tmmGenes obs ref
  rw [avgRank_map (lt := fun y => decide (y.1 * x.2 < x.1 * y.2))
      (eq := fun y => decide (y.1 * x.2 = x.1 * y.2))
      (fun y hy => by simpa using tmmM_lt_iff hO hR hx2 (pos_of_mem_genes hy).2)
      (fun y hy => by simpa using tmmM_eq_iff hO hR hx2 (pos_of_mem_genes hy).2),
    avgRank_map (lt := fun y => decide (y.1 * y.2 < x.1 * x.2))
      (eq := fun y => decide (y.1 * y.2 = x.1 * x.2))
      (fun y _ => by simpa using tmmA_lt_iff hO hR x y)
      (fun y _ => by simpa using tmmA_eq_iff hO hR x y)]
  have hL : (⌊(g.length : ℚ) * 3 / 10⌋ : ℚ) + 1 = ((g.length * 3 / 10 + 1 : Nat) : ℚ) :=
    trim_floor _ 3
  have hS : (⌊(g.length : ℚ) / 20⌋ : ℚ) + 1 = ((g.length / 20 + 1 : Nat) : ℚ) := by
    rw [show (g.length : ℚ) / 20 = ((g.length : Nat) : ℚ) / ((20 : Nat) : ℚ) by push_cast; ring,
      Rat.floor_natCast_div_natCast]
    push_cast; rfl
  have hLs : (g.length : ℚ) + 1 - ((g.length * 3 / 10 + 1 : Nat) : ℚ) =
      ((g.length + 1 - (g.length * 3 / 10 + 1) : Nat) : ℚ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hSs : (g.length : ℚ) + 1 - ((g.length / 20 + 1 : Nat) : ℚ) =
      ((g.length + 1 - (g.length / 20 + 1) : Nat) : ℚ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hL, hS, hLs, hSs]
  simp only [rank_lo_iff, rank_hi_iff]

/-! ## Logarithm bounds -/

/-- `Σ_{i<n} x^(i+1)/(i+1)`, the series of `-log (1 - x)`. -/
def logSum (x : ℚ) (n : Nat) : ℚ :=
  ((List.range n).map fun (i : Nat) => x ^ (i + 1) / (i + 1 : ℚ)).sum

/-- The series' remainder bound `|x|^(n+1)/(1 - |x|)`. -/
def logRem (x : ℚ) (n : Nat) : ℚ := |x| ^ (n + 1) / (1 - |x|)

/-- A lower bound on `log q` from `n` series terms. -/
def lnLo (q : ℚ) (n : Nat) : ℚ := -logSum (1 - q) n - logRem (1 - q) n

/-- An upper bound on `log q` from `n` series terms. -/
def lnHi (q : ℚ) (n : Nat) : ℚ := -logSum (1 - q) n + logRem (1 - q) n

theorem logSum_cast (x : ℚ) (n : Nat) :
    ((logSum x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [logSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [logSum, List.range_succ, List.sum_append]

theorem log_bounds (q : ℚ) (n : Nat) (h : |1 - q| < 1) :
    (lnLo q n : ℝ) ≤ Real.log q ∧ Real.log q ≤ lnHi q n := by
  have hx : |((1 - q : ℚ) : ℝ)| < 1 := by exact_mod_cast h
  have key := Real.abs_log_sub_add_sum_range_le hx n
  rw [← logSum_cast] at key
  have h1 : (1 : ℝ) - ((1 - q : ℚ) : ℝ) = q := by push_cast; ring
  rw [h1] at key
  constructor
  · have := (abs_le.mp key).1
    simp only [lnLo, logRem]; push_cast at this ⊢; linarith
  · have := (abs_le.mp key).2
    simp only [lnHi, logRem]; push_cast at this ⊢; linarith

/-! ## The ratio witness -/

theorem cast_sum_map {α : Type} (l : List α) (f : α → ℚ) :
    ((l.map f).sum : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  rw [Rat.cast_list_sum, List.map_map]; rfl

theorem eq_of_mem_zip_self {α : Type} : ∀ {l : List α} {x : α × α}, x ∈ l.zip l → x.1 = x.2
  | [], _, h => absurd h (by simp)
  | a :: t, x, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact eq_of_mem_zip_self h

/-- The reference sample against itself: every ratio is 1, so the log factor is 0. -/
theorem tmmLog2_self (xs : List Nat) (n : Nat) (hn : 0 < n) : tmmLog2 xs xs n n = 0 := by
  unfold tmmLog2
  split
  · rfl
  rename_i hne
  refine absurd (fun x hx => ?_) hne
  have hx' := pos_of_mem_genes hx
  have h12 := eq_of_mem_zip_self (List.mem_filter.mp hx).1
  have h2 : (x.2 : ℚ) ≠ 0 := by exact_mod_cast hx'.2.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : tmmM n n x = 1 := by
    unfold tmmM; rw [h12]; field_simp
  rw [this]; norm_num

/-- Accuracy of the exact factors at relative `ε` bounds sample `j`'s ratio to the reference
`r`, `2 ^ l j`, by the file's ratio widened by `(1 + ε) / (1 - ε)`. -/
theorem ratio_bound {k j r : Nat} {l : Nat → ℝ} {c : ℝ} {ys : List ℚ} {ε : ℚ} (hj : j < k)
    (hr : r < k) (hl0 : l r = 0) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hw : WithinRel ε ((List.range k).map fun i => (2 : ℝ) ^ (l i - c)) ys) :
    (2 : ℝ) ^ l j ≤ ((ys.getD j 0 / ys.getD r 0 * ((1 + ε) / (1 - ε)) : ℚ) : ℝ) := by
  obtain ⟨hlen, hall⟩ := hw
  simp only [List.length_map, List.length_range] at hlen
  have hmem : ∀ i (hi : i < k), ((2 : ℝ) ^ (l i - c), ys.getD i 0) ∈
      ((List.range k).map fun i => (2 : ℝ) ^ (l i - c)).zip ys := by
    intro i hi
    have hz : i < (((List.range k).map fun i => (2 : ℝ) ^ (l i - c)).zip ys).length := by
      simp [hlen, hi]
    have := List.getElem_mem hz
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range] at this
    rw [List.getD_eq_getElem _ _ (hlen ▸ hi : i < ys.length)]
    exact this
  have hj' := abs_le.mp (hall _ (hmem j hj))
  have hr' := abs_le.mp (hall _ (hmem r hr))
  simp only at hj' hr'
  set yj : ℝ := ((ys.getD j 0 : ℚ) : ℝ)
  set yr : ℝ := ((ys.getD r 0 : ℚ) : ℝ)
  set xr : ℝ := (2 : ℝ) ^ (l r - c)
  have hxr : 0 < xr := Real.rpow_pos_of_pos (by norm_num) _
  have hxj : (2 : ℝ) ^ (l j - c) = (2 : ℝ) ^ l j * xr := by
    rw [← Real.rpow_add (by norm_num), hl0]; ring_nf
  rw [hxj] at hj'
  have ha : 0 < (2 : ℝ) ^ l j := Real.rpow_pos_of_pos (by norm_num) _
  have hεr : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hε0 : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hyr : 0 < yr := by nlinarith
  have h1 : (1 - (ε : ℝ)) * ((2 : ℝ) ^ l j * xr) ≤ yj := by linarith
  have h2 : yr ≤ (1 + (ε : ℝ)) * xr := by linarith
  push_cast
  rw [div_mul_div_comm, le_div_iff₀ (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by nlinarith : 0 ≤ (2 : ℝ) ^ l j * (1 - ε)),
    mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + ε)]

/-- Sample `j` against reference `r` refutes accuracy at relative `ε`: some gene's ratio is at most
1/2 or at least 2 (edgeR's near-identity shortcut is off), the kept genes' variances are positive
and their ratios within the log series' range, and the weighted log ratio's lower bound from `N`
series terms exceeds the upper bound on the log of the file's widened ratio. -/
def ratioRefutes (rows : List (List Nat)) (ys : List ℚ) (j r N : Nat) (ε : ℚ) : Bool :=
  let nO := lib rows j
  let nR := lib rows r
  let K := keepN (col rows j) (col rows r)
  let T := ys.getD j 0 / ys.getD r 0 * ((1 + ε) / (1 - ε))
  let S := (K.map fun x => lnLo (tmmM nO nR x) N / tmmV nO nR x).sum
  let D := (K.map fun x => 1 / tmmV nO nR x).sum
  (tmmGenes (col rows j) (col rows r)).any (fun x => 2 * x.1 * nR ≤ x.2 * nO ||
      2 * x.2 * nO ≤ x.1 * nR) &&
    K.all (fun x => decide (0 < tmmV nO nR x) && decide (|1 - tmmM nO nR x| < 1)) &&
    decide (0 < D) && decide (|1 - T| < 1) && decide (lnHi T N < S / D)

theorem shortcut_off {nO nR : Nat} (hO : 0 < nO) (hR : 0 < nR) {x : Nat × Nat} (hx1 : 0 < x.1)
    (hx2 : 0 < x.2) (h : 2 * x.1 * nR ≤ x.2 * nO ∨ 2 * x.2 * nO ≤ x.1 * nR) :
    ¬ |Real.logb 2 (tmmM nO nR x)| < 1 / 10 ^ 6 := by
  have hpos : (0 : ℝ) < (tmmM nO nR x : ℚ) := by unfold tmmM; push_cast; positivity
  rw [not_lt]
  rcases h with h | h
  · have hq : ((tmmM nO nR x : ℚ) : ℝ) ≤ 1 / 2 := by
      unfold tmmM; push_cast
      rw [div_le_iff₀ (by positivity)]
      have : (2 * x.1 * nR : ℝ) ≤ x.2 * nO := by exact_mod_cast h
      linarith
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hq
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at this
    rw [abs_of_neg (by linarith)]; norm_num; linarith
  · have hq : (2 : ℝ) ≤ ((tmmM nO nR x : ℚ) : ℝ) := by
      unfold tmmM; push_cast
      rw [le_div_iff₀ (by positivity)]
      have : (2 * x.2 * nO : ℝ) ≤ x.1 * nR := by exact_mod_cast h
      linarith
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hq
    rw [Real.logb_self_eq_one (by norm_num)] at this
    rw [abs_of_pos (by linarith)]; norm_num; linarith

theorem not_within_of_ratioRefutes {rows : List (List Nat)} {k j N : Nat} {ys : List ℚ} {ε : ℚ}
    (hP : Profile rows k) (hj : j < k) (hr : tmmRef rows k < k) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (h : ratioRefutes rows ys j (tmmRef rows k) N ε = true) :
    ¬ WithinRel ε (exactTMM rows k) ys := by
  intro hw
  set r := tmmRef rows k with hrdef
  have hO : 0 < lib rows j := (hP.2.2 j hj).1
  have hR : 0 < lib rows r := (hP.2.2 r hr).1
  set l : Nat → ℝ := fun i => tmmLog2 (col rows i) (col rows r) (lib rows i) (lib rows r)
    with hl
  have hl0 : l r = 0 := tmmLog2_self _ _ hR
  have hb := ratio_bound (l := l) hj hr hl0 hε hε1 hw
  simp only [ratioRefutes, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨x, hxg, hx⟩, hK⟩, hD⟩, hT⟩, hsep⟩ := h
  set nO := lib rows j
  set nR := lib rows r
  set K := keepN (col rows j) (col rows r)
  set T := ys.getD j 0 / ys.getD r 0 * ((1 + ε) / (1 - ε))
  -- the shortcut is off, so `l j` is the weighted mean over the kept genes
  have hxp := pos_of_mem_genes hxg
  have hlj : l j = (K.map fun x => Real.logb 2 (tmmM nO nR x) / tmmV nO nR x).sum /
      (K.map fun x => (1 / tmmV nO nR x : ℝ)).sum := by
    simp only [hl, tmmLog2]
    split
    · rename_i hall
      exact absurd (hall x hxg) (shortcut_off hO hR hxp.1 hxp.2 (by simpa using hx))
    · rw [tmmKeep_eq hO hR]
  -- the weighted mean of natural logs is at least the series' lower bound
  have hD' : (0 : ℝ) < (K.map fun x => (1 / tmmV nO nR x : ℝ)).sum := by
    have : ((K.map fun x => 1 / tmmV nO nR x).sum : ℝ) =
        (K.map fun x => (1 / tmmV nO nR x : ℝ)).sum := by
      rw [cast_sum_map]; simp
    rw [← this]; exact_mod_cast hD
  have hlow : (((K.map fun x => lnLo (tmmM nO nR x) N / tmmV nO nR x).sum /
      (K.map fun x => 1 / tmmV nO nR x).sum : ℚ) : ℝ) ≤ Real.log 2 * l j := by
    rw [Rat.cast_div, cast_sum_map, cast_sum_map, hlj, mul_div_assoc']
    have hD2 : (K.map fun x => ((1 / tmmV nO nR x : ℚ) : ℝ)).sum =
        (K.map fun x => (1 / tmmV nO nR x : ℝ)).sum := by simp
    rw [hD2]
    refine div_le_div_of_nonneg_right ?_ hD'.le
    · rw [← List.sum_map_mul_left]
      apply List.sum_le_sum
      intro y hy
      obtain ⟨hv, hq⟩ := hK y hy
      have hv' : (0 : ℝ) < (tmmV nO nR y : ℚ) := by exact_mod_cast hv
      have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
      have heq : Real.log 2 * (Real.logb 2 (tmmM nO nR y : ℚ) / ((tmmV nO nR y : ℚ) : ℝ)) =
          Real.log (tmmM nO nR y : ℚ) / ((tmmV nO nR y : ℚ) : ℝ) := by
        rw [← Real.log_div_log]; field_simp
      rw [heq, Rat.cast_div]
      exact div_le_div_of_nonneg_right (log_bounds _ N hq).1 hv'.le
  -- the exact ratio's log is at most the series' upper bound on the widened file ratio's log
  have hTpos : (0 : ℝ) < (T : ℚ) := by
    have : 0 < T := by have := abs_lt.mp hT; linarith
    exact_mod_cast this
  have hup : Real.log 2 * l j ≤ (lnHi T N : ℝ) := by
    have : Real.log 2 * l j ≤ Real.log (T : ℚ) := by
      rw [Real.le_log_iff_exp_le hTpos, ← Real.rpow_def_of_pos (by norm_num)]
      exact hb
    exact this.trans (log_bounds T N hT).2
  have := hlow.trans hup
  exact absurd (by exact_mod_cast this) (not_le.mpr hsep)

/-! ## The checker -/

/-- The input is a `Profile` count matrix with `k` samples and the output a decimal file of `k`
lines, and sample `j` against the reference refutes accuracy at relative `1/1000` with `N`
series terms (`ratioRefutes`). -/
def RefutesExactAverageTMM.checkWith (j N : Nat) (i o : Blob) : Bool :=
  match parseCounts i.data, parseDec o.data with
  | some rows, some xs =>
    let k := (rows.headD []).length
    let r := tmmRefN rows k
    countsText rows == i.data && decFile xs == o.data && profileB rows k && decide (j < k) &&
      decide (r < k) && ratioRefutes rows (xs.map decVal) j r N (1 / 1000)
  | _, _ => false

/-- The checker `fva certify` calls: sample 3 (index 2) against the reference, 8 series terms. -/
def RefutesExactAverageTMM.check : Blob → Blob → Bool := RefutesExactAverageTMM.checkWith 2 8

theorem RefutesExactAverageTMM.checkWith_sound (j N : Nat) (i o : Blob)
    (h : RefutesExactAverageTMM.checkWith j N i o = true) :
    Accepted RefutesExactAverageTMM i o := by
  unfold RefutesExactAverageTMM.checkWith at h
  split at h
  · rename_i rows xs _ _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hi, ho⟩, hP⟩, hj⟩, hr⟩, hR⟩ := h
    rw [← tmmRef_eq] at hr hR
    have hP' := profile_of hP
    refine ⟨⟨rows, _, xs, hi.symm, hP', ho.symm⟩, fun rows' k' xs' hi' hP2 ho' => ?_⟩
    obtain rfl := countsText_inj (hi.trans hi')
    obtain rfl := decFile_inj (ho.trans ho')
    -- `k` is the rows' length: the profile has a positive library, so a row
    have hk : k' = (rows.headD []).length := by
      cases rows with
      | nil => exact absurd (hP2.2.2 0 (by have := hP2.1; omega)).1 (by simp [lib, col])
      | cons r rs => exact ((hP2.2.1 r (by simp)).1).symm
    subst hk
    exact not_within_of_ratioRefutes hP' hj hr (by norm_num) (by norm_num) hR
  · simp at h

theorem RefutesExactAverageTMM.check_sound (i o : Blob)
    (h : RefutesExactAverageTMM.check i o = true) : Accepted RefutesExactAverageTMM i o :=
  RefutesExactAverageTMM.checkWith_sound 2 8 i o h

end Subjects.Tmm
