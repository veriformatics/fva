import Proofs.Data
import Proofs.Logs

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TMM

abbrev Pair := ℕ × ℕ

def eligible (i : ℕ) : List Pair :=
  (counts.map fun r => (r[i]!, r[3]!)).filter fun p => p.1 > 0 && p.2 > 0

def rankM2 (ps : List Pair) (p : Pair) : ℕ :=
  2 * (ps.filter fun q => q.1*p.2 < p.1*q.2).length +
      (ps.filter fun q => q.1*p.2 == p.1*q.2).length + 1

def rankA2 (ps : List Pair) (p : Pair) : ℕ :=
  2 * (ps.filter fun q => q.1*q.2 < p.1*p.2).length +
      (ps.filter fun q => q.1*q.2 == p.1*p.2).length + 1

def trimmed (i : ℕ) : List Pair :=
  let ps := eligible i
  let n := ps.length
  ps.filter fun p =>
    2*(n*3/10+1) ≤ rankM2 ps p && rankM2 ps p ≤ 2*(n-n*3/10) &&
    2*(n/20+1) ≤ rankA2 ps p && rankA2 ps p ≤ 2*(n-n/20)

def pairsOfMask (masks : List (List ℕ)) (i : ℕ) : List Pair :=
  (masks[i]!).map fun k => ((counts[k]!)[i]!, (counts[k]!)[3]!)

-- R's type-7 75th percentile: zero-based position (454-1)*3/4 = 339.75.
def quartile (i : ℕ) : ℚ :=
  let ys := (counts.map fun r => r[i]!).mergeSort (· ≤ ·)
  ((ys[339]! : ℚ) + 3*(ys[340]! : ℚ))/4/(libs[i]! : ℚ)
def quartileMean : ℚ := ((List.range 7).map quartile).sum/7

theorem default_reference :
    ∀ i ∈ List.range 7, i ≠ 3 → |quartile 3-quartileMean| < |quartile i-quartileMean| := by
  native_decide

theorem exact_trimming : ∀ i ∈ List.range 7, pairsOfMask idealMasks i = trimmed i := by
  native_decide

-- Natural-log TMM. The log(2) in the M values cancels with base-2 exponentiation.
def weight (i : ℕ) (p : Pair) : ℚ :=
  1 / (((libs[i]! : ℚ) - p.1)/((libs[i]! : ℚ)*p.1) +
       ((libs[3]! : ℚ) - p.2)/((libs[3]! : ℚ)*p.2))

noncomputable def logRatio (i : ℕ) (p : Pair) : ℝ :=
  Real.log p.1 - Real.log p.2 - (Real.log (libs[i]!) - Real.log (libs[3]!))

noncomputable def raw (ps : List Pair) (i : ℕ) : ℝ :=
  (ps.map (fun p => (weight i p : ℝ)*logRatio i p)).sum /
  (ps.map (fun p => (weight i p : ℝ))).sum

noncomputable def centered (masks : List (List ℕ)) (i : ℕ) : ℝ :=
  raw (pairsOfMask masks i) i -
  ((List.range 7).map (fun j => raw (pairsOfMask masks j) j)).sum/7

noncomputable def factor (masks : List (List ℕ)) (i : ℕ) : ℝ :=
  Real.exp (centered masks i)

-- Round weight bounds outward on a fixed decimal grid to keep computations small.
def weightBox (i : ℕ) (p : Pair) : Box :=
  let low : ℚ := (⌊weight i p * 10^18⌋ : ℤ) / (10^18 : ℚ)
  ⟨low, low+1/(10^18 : ℚ)⟩
def ratioBox (i : ℕ) (p : Pair) : Box :=
  ((logBox p.1).sub (logBox p.2)).sub ((logBox (libs[i]!)).sub (logBox (libs[3]!)))
def sumBox : List Box → Box
  | [] => Box.point 0
  | b::bs => b.add (sumBox bs)
def numBox (ps : List Pair) (i : ℕ) : Box :=
  sumBox (ps.map fun p => (weightBox i p).mul (ratioBox i p))
def denBox (ps : List Pair) (i : ℕ) : Box :=
  sumBox (ps.map fun p => weightBox i p)
def rawBox (ps : List Pair) (i : ℕ) : Box := (numBox ps i).div (denBox ps i)
def centerBox (masks : List (List ℕ)) (i : ℕ) : Box :=
  (rawBox (pairsOfMask masks i) i).sub
    ((sumBox ((List.range 7).map fun j => rawBox (pairsOfMask masks j) j)).div (Box.point 7))

def validPairs (ps : List Pair) (i : ℕ) : Prop :=
  libs[i]! ∈ logKeys ∧ libs[3]! ∈ logKeys ∧ 0 < (denBox ps i).lo ∧
  ∀ p ∈ ps, p.1 ∈ logKeys ∧ p.2 ∈ logKeys ∧
    (weightBox i p).lo ≤ weight i p ∧ weight i p ≤ (weightBox i p).hi
instance (ps : List Pair) (i : ℕ) : Decidable (validPairs ps i) := by
  unfold validPairs
  infer_instance

theorem sumBox_sound (bs : List Box) (xs : List ℝ)
    (h : List.Forall₂ Box.Holds bs xs) : (sumBox bs).Holds xs.sum := by
  induction h with
  | nil => simpa only [sumBox,List.sum_nil,Rat.cast_zero] using point_sound 0
  | cons h hs ih => exact add_sound h ih

theorem rawBox_sound (ps : List Pair) (i : ℕ) (h : validPairs ps i) :
    (rawBox ps i).Holds (raw ps i) := by
  have hr : ∀ p ∈ ps, (ratioBox i p).Holds (logRatio i p) := by
    intro p hp
    exact sub_sound (sub_sound (logBox_sound (h.2.2.2 p hp).1)
      (logBox_sound (h.2.2.2 p hp).2.1))
      (sub_sound (logBox_sound h.1) (logBox_sound h.2.1))
  have hw : ∀ p ∈ ps, (weightBox i p).Holds (weight i p : ℝ) := by
    intro p hp
    constructor
    · exact_mod_cast (h.2.2.2 p hp).2.2.1
    · exact_mod_cast (h.2.2.2 p hp).2.2.2
  apply div_sound _ _ h.2.2.1
  · apply sumBox_sound
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro p hp
    exact mul_sound (hw p hp) (hr p hp)
  · apply sumBox_sound
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    exact hw

theorem centerBox_sound (masks : List (List ℕ))
    (h : ∀ i ∈ List.range 7, validPairs (pairsOfMask masks i) i)
    (i : ℕ) (hi : i ∈ List.range 7) :
    (centerBox masks i).Holds (centered masks i) := by
  apply sub_sound (rawBox_sound _ _ (h i hi))
  apply div_sound _ (point_sound 7) (by norm_num [Box.point])
  apply sumBox_sound
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro j hj
  exact rawBox_sound _ _ (h j hj)

theorem exp_enclosure {a : Box} {x : ℝ} {lo hi : ℚ} {ll lh : Box}
    (hx : a.Holds x) (hl : ll.Holds (Real.log (lo:ℝ)))
    (hh : lh.Holds (Real.log (hi:ℝ))) (plo : 0 < lo) (phi : 0 < hi)
    (cl : ll.hi ≤ a.lo) (ch : a.hi ≤ lh.lo) :
    (lo:ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (hi:ℝ) := by
  have plo' : (0:ℝ) < lo := by exact_mod_cast plo
  have phi' : (0:ℝ) < hi := by exact_mod_cast phi
  have cl' : (ll.hi:ℝ) ≤ a.lo := by exact_mod_cast cl
  have ch' : (a.hi:ℝ) ≤ lh.lo := by exact_mod_cast ch
  exact ⟨(Real.log_le_iff_le_exp plo').mp (hl.2.trans (cl'.trans hx.1)),
    (Real.le_log_iff_exp_le phi').mp (hx.2.trans (ch'.trans hh.1))⟩
def centerSummary (bs : ℕ → Box) (i : ℕ) : Box :=
  (bs i).sub ((sumBox ((List.range 7).map bs)).div (Box.point 7))

theorem center_summary_sound (masks : List (List ℕ)) (bs : ℕ → Box)
    (h : ∀ i ∈ List.range 7, (bs i).Holds (raw (pairsOfMask masks i) i))
    (i : ℕ) (hi : i ∈ List.range 7) :
    (centerSummary bs i).Holds (centered masks i) := by
  apply sub_sound (h i hi)
  apply div_sound _ (point_sound 7) (by norm_num [Box.point])
  apply sumBox_sound
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  exact h
end TMM
