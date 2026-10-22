import FVA.Proof.Numerics.AdequacyLemmas

/-!
# Adequacy of the float spec (contract D4)

Bit patterns and values correspond one to one; rounding is total, functional and well-formed;
NaN sets are nonempty sets of well-formed NaNs; every operator's result set outside its NaN cases
holds at most one value.
-/

namespace FVA.Wasm.Num

open FVal

variable {F : FloatFormat}

theorem ofBits_wf (hF : F.Sane) (b : BitVec F.N) : (ofBits F b).WF F := by
  obtain ⟨hs, hp⟩ := Adequacy.exponent_span hF
  have hm := Nat.mod_lt b.toNat (Nat.two_pow_pos F.M)
  have he := Nat.mod_lt (b.toNat / 2 ^ F.M) (Nat.two_pow_pos F.E)
  unfold ofBits
  dsimp only
  split
  · split
    · trivial
    · exact ⟨by omega, hm⟩
  · split
    · exact hm
    · exact ⟨hm, by omega, by omega⟩

theorem fbits_ofBits (hF : F.Sane) (b : BitVec F.N) : fbits F (ofBits F b) = b := by
  cases hF
  have hb : BitVec.ofNat F.N
      ((if decide (2 ^ (F.E + F.M) ≤ b.toNat) then 2 ^ (F.E + F.M) else 0) +
        (b.toNat / 2 ^ F.M % 2 ^ F.E) * 2 ^ F.M + b.toNat % 2 ^ F.M) = b := by
    rw [Adequacy.float_reassemble]
    simp
  unfold ofBits
  dsimp only
  split
  · rename_i he
    split
    · rename_i hm
      simpa only [fbits, he, hm, Nat.add_zero] using hb
    · simpa only [fbits, he] using hb
  · split
    · rename_i he
      simpa only [fbits, he, Nat.zero_mul, Nat.add_zero] using hb
    · simpa only [fbits, sub_add_cancel, Int.toNat_natCast] using hb

theorem ofBits_fbits (hF : F.Sane) {z : FVal} (hz : z.WF F) : ofBits F (fbits F z) = z := by
  have hQ : 1 < 2 ^ F.E := Nat.one_lt_two_pow (by have := hF.hE; omega)
  cases z with
  | normal s m e =>
    obtain ⟨hl, hu⟩ := Adequacy.exponent_field_bounds hF hz.2.1 hz.2.2
    have hb := Adequacy.float_layout s (by omega : (e + F.emax).toNat < 2 ^ F.E) hz.1
    unfold fbits ofBits
    rw [hb.1, hb.2.1, hb.2.2]
    have hmax : (e + F.emax).toNat ≠ 2 ^ F.E - 1 := by omega
    have hzero : (e + F.emax).toNat ≠ 0 := by omega
    simp only [hmax, hzero, ↓reduceIte]
    congr 1
    have he : 0 ≤ e + F.emax := by
      have hs := (Adequacy.exponent_span hF).1
      omega
    rw [Int.toNat_of_nonneg he]
    omega
  | subnormal s m =>
    have hb := Adequacy.float_layout s (Nat.two_pow_pos F.E) hz
    simp only [Nat.zero_mul, Nat.add_zero] at hb
    unfold fbits ofBits
    rw [hb.1, hb.2.1, hb.2.2]
    have hmax : 0 ≠ 2 ^ F.E - 1 := by omega
    simp only [hmax, ↓reduceIte]
  | inf s =>
    have hb := Adequacy.float_layout s (by omega : 2 ^ F.E - 1 < 2 ^ F.E)
      (Nat.two_pow_pos F.M)
    simp only [Nat.add_zero] at hb
    unfold fbits ofBits
    rw [hb.1, hb.2.1, hb.2.2]
    simp only [↓reduceIte]
  | nan s n =>
    have hb := Adequacy.float_layout s (by omega : 2 ^ F.E - 1 < 2 ^ F.E) hz.2
    unfold fbits ofBits
    rw [hb.1, hb.2.1, hb.2.2]
    have hn : n ≠ 0 := by have := hz.1; omega
    simp only [hn, ↓reduceIte]

theorem ieee_total (hF : F.Sane) (r : ℝ) : ∃ v, Ieee F r v :=
  ⟨gridRound F r, (ieee_iff_grid hF r _).2 rfl⟩

theorem ieee_functional (hF : F.Sane) {r : ℝ} {v w : FVal} (hv : Ieee F r v) (hw : Ieee F r w) :
    v = w :=
  ((ieee_iff_grid hF r v).1 hv).trans ((ieee_iff_grid hF r w).1 hw).symm

theorem ieee_wf (hF : F.Sane) {r : ℝ} {v : FVal} (hv : Ieee F r v) : v.WF F := by
  cases hF
  rcases hv with ⟨_, rfl⟩ | ⟨_, _, hw, _, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨a, b, _, _, _, hc⟩
  · exact Nat.two_pow_pos _
  · exact hw
  · trivial
  · trivial
  · rcases hc with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, _, hv⟩ | ⟨_, _, hv⟩ <;>
      exact Adequacy.rectify_wf hv

theorem nans_nonempty (hF : F.Sane) (zs : List FVal) : (nans F zs).Nonempty := by
  refine ⟨nan false F.canon, ?_⟩
  unfold nans
  split
  · exact ⟨false, rfl⟩
  · exact ⟨false, F.canon, rfl, le_rfl, (Adequacy.canon_bounds hF).2⟩

theorem nans_wf (hF : F.Sane) {zs : List FVal} {v : FVal} (hv : v ∈ nans F zs) :
    v.WF F ∧ v.IsNaN := by
  refine ⟨?_, Adequacy.nans_isNaN hv⟩
  unfold nans at hv
  split at hv
  · rcases hv with ⟨s, rfl⟩
    exact Adequacy.canon_bounds hF
  · rcases hv with ⟨s, n, rfl, hl, hu⟩
    exact ⟨(Adequacy.canon_bounds hF).1.trans hl, hu⟩

/-- A result set holds at most one non-NaN value. -/
def Det (S : Set FVal) : Prop := ∀ v ∈ S, ∀ w ∈ S, ¬ v.IsNaN → v = w

private theorem det_singleton (z : FVal) : Det {z} := by
  intro v hv w hw _
  exact (Set.mem_singleton_iff.1 hv).trans (Set.mem_singleton_iff.1 hw).symm

private theorem det_nans (zs : List FVal) : Det (nans F zs) := by
  intro v hv _ _ hn
  exact (hn (Adequacy.nans_isNaN hv)).elim

private theorem det_ieee (hF : F.Sane) (r : ℝ) : Det (ieee F r) := by
  intro v hv w hw _
  exact ieee_functional hF hv hw

private theorem det_exact {r : ℝ} (hr : r ≠ 0) :
    Det {v | v.WF F ∧ v.IsNum ∧ v.toReal F = r} := by
  intro v hv w hw _
  exact num_eq_of_toReal_eq hv.1 hv.2.1 hw.1 hw.2.1 (hv.2.2 ▸ hr)
    (hv.2.2.trans hw.2.2.symm)

theorem fadd_det (hF : F.Sane) (z₁ z₂ : FVal) : Det (fadd F z₁ z₂) := by
  unfold fadd
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _ | exact det_ieee hF _

theorem fsub_det (hF : F.Sane) (z₁ z₂ : FVal) : Det (fsub F z₁ z₂) := by
  unfold fsub
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _ | exact det_ieee hF _

theorem fmul_det (hF : F.Sane) (z₁ z₂ : FVal) : Det (fmul F z₁ z₂) := by
  unfold fmul
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _ | exact det_ieee hF _

theorem fdiv_det (hF : F.Sane) (z₁ z₂ : FVal) : Det (fdiv F z₁ z₂) := by
  unfold fdiv
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _ | exact det_ieee hF _

theorem fmin_det (z₁ z₂ : FVal) : Det (fmin F z₁ z₂) := by
  unfold fmin
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _

theorem fmax_det (z₁ z₂ : FVal) : Det (fmax F z₁ z₂) := by
  unfold fmax
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _

theorem fsqrt_det (hF : F.Sane) (z : FVal) : Det (fsqrt F z) := by
  unfold fsqrt
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _ | exact det_ieee hF _

theorem fceil_det (hF : F.Sane) {z : FVal} (hz : z.WF F) : Det (fceil F z) := by
  cases hF
  unfold fceil
  split
  · exact det_nans _
  rename_i hn
  split
  · exact det_singleton _
  rename_i hi
  have hr := Adequacy.num_nonzero hz
    (Adequacy.num_of_not_nan_inf hn (fun h => hi (Or.inl h))) (fun h => hi (Or.inr h))
  split
  · exact det_singleton _
  rename_i hs
  exact det_exact (Adequacy.ceil_nonzero hr hs)

theorem ffloor_det (hF : F.Sane) {z : FVal} (hz : z.WF F) : Det (ffloor F z) := by
  cases hF
  unfold ffloor
  split
  · exact det_nans _
  rename_i hn
  split
  · exact det_singleton _
  rename_i hi
  have hr := Adequacy.num_nonzero hz
    (Adequacy.num_of_not_nan_inf hn (fun h => hi (Or.inl h))) (fun h => hi (Or.inr h))
  split
  · exact det_singleton _
  rename_i hs
  exact det_exact (Adequacy.floor_nonzero hr hs)

theorem ftrunc_det (hF : F.Sane) {z : FVal} (hz : z.WF F) : Det (ftrunc F z) := by
  cases hF
  unfold ftrunc
  split
  · exact det_nans _
  rename_i hn
  split
  · exact det_singleton _
  rename_i hi
  have hr := Adequacy.num_nonzero hz
    (Adequacy.num_of_not_nan_inf hn (fun h => hi (Or.inl h))) (fun h => hi (Or.inr h))
  split
  · exact det_singleton _
  rename_i hp
  split
  · exact det_singleton _
  rename_i hm
  apply det_exact
  unfold truncR
  split
  · exact Adequacy.floor_nonzero hr hp
  · exact Adequacy.ceil_nonzero hr hm

theorem fnearest_det (hF : F.Sane) {z : FVal} (hz : z.WF F) : Det (fnearest F z) := by
  cases hF
  unfold fnearest
  split
  · exact det_nans _
  rename_i hn
  split
  · exact det_singleton _
  rename_i hi
  have hr := Adequacy.num_nonzero hz
    (Adequacy.num_of_not_nan_inf hn (fun h => hi (Or.inl h))) (fun h => hi (Or.inr h))
  split
  · exact det_singleton _
  rename_i hp
  split
  · exact det_singleton _
  rename_i hm
  apply det_exact
  intro he
  have hz : roundEven (z.toReal F) = 0 := by exact_mod_cast he
  have hb := Adequacy.roundEven_zero_bounds hz
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · exact hm ⟨hb.1, hneg⟩
  · exact hp ⟨hpos, hb.2⟩

theorem fpromote_det (z : FVal) : Det (fpromote z) := by
  unfold fpromote
  split
  · exact det_nans _
  split
  · exact det_nans _
  split
  · exact det_singleton _
  intro v hv w hw _
  by_cases hr : z.toReal f32fmt = 0
  · have hv0 := num_zero_eq hv.1 hv.2.1 (hv.2.2.2.trans hr)
    have hw0 := num_zero_eq hw.1 hw.2.1 (hw.2.2.2.trans hr)
    rw [hv0, hw0, hv.2.2.1, hw.2.2.1]
  · exact num_eq_of_toReal_eq hv.1 hv.2.1 hw.1 hw.2.1 (hv.2.2.2 ▸ hr)
      (hv.2.2.2.trans hw.2.2.2.symm)

theorem fdemote_det (z : FVal) : Det (fdemote z) := by
  unfold fdemote
  repeat' split
  all_goals first | exact det_nans _ | exact det_singleton _ | exact det_ieee f32fmt_sane _

theorem fconvertU_det (hF : F.Sane) {M : ℕ} (i : BitVec M) : Det (fconvertU F i) :=
  det_ieee hF _

theorem fconvertS_det (hF : F.Sane) {M : ℕ} (i : BitVec M) : Det (fconvertS F i) :=
  det_ieee hF _

end FVA.Wasm.Num
