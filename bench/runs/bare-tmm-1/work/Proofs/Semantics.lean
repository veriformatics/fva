import Proofs.Model

namespace Verification

-- The rational ordering keys used by selected agree with the real M/A ordering.
lemma m_order (x y u v L R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hu : 0 < u) (hv : 0 < v) (hL : 0 < L) (hR : 0 < R) :
    (Real.log ((x/L)/(y/R)) < Real.log ((u/L)/(v/R))) ↔ x*v < u*y := by
  rw [Real.log_lt_log_iff (div_pos (div_pos hx hL) (div_pos hy hR))
    (div_pos (div_pos hu hL) (div_pos hv hR))]
  rw [div_lt_div_iff₀ (div_pos hy hR) (div_pos hv hR)]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_lt_div_iff_of_pos_right (mul_pos hL hR)

lemma a_order (x y u v L R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hu : 0 < u) (hv : 0 < v) (hL : 0 < L) (hR : 0 < R) :
    ((Real.log (x/L) + Real.log (y/R))/2 <
      (Real.log (u/L) + Real.log (v/R))/2) ↔ x*y < u*v := by
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.log_mul (ne_of_gt (div_pos hx hL)) (ne_of_gt (div_pos hy hR)),
    ← Real.log_mul (ne_of_gt (div_pos hu hL)) (ne_of_gt (div_pos hv hR))]
  rw [Real.log_lt_log_iff (mul_pos (div_pos hx hL) (div_pos hy hR))
    (mul_pos (div_pos hu hL) (div_pos hv hR))]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_lt_div_iff_of_pos_right (mul_pos hL hR)

end Verification
