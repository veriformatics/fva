import Proofs.Bounds
namespace TMM
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem log0 : ((-22307 / 40000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1916 : ℚ) : ℝ) ∧ Real.log ((1097 / 1916 : ℚ) : ℝ) ≤ ((-139411 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1916 : ℚ) (434933 / 500000 : ℚ) (869867 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log1 : ((-462357 / 1000000 : ℚ) : ℝ) ≤ Real.log ((12067 / 19160 : ℚ) : ℝ) ∧ Real.log ((12067 / 19160 : ℚ) : ℝ) ≤ ((-231171 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (12067 / 19160 : ℚ) (445421 / 500000 : ℚ) (890843 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log2 : ((-220203 / 500000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1704 : ℚ) : ℝ) ∧ Real.log ((1097 / 1704 : ℚ) : ℝ) ≤ ((-440393 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1704 : ℚ) (13996 / 15625 : ℚ) (179149 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log3 : ((-109971 / 250000 : ℚ) : ℝ) ≤ Real.log ((9873 / 15328 : ℚ) : ℝ) ∧ Real.log ((9873 / 15328 : ℚ) : ℝ) ≤ ((-43987 / 100000 : ℚ) : ℝ) := by
  have h := root_bounds (9873 / 15328 : ℚ) (895861 / 1000000 : ℚ) (447931 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log4 : ((-19657 / 50000 : ℚ) : ℝ) ≤ Real.log ((3291 / 4876 : ℚ) : ℝ) ∧ Real.log ((3291 / 4876 : ℚ) : ℝ) ≤ ((-39313 / 100000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 4876 : ℚ) (906391 / 1000000 : ℚ) (113299 / 125000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log5 : ((-187671 / 500000 : ℚ) : ℝ) ≤ Real.log ((3291 / 4790 : ℚ) : ℝ) ∧ Real.log ((3291 / 4790 : ℚ) : ℝ) ≤ ((-375333 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 4790 : ℚ) (910433 / 1000000 : ℚ) (455217 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log6 : ((-45309 / 125000 : ℚ) : ℝ) ≤ Real.log ((4388 / 6305 : ℚ) : ℝ) ∧ Real.log ((4388 / 6305 : ℚ) : ℝ) ≤ ((-362463 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 6305 : ℚ) (913367 / 1000000 : ℚ) (114171 / 125000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log7 : ((-5578 / 15625 : ℚ) : ℝ) ≤ Real.log ((12067 / 17244 : ℚ) : ℝ) ∧ Real.log ((12067 / 17244 : ℚ) : ℝ) ≤ ((-44623 / 125000 : ℚ) : ℝ) := by
  have h := root_bounds (12067 / 17244 : ℚ) (914619 / 1000000 : ℚ) (45731 / 50000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log8 : ((-356769 / 1000000 : ℚ) : ℝ) ≤ Real.log ((7679 / 10971 : ℚ) : ℝ) ∧ Real.log ((7679 / 10971 : ℚ) : ℝ) ≤ ((-356761 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 10971 : ℚ) (91467 / 100000 : ℚ) (914671 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log9 : ((-334519 / 1000000 : ℚ) : ℝ) ≤ Real.log ((5485 / 7664 : ℚ) : ℝ) ∧ Real.log ((5485 / 7664 : ℚ) : ℝ) ≤ ((-20907 / 62500 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 7664 : ℚ) (229943 / 250000 : ℚ) (919773 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log10 : ((-322621 / 1000000 : ℚ) : ℝ) ≤ Real.log ((3291 / 4544 : ℚ) : ℝ) ∧ Real.log ((3291 / 4544 : ℚ) : ℝ) ≤ ((-161307 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 4544 : ℚ) (57657 / 62500 : ℚ) (922513 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log11 : ((-6433 / 20000 : ℚ) : ℝ) ≤ Real.log ((5485 / 7566 : ℚ) : ℝ) ∧ Real.log ((5485 / 7566 : ℚ) : ℝ) ≤ ((-321643 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 7566 : ℚ) (57671 / 62500 : ℚ) (922737 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log12 : ((-293481 / 1000000 : ℚ) : ℝ) ≤ Real.log ((6582 / 8827 : ℚ) : ℝ) ∧ Real.log ((6582 / 8827 : ℚ) : ℝ) ≤ ((-146737 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (6582 / 8827 : ℚ) (929257 / 1000000 : ℚ) (464629 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log13 : ((-286251 / 1000000 : ℚ) : ℝ) ≤ Real.log ((7679 / 10224 : ℚ) : ℝ) ∧ Real.log ((7679 / 10224 : ℚ) : ℝ) ≤ ((-57249 / 200000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 10224 : ℚ) (465469 / 500000 : ℚ) (930939 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log14 : ((-134991 / 500000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1437 : ℚ) : ℝ) ∧ Real.log ((1097 / 1437 : ℚ) : ℝ) ≤ ((-33747 / 125000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1437 : ℚ) (233683 / 250000 : ℚ) (934733 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log15 : ((-129803 / 500000 : ℚ) : ℝ) ≤ Real.log ((6582 / 8533 : ℚ) : ℝ) ∧ Real.log ((6582 / 8533 : ℚ) : ℝ) ≤ ((-649 / 2500 : ℚ) : ℝ) := by
  have h := root_bounds (6582 / 8533 : ℚ) (23429 / 25000 : ℚ) (937161 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log16 : ((-129041 / 500000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1420 : ℚ) : ℝ) ∧ Real.log ((1097 / 1420 : ℚ) : ℝ) ≤ ((-64519 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1420 : ℚ) (937517 / 1000000 : ℚ) (468759 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log17 : ((-128557 / 500000 : ℚ) : ℝ) ≤ Real.log ((8776 / 11349 : ℚ) : ℝ) ∧ Real.log ((8776 / 11349 : ℚ) : ℝ) ≤ ((-64277 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (8776 / 11349 : ℚ) (58609 / 62500 : ℚ) (187549 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log18 : ((-235609 / 1000000 : ℚ) : ℝ) ≤ Real.log ((9873 / 12496 : ℚ) : ℝ) ∧ Real.log ((9873 / 12496 : ℚ) : ℝ) ≤ ((-58901 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (9873 / 12496 : ℚ) (942799 / 1000000 : ℚ) (2357 / 2500 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log19 : ((-55809 / 250000 : ℚ) : ℝ) ≤ Real.log ((8776 / 10971 : ℚ) : ℝ) ∧ Real.log ((8776 / 10971 : ℚ) : ℝ) ≤ ((-22323 / 100000 : ℚ) : ℝ) := by
  have h := root_bounds (8776 / 10971 : ℚ) (23643 / 25000 : ℚ) (945721 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log20 : ((-221189 / 1000000 : ℚ) : ℝ) ≤ Real.log ((7679 / 9580 : ℚ) : ℝ) ∧ Real.log ((7679 / 9580 : ℚ) : ℝ) ≤ ((-221183 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 9580 : ℚ) (236551 / 250000 : ℚ) (189241 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log21 : ((-217259 / 1000000 : ℚ) : ℝ) ≤ Real.log ((5485 / 6816 : ℚ) : ℝ) ∧ Real.log ((5485 / 6816 : ℚ) : ℝ) ≤ ((-108627 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 6816 : ℚ) (473567 / 500000 : ℚ) (189427 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log22 : ((-214173 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1359 : ℚ) : ℝ) ∧ Real.log ((1097 / 1359 : ℚ) : ℝ) ≤ ((-26771 / 125000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1359 : ℚ) (189573 / 200000 : ℚ) (473933 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log23 : ((-186003 / 1000000 : ℚ) : ℝ) ≤ Real.log ((4388 / 5285 : ℚ) : ℝ) ∧ Real.log ((4388 / 5285 : ℚ) : ℝ) ≤ ((-92999 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 5285 : ℚ) (238641 / 250000 : ℚ) (190913 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log24 : ((-18297 / 100000 : ℚ) : ℝ) ≤ Real.log ((4388 / 5269 : ℚ) : ℝ) ∧ Real.log ((4388 / 5269 : ℚ) : ℝ) ≤ ((-36593 / 200000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 5269 : ℚ) (119411 / 125000 : ℚ) (955289 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log25 : ((-761 / 5000 : ℚ) : ℝ) ≤ Real.log ((3291 / 3832 : ℚ) : ℝ) ∧ Real.log ((3291 / 3832 : ℚ) : ℝ) ≤ ((-30439 / 200000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 3832 : ℚ) (192533 / 200000 : ℚ) (481333 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log26 : ((-139327 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1261 : ℚ) : ℝ) ∧ Real.log ((1097 / 1261 : ℚ) : ℝ) ≤ ((-69661 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1261 : ℚ) (120721 / 125000 : ℚ) (965769 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log27 : ((-137211 / 1000000 : ℚ) : ℝ) ≤ Real.log ((3291 / 3775 : ℚ) : ℝ) ∧ Real.log ((3291 / 3775 : ℚ) : ℝ) ≤ ((-68603 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 3775 : ℚ) (966279 / 1000000 : ℚ) (24157 / 25000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log28 : ((-124147 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1242 : ℚ) : ℝ) ∧ Real.log ((1097 / 1242 : ℚ) : ℝ) ≤ ((-62071 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1242 : ℚ) (6059 / 6250 : ℚ) (969441 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log29 : ((-24469 / 200000 : ℚ) : ℝ) ≤ Real.log ((18649 / 21076 : ℚ) : ℝ) ∧ Real.log ((18649 / 21076 : ℚ) : ℝ) ≤ ((-122339 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (18649 / 21076 : ℚ) (969877 / 1000000 : ℚ) (484939 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log30 : ((-52727 / 500000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1219 : ℚ) : ℝ) ∧ Real.log ((1097 / 1219 : ℚ) : ℝ) ≤ ((-105449 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1219 : ℚ) (973981 / 1000000 : ℚ) (486991 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log31 : ((-96389 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1208 : ℚ) : ℝ) ∧ Real.log ((1097 / 1208 : ℚ) : ℝ) ≤ ((-96383 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1208 : ℚ) (976191 / 1000000 : ℚ) (15253 / 15625 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log32 : ((-43829 / 500000 : ℚ) : ℝ) ≤ Real.log ((2194 / 2395 : ℚ) : ℝ) ∧ Real.log ((2194 / 2395 : ℚ) : ℝ) ≤ ((-87653 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (2194 / 2395 : ℚ) (244581 / 250000 : ℚ) (39133 / 40000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log33 : ((-23419 / 500000 : ℚ) : ℝ) ≤ Real.log ((5485 / 5748 : ℚ) : ℝ) ∧ Real.log ((5485 / 5748 : ℚ) : ℝ) ≤ ((-46833 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 5748 : ℚ) (988359 / 1000000 : ℚ) (24709 / 25000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log34 : ((-34937 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1136 : ℚ) : ℝ) ∧ Real.log ((1097 / 1136 : ℚ) : ℝ) ≤ ((-8733 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1136 : ℚ) (123913 / 125000 : ℚ) (198261 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log35 : ((-2123 / 62500 : ℚ) : ℝ) ≤ Real.log ((10970 / 11349 : ℚ) : ℝ) ∧ Real.log ((10970 / 11349 : ℚ) : ℝ) ≤ ((-33963 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (10970 / 11349 : ℚ) (123943 / 125000 : ℚ) (198309 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log36 : ((-31851 / 1000000 : ℚ) : ℝ) ≤ Real.log ((2194 / 2265 : ℚ) : ℝ) ∧ Real.log ((2194 / 2265 : ℚ) : ℝ) ≤ ((-15923 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (2194 / 2265 : ℚ) (992069 / 1000000 : ℚ) (99207 / 100000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log37 : ((0 / 1 : ℚ) : ℝ) ≤ Real.log ((1 / 1 : ℚ) : ℝ) ∧ Real.log ((1 / 1 : ℚ) : ℝ) ≤ ((1 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (1 / 1 : ℚ) (1 / 1 : ℚ) (1000001 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log38 : ((1951 / 1000000 : ℚ) : ℝ) ≤ Real.log ((7679 / 7664 : ℚ) : ℝ) ∧ Real.log ((7679 / 7664 : ℚ) : ℝ) ≤ ((489 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 7664 : ℚ) (125061 / 125000 : ℚ) (1000489 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log39 : ((1173 / 125000 : ℚ) : ℝ) ≤ Real.log ((4388 / 4347 : ℚ) : ℝ) ∧ Real.log ((4388 / 4347 : ℚ) : ℝ) ≤ ((9389 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 4347 : ℚ) (1002349 / 1000000 : ℚ) (20047 / 20000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log40 : ((37143 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1057 : ℚ) : ℝ) ∧ Real.log ((1097 / 1057 : ℚ) : ℝ) ≤ ((37147 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1057 : ℚ) (1009329 / 1000000 : ℚ) (100933 / 100000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log41 : ((2687 / 62500 : ℚ) : ℝ) ≤ Real.log ((6582 / 6305 : ℚ) : ℝ) ∧ Real.log ((6582 / 6305 : ℚ) : ℝ) ≤ ((42997 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (6582 / 6305 : ℚ) (505403 / 500000 : ℚ) (1010807 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log42 : ((29087 / 500000 : ℚ) : ℝ) ≤ Real.log ((1097 / 1035 : ℚ) : ℝ) ∧ Real.log ((1097 / 1035 : ℚ) : ℝ) ≤ ((58179 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 1035 : ℚ) (20293 / 20000 : ℚ) (1014651 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log43 : ((30689 / 500000 : ℚ) : ℝ) ≤ Real.log ((14261 / 13412 : ℚ) : ℝ) ∧ Real.log ((14261 / 13412 : ℚ) : ℝ) ≤ ((61383 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (14261 / 13412 : ℚ) (1015463 / 1000000 : ℚ) (126933 / 125000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log44 : ((19217 / 250000 : ℚ) : ℝ) ≤ Real.log ((6582 / 6095 : ℚ) : ℝ) ∧ Real.log ((6582 / 6095 : ℚ) : ℝ) ≤ ((76873 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (6582 / 6095 : ℚ) (1019403 / 1000000 : ℚ) (254851 / 250000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log45 : ((9791 / 125000 : ℚ) : ℝ) ≤ Real.log ((18649 / 17244 : ℚ) : ℝ) ∧ Real.log ((18649 / 17244 : ℚ) : ℝ) ≤ ((19583 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (18649 / 17244 : ℚ) (40791 / 40000 : ℚ) (15934 / 15625 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log46 : ((16763 / 200000 : ℚ) : ℝ) ≤ Real.log ((5485 / 5044 : ℚ) : ℝ) ∧ Real.log ((5485 / 5044 : ℚ) : ℝ) ≤ ((4191 / 50000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 5044 : ℚ) (40847 / 40000 : ℚ) (127647 / 125000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log47 : ((42967 / 500000 : ℚ) : ℝ) ≤ Real.log ((3291 / 3020 : ℚ) : ℝ) ∧ Real.log ((3291 / 3020 : ℚ) : ℝ) ≤ ((85939 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 3020 : ℚ) (255429 / 250000 : ℚ) (1021717 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log48 : ((22397 / 200000 : ℚ) : ℝ) ≤ Real.log ((9873 / 8827 : ℚ) : ℝ) ∧ Real.log ((9873 / 8827 : ℚ) : ℝ) ≤ ((11199 / 100000 : ℚ) : ℝ) := by
  have h := root_bounds (9873 / 8827 : ℚ) (128549 / 125000 : ℚ) (1028393 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log49 : ((117691 / 1000000 : ℚ) : ℝ) ≤ Real.log ((5485 / 4876 : ℚ) : ℝ) ∧ Real.log ((5485 / 4876 : ℚ) : ℝ) ≤ ((1839 / 15625 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 4876 : ℚ) (51493 / 50000 : ℚ) (1029861 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log50 : ((119213 / 1000000 : ℚ) : ℝ) ≤ Real.log ((7679 / 6816 : ℚ) : ℝ) ∧ Real.log ((7679 / 6816 : ℚ) : ℝ) ≤ ((59609 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 6816 : ℚ) (257563 / 250000 : ℚ) (1030253 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log51 : ((135483 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 958 : ℚ) : ℝ) ∧ Real.log ((1097 / 958 : ℚ) : ℝ) ≤ ((2117 / 15625 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 958 : ℚ) (1034451 / 1000000 : ℚ) (258613 / 250000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log52 : ((73693 / 500000 : ℚ) : ℝ) ≤ Real.log ((3291 / 2840 : ℚ) : ℝ) ∧ Real.log ((3291 / 2840 : ℚ) : ℝ) ≤ ((147391 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 2840 : ℚ) (518767 / 500000 : ℚ) (207507 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log53 : ((74177 / 500000 : ℚ) : ℝ) ≤ Real.log ((4388 / 3783 : ℚ) : ℝ) ∧ Real.log ((4388 / 3783 : ℚ) : ℝ) ≤ ((148359 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 3783 : ℚ) (207557 / 200000 : ℚ) (518893 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log54 : ((150469 / 1000000 : ℚ) : ℝ) ≤ Real.log ((4388 / 3775 : ℚ) : ℝ) ∧ Real.log ((4388 / 3775 : ℚ) : ℝ) ≤ ((75237 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 3775 : ℚ) (519167 / 500000 : ℚ) (207667 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log55 : ((81767 / 500000 : ℚ) : ℝ) ≤ Real.log ((2194 / 1863 : ℚ) : ℝ) ∧ Real.log ((2194 / 1863 : ℚ) : ℝ) ≤ ((163539 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (2194 / 1863 : ℚ) (1041731 / 1000000 : ℚ) (260433 / 250000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log56 : ((82867 / 500000 : ℚ) : ℝ) ≤ Real.log ((12067 / 10224 : ℚ) : ℝ) ∧ Real.log ((12067 / 10224 : ℚ) : ℝ) ≤ ((165739 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (12067 / 10224 : ℚ) (16286 / 15625 : ℚ) (208461 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log57 : ((182229 / 1000000 : ℚ) : ℝ) ≤ Real.log ((4388 / 3657 : ℚ) : ℝ) ∧ Real.log ((4388 / 3657 : ℚ) : ℝ) ≤ ((91117 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 3657 : ℚ) (1046611 / 1000000 : ℚ) (261653 / 250000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log58 : ((37641 / 200000 : ℚ) : ℝ) ≤ Real.log ((5485 / 4544 : ℚ) : ℝ) ∧ Real.log ((5485 / 4544 : ℚ) : ℝ) ≤ ((18821 / 100000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 4544 : ℚ) (65511 / 62500 : ℚ) (1048177 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log59 : ((47823 / 250000 : ℚ) : ℝ) ≤ Real.log ((1097 / 906 : ℚ) : ℝ) ∧ Real.log ((1097 / 906 : ℚ) : ℝ) ≤ ((2989 / 15625 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 906 : ℚ) (209797 / 200000 : ℚ) (524493 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log60 : ((24643 / 125000 : ℚ) : ℝ) ≤ Real.log ((7679 / 6305 : ℚ) : ℝ) ∧ Real.log ((7679 / 6305 : ℚ) : ℝ) ≤ ((197149 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 6305 : ℚ) (1050521 / 1000000 : ℚ) (525261 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log61 : ((215527 / 1000000 : ℚ) : ℝ) ≤ Real.log ((14261 / 11496 : ℚ) : ℝ) ∧ Real.log ((14261 / 11496 : ℚ) : ℝ) ≤ ((53883 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (14261 / 11496 : ℚ) (3298 / 3125 : ℚ) (1055361 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log62 : ((27047 / 125000 : ℚ) : ℝ) ≤ Real.log ((9873 / 7952 : ℚ) : ℝ) ∧ Real.log ((9873 / 7952 : ℚ) : ℝ) ≤ ((216381 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (9873 / 7952 : ℚ) (32987 / 31250 : ℚ) (211117 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log63 : ((46159 / 200000 : ℚ) : ℝ) ≤ Real.log ((12067 / 9580 : ℚ) : ℝ) ∧ Real.log ((12067 / 9580 : ℚ) : ℝ) ≤ ((577 / 2500 : ℚ) : ℝ) := by
  have h := root_bounds (12067 / 9580 : ℚ) (264849 / 250000 : ℚ) (1059397 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log64 : ((115509 / 500000 : ℚ) : ℝ) ≤ Real.log ((7679 / 6095 : ℚ) : ℝ) ∧ Real.log ((7679 / 6095 : ℚ) : ℝ) ≤ ((231023 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 6095 : ℚ) (211891 / 200000 : ℚ) (16554 / 15625 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log65 : ((60021 / 250000 : ℚ) : ℝ) ≤ Real.log ((7679 / 6040 : ℚ) : ℝ) ∧ Real.log ((7679 / 6040 : ℚ) : ℝ) ≤ ((240089 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 6040 : ℚ) (1061859 / 1000000 : ℚ) (53093 / 50000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log66 : ((252747 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 852 : ℚ) : ℝ) ∧ Real.log ((1097 / 852 : ℚ) : ℝ) ≤ ((15797 / 62500 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 852 : ℚ) (532613 / 500000 : ℚ) (1065227 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log67 : ((50653 / 200000 : ℚ) : ℝ) ≤ Real.log ((9873 / 7664 : ℚ) : ℝ) ∧ Real.log ((9873 / 7664 : ℚ) : ℝ) ≤ ((253271 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (9873 / 7664 : ℚ) (266341 / 250000 : ℚ) (213073 / 200000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log68 : ((133069 / 500000 : ℚ) : ℝ) ≤ Real.log ((3291 / 2522 : ℚ) : ℝ) ∧ Real.log ((3291 / 2522 : ℚ) : ℝ) ≤ ((266143 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 2522 : ℚ) (534399 / 500000 : ℚ) (1068799 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log69 : ((140659 / 500000 : ℚ) : ℝ) ≤ Real.log ((1097 / 828 : ℚ) : ℝ) ∧ Real.log ((1097 / 828 : ℚ) : ℝ) ≤ ((70331 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 828 : ℚ) (536431 / 500000 : ℚ) (1072863 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log70 : ((57927 / 200000 : ℚ) : ℝ) ≤ Real.log ((7679 / 5748 : ℚ) : ℝ) ∧ Real.log ((7679 / 5748 : ℚ) : ℝ) ≤ ((289641 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 5748 : ℚ) (215019 / 200000 : ℚ) (134387 / 125000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log71 : ((300009 / 1000000 : ℚ) : ℝ) ≤ Real.log ((3291 / 2438 : ℚ) : ℝ) ∧ Real.log ((3291 / 2438 : ℚ) : ℝ) ≤ ((60003 / 200000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 2438 : ℚ) (1077887 / 1000000 : ℚ) (16842 / 15625 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log72 : ((158843 / 500000 : ℚ) : ℝ) ≤ Real.log ((7679 / 5589 : ℚ) : ℝ) ∧ Real.log ((7679 / 5589 : ℚ) : ℝ) ≤ ((79423 / 250000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 5589 : ℚ) (1082661 / 1000000 : ℚ) (541331 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log73 : ((165337 / 500000 : ℚ) : ℝ) ≤ Real.log ((8776 / 6305 : ℚ) : ℝ) ∧ Real.log ((8776 / 6305 : ℚ) : ℝ) ≤ ((8267 / 25000 : ℚ) : ℝ) := by
  have h := root_bounds (8776 / 6305 : ℚ) (543091 / 500000 : ℚ) (1086183 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log74 : ((345857 / 1000000 : ℚ) : ℝ) ≤ Real.log ((4388 / 3105 : ℚ) : ℝ) ∧ Real.log ((4388 / 3105 : ℚ) : ℝ) ≤ ((43233 / 125000 : ℚ) : ℝ) := by
  have h := root_bounds (4388 / 3105 : ℚ) (1090313 / 1000000 : ℚ) (545157 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log75 : ((364549 / 1000000 : ℚ) : ℝ) ≤ Real.log ((8776 / 6095 : ℚ) : ℝ) ∧ Real.log ((8776 / 6095 : ℚ) : ℝ) ≤ ((364557 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (8776 / 6095 : ℚ) (54771 / 50000 : ℚ) (1095421 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log76 : ((185263 / 500000 : ℚ) : ℝ) ≤ Real.log ((3291 / 2272 : ℚ) : ℝ) ∧ Real.log ((3291 / 2272 : ℚ) : ℝ) ≤ ((185267 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (3291 / 2272 : ℚ) (548529 / 500000 : ℚ) (1097059 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log77 : ((74299 / 200000 : ℚ) : ℝ) ≤ Real.log ((5485 / 3783 : ℚ) : ℝ) ∧ Real.log ((5485 / 3783 : ℚ) : ℝ) ≤ ((371503 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 3783 : ℚ) (274331 / 250000 : ℚ) (43893 / 40000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log78 : ((373613 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 755 : ℚ) : ℝ) ∧ Real.log ((1097 / 755 : ℚ) : ℝ) ≤ ((373621 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 755 : ℚ) (219581 / 200000 : ℚ) (548953 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log79 : ((193339 / 500000 : ℚ) : ℝ) ≤ Real.log ((5485 / 3726 : ℚ) : ℝ) ∧ Real.log ((5485 / 3726 : ℚ) : ℝ) ≤ ((193343 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 3726 : ℚ) (1101497 / 1000000 : ℚ) (550749 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log80 : ((50671 / 125000 : ℚ) : ℝ) ≤ Real.log ((5485 / 3657 : ℚ) : ℝ) ∧ Real.log ((5485 / 3657 : ℚ) : ℝ) ≤ ((202689 / 500000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 3657 : ℚ) (34583 / 31250 : ℚ) (1106657 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log81 : ((417047 / 1000000 : ℚ) : ℝ) ≤ Real.log ((12067 / 7952 : ℚ) : ℝ) ∧ Real.log ((12067 / 7952 : ℚ) : ℝ) ≤ ((417057 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (12067 / 7952 : ℚ) (277473 / 250000 : ℚ) (1109893 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log82 : ((84057 / 200000 : ℚ) : ℝ) ≤ Real.log ((7679 / 5044 : ℚ) : ℝ) ∧ Real.log ((7679 / 5044 : ℚ) : ℝ) ≤ ((52537 / 125000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 5044 : ℚ) (1110791 / 1000000 : ℚ) (138849 / 125000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log83 : ((435061 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 710 : ℚ) : ℝ) ∧ Real.log ((1097 / 710 : ℚ) : ℝ) ≤ ((435073 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 710 : ℚ) (557451 / 500000 : ℚ) (1114903 / 1000000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log84 : ((90831 / 200000 : ℚ) : ℝ) ≤ Real.log ((7679 / 4876 : ℚ) : ℝ) ∧ Real.log ((7679 / 4876 : ℚ) : ℝ) ≤ ((454169 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (7679 / 4876 : ℚ) (1120237 / 1000000 : ℚ) (560119 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log85 : ((475883 / 1000000 : ℚ) : ℝ) ≤ Real.log ((5485 / 3408 : ℚ) : ℝ) ∧ Real.log ((5485 / 3408 : ℚ) : ℝ) ≤ ((475899 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (5485 / 3408 : ℚ) (1126339 / 1000000 : ℚ) (56317 / 50000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log86 : ((568983 / 1000000 : ℚ) : ℝ) ≤ Real.log ((1097 / 621 : ℚ) : ℝ) ∧ Real.log ((1097 / 621 : ℚ) : ℝ) ≤ ((71127 / 125000 : ℚ) : ℝ) := by
  have h := root_bounds (1097 / 621 : ℚ) (230573 / 200000 : ℚ) (576433 / 500000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
theorem log87 : ((-2909 / 125000 : ℚ) : ℝ) ≤ Real.log ((977 / 1000 : ℚ) : ℝ) ∧ Real.log ((977 / 1000 : ℚ) : ℝ) ≤ ((-23267 / 1000000 : ℚ) : ℝ) := by
  have h := root_bounds (977 / 1000 : ℚ) (994199 / 1000000 : ℚ) (4971 / 5000 : ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · exact le_trans (by norm_num [lower, approx, error, z]) h.1
  · exact le_trans h.2 (by norm_num [upper, approx, error, z])
end TMM
