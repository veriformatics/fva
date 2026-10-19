import AvgFloor.Spec
import FVA

namespace AvgFloor.Proof
open FVA.Wasm

/-- Five instructions plus the terminal empty instruction list require six fuel units. -/
theorem invoke_exact (fuel : Nat) (a b : BitVec 32) :
    invoke Lifted.avg_floor fuel [.i32 a, .i32 b] =
      if 6 ≤ fuel then some [.i32 ((a + b).sshiftRight 1)] else none := by
  rcases fuel with _ | (_ | (_ | (_ | (_ | (_ | fuel)))))
  all_goals first | rfl | skip
  wasm_sim [Lifted.avg_floor]
  simp only [BitVec.toNat_ofNat]
  rw [BitVec.add_comm]
  rfl

theorem returns_iff (a b r : BitVec 32) :
    Returns Lifted.module "avg_floor" [.i32 a, .i32 b] [.i32 r] ↔
      r = (a + b).sshiftRight 1 := by
  constructor
  · rintro ⟨f, hf, fuel, h⟩
    have : Lifted.avg_floor = f := by simpa [Lifted.module, Lifted.avg_floor] using hf
    subst f
    rw [invoke_exact] at h
    split at h
    · simpa using h.symm
    · contradiction
  · intro h
    subst r
    exact returns_of_invoke rfl ⟨6, by rw [invoke_exact]; rfl⟩

theorem input_bounds (a : BitVec 32) :
    -2147483648 ≤ a.toInt ∧ a.toInt ≤ 2147483647 := by
  have h₁ := BitVec.le_toInt a
  have h₂ := BitVec.toInt_lt (x := a)
  change -2147483648 ≤ a.toInt at h₁
  change a.toInt < 2147483648 at h₂
  omega

/-- This establishes that `floorMean` is mathematical floor, not C truncation. -/
theorem floorMean_is_floor (a b : BitVec 32) :
    2 * floorMean a b ≤ signedSum a b ∧
    signedSum a b < 2 * (floorMean a b + 1) := by
  unfold floorMean
  omega

/-- Encoding the mathematical answer as i32 never loses information. -/
theorem floorMean_fits (a b : BitVec 32) :
    (BitVec.ofInt 32 (floorMean a b)).toInt = floorMean a b := by
  obtain ⟨ha, ha'⟩ := input_bounds a
  obtain ⟨hb, hb'⟩ := input_bounds b
  apply BitVec.toInt_ofInt_eq_self (by decide)
  all_goals simp only [floorMean, signedSum]; omega

/-- Wrapping addition has the three usual signed-overflow cases. -/
theorem signed_add (a b : BitVec 32) :
    (a + b).toInt =
      if signedSum a b < -2147483648 then signedSum a b + 4294967296
      else if 2147483647 < signedSum a b then signedSum a b - 4294967296
      else signedSum a b := by
  rw [BitVec.toInt_add]
  change (signedSum a b).bmod 4294967296 = _
  obtain ⟨ha, ha'⟩ := input_bounds a
  obtain ⟨hb, hb'⟩ := input_bounds b
  simp only [Int.bmod, signedSum]
  repeat' first | split | omega

theorem output_value (a b : BitVec 32) :
    ((a + b).sshiftRight 1).toInt = wrappedMean a b := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, signed_add]
  rfl

theorem machine_behavior_holds : machine_behavior := by
  intro a b
  exact (returns_iff a b _).mpr rfl

theorem exact_result_holds : exact_result := by
  intro a b r
  rw [returns_iff, ← output_value]
  exact BitVec.toInt_inj.symm

theorem correct_iff_sum_fits_holds : correct_iff_sum_fits := by
  intro a b
  have hw := output_value a b
  have heq : wrappedMean a b = floorMean a b ↔ sumFits a b := by
    unfold wrappedMean floorMean sumFits
    dsimp only
    repeat' first | split | omega
  constructor
  · rintro ⟨r, hr, he⟩
    exact heq.mp (((exact_result_holds a b r).mp hr).symm.trans he)
  · intro h
    refine ⟨(a + b).sshiftRight 1, machine_behavior_holds a b, ?_⟩
    exact hw.trans (heq.mpr h)

theorem positive_overflow_holds : positive_overflow := by
  refine ⟨(returns_iff _ _ _).mpr (by decide), by decide, ?_⟩
  rw [returns_iff]
  decide

theorem negative_overflow_holds : negative_overflow := by
  refine ⟨(returns_iff _ _ _).mpr (by decide), by decide, ?_⟩
  rw [returns_iff]
  decide

theorem r1_false_holds : r1_false := by
  intro h
  have hc := (correct_iff_sum_fits_holds 2147483647#32 2147483647#32).mp
    (h 2147483647#32 2147483647#32)
  exact (by unfold sumFits signedSum; decide : ¬ sumFits 2147483647#32 2147483647#32) hc

theorem r2_false_holds : r2_false := by
  intro h
  have hn : ¬ sumFits 2147483647#32 2147483647#32 := by unfold sumFits signedSum; decide
  have hc := (correct_iff_sum_fits_holds 2147483647#32 2147483647#32).mp
    (h 2147483647#32 2147483647#32 hn)
  exact hn hc

end AvgFloor.Proof
