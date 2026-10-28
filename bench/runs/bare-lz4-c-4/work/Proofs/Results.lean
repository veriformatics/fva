import Proofs.Artifact

namespace Verification
set_option maxRecDepth 10000

-- These proofs use kernel reduction, with no native_decide or execution oracle.
theorem zeroCapacity_other (src dst size : Nat) (m : Memory)
    (hs : src ≠ 0) (hn : size ≠ 1) :
    invoke decoderModule 100 src dst size 0 m =
      some ⟨4294967295, m, []⟩ := by
  cases src with
  | zero => exact False.elim (hs rfl)
  | succ src =>
    cases size with
    | zero => rfl
    | succ size =>
      cases size with
      | zero => exact False.elim (hn rfl)
      | succ size => rfl

-- Fixed source address, arbitrary destination address and arbitrary memory.
theorem zeroCapacity_unit (dst : Nat) (m : Memory) :
    invoke decoderModule 100 131072 dst 1 0 m =
      some ⟨(if readByte m 131072 = 0 then 0 else 4294967295), m,
        [⟨false, 131072, 1⟩]⟩ := by rfl

theorem zeroCapacity_empty (dst : Nat) (m : Memory) (h : readByte m 131072 = 0) :
    invoke decoderModule 100 131072 dst 1 0 m =
      some ⟨0, m, [⟨false, 131072, 1⟩]⟩ := by
  simpa only [h, ite_true] using zeroCapacity_unit dst m

theorem emptySource (dst : Nat) (m : Memory) :
    invoke decoderModule 100 131072 dst 0 13 m =
      some ⟨4294967295, m, []⟩ := by rfl

theorem zeroCapacity_safety (dst size : Nat) (m : Memory) :
    ∃ r, invoke decoderModule 100 131072 dst size 0 m = some r ∧
      r.memory = m ∧ safeTrace 131072 dst size 0 r.trace = true := by
  by_cases h : size = 1
  · subst size
    exact ⟨_, zeroCapacity_unit dst m, rfl, rfl⟩
  · exact ⟨_, zeroCapacity_other 131072 dst size m (by decide) h, rfl, rfl⟩

theorem zeroCapacity_sound (dst size : Nat) (m : Memory) (r : Result)
    (hr : invoke decoderModule 100 131072 dst size 0 m = some r)
    (hn : r.value < 2147483648) :
    size = 1 ∧ readByte m 131072 = 0 ∧ r.value = 0 ∧ r.memory = m ∧
      r.trace = [⟨false, 131072, 1⟩] := by
  by_cases h : size = 1
  · subst size
    have heq := Option.some.inj (hr.symm.trans (zeroCapacity_unit dst m))
    subst r
    by_cases hz : readByte m 131072 = 0
    · simp [hz]
    · simp [hz] at hn
  · have heq := Option.some.inj
      (hr.symm.trans (zeroCapacity_other 131072 dst size m (by decide) h))
    subst r
    exact False.elim (Nat.not_lt_of_ge (by decide : 2147483648 ≤ 4294967295) hn)

end Verification
