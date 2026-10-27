import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
#reduce |(1:ℚ)-3|
example : |(1:ℚ)-3| = 2 := by decide +kernel
example : ((4:ℚ)/1261) = (4:ℚ)/1261 := rfl
#reduce [2,1,3].mergeSort (· ≤ ·)
