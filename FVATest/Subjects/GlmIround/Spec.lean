import FVATest.Subjects.GlmIround.Lifted
import FVA.Spec.CAbi
import FVA.Spec.Numerics.Float

/-!
# What GLM 1.0.3's `glm::iround<double>` does (claim; contract U14 S5)

`glm-iround.wasm` is `extern "C" int iround(double x) { return glm::iround(x); }`, which GLM
compiles to `x + 0.5` then truncation toward zero. The module is the 66-byte artifact.

`iround_breaks`: `iround` returns 1 on the input `0.49999999999999994` (the `f64` just below one
half, bits `3fdfffffffffffff`), although that input's real value lies strictly between 0 and one
half, so its nearest integer is 0. "Round to the nearest integer" is false for the shipped code:
`x + 0.5` rounds up to exactly `1.0` here, and truncation then gives 1.
-/

namespace Subjects.GlmIround

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- `0.49999999999999994`, the largest `f64` below one half (bits `3fdfffffffffffff`). -/
def belowHalf : BitVec 64 := 0x3fdfffffffffffff

/-- R "nearest integer" is false for the shipped `iround`: it returns 1 on `belowHalf`, whose real
value is in `(0, 1/2)` — nearest integer 0, not 1. -/
def iround_breaks : Prop :=
  Returns Lifted.module "iround" [.f64 belowHalf] [.i32 1] ∧
    (ofBits f64fmt belowHalf).toReal f64fmt ∈ Set.Ioo (0 : ℝ) (1 / 2)

end Subjects.GlmIround
