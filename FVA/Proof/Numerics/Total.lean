import FVA.Proof.Numerics.Arith
import FVA.Proof.Numerics.Sqrt
import FVA.Proof.Numerics.Integral
import FVA.Proof.Numerics.Convert

/-!
# Every float operator has a result (contract D4)

On well-formed operands each spec operator's result set is nonempty: the executable operator's
result is a member. With `FVA.Proof.Numerics.Adequacy` (at most one non-NaN member), every
operator is total and deterministic outside its NaN cases.
-/

namespace FVA.Wasm.Num

open FVal

variable {F : FloatFormat}

theorem fadd_nonempty (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    (fadd F z₁ z₂).Nonempty := ⟨_, fadd_mem hF h₁ h₂⟩

theorem fsub_nonempty (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    (fsub F z₁ z₂).Nonempty := ⟨_, fsub_mem hF h₁ h₂⟩

theorem fmul_nonempty (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    (fmul F z₁ z₂).Nonempty := ⟨_, fmul_mem hF h₁ h₂⟩

theorem fdiv_nonempty (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    (fdiv F z₁ z₂).Nonempty := ⟨_, fdiv_mem hF h₁ h₂⟩

theorem fmin_nonempty (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    (fmin F z₁ z₂).Nonempty := ⟨_, fmin_mem hF h₁ h₂⟩

theorem fmax_nonempty (hF : F.Sane) {z₁ z₂ : FVal} (h₁ : z₁.WF F) (h₂ : z₂.WF F) :
    (fmax F z₁ z₂).Nonempty := ⟨_, fmax_mem hF h₁ h₂⟩

theorem fsqrt_nonempty (hF : F.Sane) {z : FVal} (hz : z.WF F) : (fsqrt F z).Nonempty :=
  ⟨_, fsqrt_mem hF hz⟩

theorem fceil_nonempty (hF : F.Wide) {z : FVal} (hz : z.WF F) : (fceil F z).Nonempty :=
  ⟨_, fceil_mem hF hz⟩

theorem ffloor_nonempty (hF : F.Wide) {z : FVal} (hz : z.WF F) : (ffloor F z).Nonempty :=
  ⟨_, ffloor_mem hF hz⟩

theorem ftrunc_nonempty (hF : F.Wide) {z : FVal} (hz : z.WF F) : (ftrunc F z).Nonempty :=
  ⟨_, ftrunc_mem hF hz⟩

theorem fnearest_nonempty (hF : F.Wide) {z : FVal} (hz : z.WF F) : (fnearest F z).Nonempty :=
  ⟨_, fnearest_mem hF hz⟩

theorem fpromote_nonempty {z : FVal} (hz : z.WF f32fmt) : (fpromote z).Nonempty :=
  ⟨_, fpromote_mem hz⟩

theorem fdemote_nonempty {z : FVal} (hz : z.WF f64fmt) : (fdemote z).Nonempty :=
  ⟨_, fdemote_mem hz⟩

theorem fconvertU_nonempty (hF : F.Sane) {M : ℕ} (i : BitVec M) : (fconvertU F i).Nonempty :=
  ⟨_, fconvertU_mem hF i⟩

theorem fconvertS_nonempty (hF : F.Sane) {M : ℕ} (i : BitVec M) : (fconvertS F i).Nonempty :=
  ⟨_, fconvertS_mem hF i⟩

end FVA.Wasm.Num
