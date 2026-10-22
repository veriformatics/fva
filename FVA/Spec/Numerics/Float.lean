import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Defs
import FVA.Spec.Numerics.Int

/-!
# Floating-point operations (reviewed spec)

Transcribes WebAssembly 2.0 floating-point values (spec §2.2.3), their bit representation
(§4.3.1), rounding (§4.3.3 "Rounding"), NaN propagation, every float operator of §4.3.3, and the
float conversions of §4.3.4, case by case in the spec's order. Results are sets: an operator whose
result is a NaN may return any element of `nans`, and a claim about a program must hold for every
allowed result. Exact values are Mathlib reals; the executable implementation is proven against
this file separately.

Where the spec's prose and its formal equations disagree, the equations are transcribed; where
the equations contradict IEEE 754 and the official tests, IEEE is transcribed (each noted at the
definition).
-/

namespace FVA.Wasm.Num

open Classical

/-- A float bit width: `M` = significand bits, `E` = exponent bits (spec §2.2.3). -/
structure FloatFormat where
  /-- `significand(N)`. -/
  M : Nat
  /-- `exponent(N)`. -/
  E : Nat

/-- `f32`: `M = 23`, `E = 8`. -/
def f32fmt : FloatFormat := ⟨23, 8⟩
/-- `f64`: `M = 52`, `E = 11`. -/
def f64fmt : FloatFormat := ⟨52, 11⟩

namespace FloatFormat
variable (F : FloatFormat)
/-- Total bit width `N = 1 + E + M`. -/
def N : Nat := 1 + F.E + F.M
/-- Largest exponent of a normal value, `2^(E−1) − 1` (also `fbias_N`). -/
def emax : Int := 2 ^ (F.E - 1) - 1
/-- Smallest exponent, `−2^(E−1) + 2` (normals and subnormals). -/
def emin : Int := 2 - 2 ^ (F.E - 1)
/-- `canon_N = 2^(M−1)`: the canonical NaN payload. -/
def canon : Nat := 2 ^ (F.M - 1)
end FloatFormat

/-- Floating-point values (spec §2.2.3): a sign (`true` = negative) and a magnitude. -/
inductive FVal where
  /-- `±(1 + m·2^−M)·2^e`. -/
  | normal (neg : Bool) (m : Nat) (e : Int)
  /-- `±(0 + m·2^−M)·2^emin`; `m = 0` is a zero. -/
  | subnormal (neg : Bool) (m : Nat)
  /-- `±∞`. -/
  | inf (neg : Bool)
  /-- `±nan(n)`. -/
  | nan (neg : Bool) (n : Nat)
  deriving DecidableEq

namespace FVal
variable {F : FloatFormat}

/-- The side conditions of the grammar: `m < 2^M`, `emin ≤ e ≤ emax`, `1 ≤ n < 2^M`. -/
def WF (F : FloatFormat) : FVal → Prop
  | normal _ m e => m < 2 ^ F.M ∧ F.emin ≤ e ∧ e ≤ F.emax
  | subnormal _ m => m < 2 ^ F.M
  | inf _ => True
  | nan _ n => 1 ≤ n ∧ n < 2 ^ F.M

/-- The sign (`true` = negative). -/
def neg : FVal → Bool
  | normal s _ _ | subnormal s _ | inf s | nan s _ => s

/-- The value with the sign replaced. -/
def withSign (s : Bool) : FVal → FVal
  | normal _ m e => normal s m e
  | subnormal _ m => subnormal s m
  | inf _ => inf s
  | nan _ n => nan s n

/-- `+0`. -/
def posZero : FVal := subnormal false 0
/-- `−0`. -/
def negZero : FVal := subnormal true 0

/-- A NaN. -/
def IsNaN : FVal → Prop
  | nan _ _ => True
  | _ => False
/-- An infinity. -/
def IsInf : FVal → Prop
  | inf _ => True
  | _ => False
/-- A zero. -/
def IsZero : FVal → Prop
  | subnormal _ 0 => True
  | _ => False
/-- A number: neither a NaN nor an infinity. -/
def IsNum : FVal → Prop
  | normal _ _ _ | subnormal _ _ => True
  | _ => False

/-- The exact value of a number (spec §2.2.3); `0` for infinities and NaNs. -/
noncomputable def toReal (F : FloatFormat) : FVal → ℝ
  | normal s m e => (if s then -1 else 1) * (1 + (m : ℝ) * 2 ^ (-(F.M : Int))) * 2 ^ e
  | subnormal s m => (if s then -1 else 1) * ((m : ℝ) * 2 ^ (-(F.M : Int))) * 2 ^ F.emin
  | _ => 0

/-- The significand field `m` of a number (for `even_N`). -/
def sigField : FVal → Nat
  | normal _ m _ | subnormal _ m => m
  | _ => 0

end FVal

open FVal

/-! ## Bit representation (§4.3.1) -/

/-- `fbits_N(z)`: sign bit, `E` exponent bits, `M` significand bits. -/
def fbits (F : FloatFormat) : FVal → BitVec F.N
  | normal s m e => BitVec.ofNat F.N
      ((if s then 2 ^ (F.E + F.M) else 0) + (e + F.emax).toNat * 2 ^ F.M + m)
  | subnormal s m => BitVec.ofNat F.N ((if s then 2 ^ (F.E + F.M) else 0) + m)
  | inf s => BitVec.ofNat F.N ((if s then 2 ^ (F.E + F.M) else 0) + (2 ^ F.E - 1) * 2 ^ F.M)
  | nan s n => BitVec.ofNat F.N
      ((if s then 2 ^ (F.E + F.M) else 0) + (2 ^ F.E - 1) * 2 ^ F.M + n)

/-- `fbits_N⁻¹`: the value a bit pattern represents. -/
def ofBits (F : FloatFormat) (b : BitVec F.N) : FVal :=
  let s := decide (2 ^ (F.E + F.M) ≤ b.toNat)
  let ex := b.toNat / 2 ^ F.M % 2 ^ F.E
  let m := b.toNat % 2 ^ F.M
  if ex = 2 ^ F.E - 1 then (if m = 0 then inf s else nan s m)
  else if ex = 0 then subnormal s m
  else normal s m (ex - F.emax)

/-! ## Rounding (§4.3.3) -/

/-- An exact floating-point number: the value of some (well-formed) number. -/
def Exact (F : FloatFormat) (r : ℝ) : Prop := ∃ z : FVal, z.WF F ∧ z.IsNum ∧ z.toReal F = r

/-- `limit_N = 2^(2^(E−1))`: the smallest power of 2 not exactly representable. -/
noncomputable def limit (F : FloatFormat) : ℝ := 2 ^ (2 ^ (F.E - 1))

/-- A candidate number: exact, or a positive or negative limit number. -/
def Candidate (F : FloatFormat) (r : ℝ) : Prop := Exact F r ∨ r = limit F ∨ r = -limit F

/-- A candidate pair: two candidates with no candidate strictly between them. -/
def CandidatePair (F : FloatFormat) (z₁ z₂ : ℝ) : Prop :=
  Candidate F z₁ ∧ Candidate F z₂ ∧ z₁ < z₂ ∧ ∀ z, Candidate F z → z ≤ z₁ ∨ z ≥ z₂

/-- `even_N(z)`: the significand field is even; limits count as even. -/
def EvenCand (F : FloatFormat) (z : ℝ) : Prop :=
  z = limit F ∨ z = -limit F ∨
    ∃ v : FVal, v.WF F ∧ v.IsNum ∧ v.toReal F = z ∧ v.sigField % 2 = 0

/-- `rectify_N(r, z)`: a limit becomes the infinity of its sign, a zero takes the sign of `r`,
any other candidate is that number. -/
def Rectify (F : FloatFormat) (r z : ℝ) (v : FVal) : Prop :=
  (z = limit F ∧ v = inf false) ∨ (z = -limit F ∧ v = inf true) ∨
  (z = 0 ∧ v = subnormal (decide (r < 0)) 0) ∨
  (z ≠ 0 ∧ z ≠ limit F ∧ z ≠ -limit F ∧ v.WF F ∧ v.IsNum ∧ v.toReal F = z)

/-- `closest_N(r, z₁, z₂)` followed by `rectify_N`. -/
def Closest (F : FloatFormat) (r z₁ z₂ : ℝ) (v : FVal) : Prop :=
  (|r - z₁| < |r - z₂| ∧ Rectify F r z₁ v) ∨
  (|r - z₁| > |r - z₂| ∧ Rectify F r z₂ v) ∨
  (|r - z₁| = |r - z₂| ∧ EvenCand F z₁ ∧ Rectify F r z₁ v) ∨
  (|r - z₁| = |r - z₂| ∧ EvenCand F z₂ ∧ Rectify F r z₂ v)

/-- `ieee_N(r) = v`: the real `r` rounded to nearest, ties to even (§4.3.3, IEEE 754 §4.3.1). -/
def Ieee (F : FloatFormat) (r : ℝ) (v : FVal) : Prop :=
  (r = 0 ∧ v = posZero) ∨
  (r ≠ 0 ∧ Exact F r ∧ v.WF F ∧ v.IsNum ∧ v.toReal F = r) ∨
  (r ≥ limit F ∧ v = inf false) ∨
  (r ≤ -limit F ∧ v = inf true) ∨
  (∃ z₁ z₂, CandidatePair F z₁ z₂ ∧ z₁ < r ∧ r < z₂ ∧ Closest F r z₁ z₂ v)

/-- The results of rounding `r`. -/
def ieee (F : FloatFormat) (r : ℝ) : Set FVal := {v | Ieee F r v}

/-! ## NaN propagation (§4.3.3) -/

/-- `nans_N{z*}`: canonical NaNs (either sign) if every NaN in `zs` is canonical, else arithmetic
NaNs (payload at least `canon_N`, below `2^M`), either sign. -/
def nans (F : FloatFormat) (zs : List FVal) : Set FVal :=
  if ∀ z ∈ zs, ∀ s n, z = nan s n → n = F.canon then
    {v | ∃ s, v = nan s F.canon}
  else {v | ∃ s n, v = nan s n ∧ F.canon ≤ n ∧ n < 2 ^ F.M}

/-! ## Operators (§4.3.3) -/

/-- `fadd_N(z₁, z₂)`. -/
noncomputable def fadd (F : FloatFormat) (z₁ z₂ : FVal) : Set FVal :=
  if z₁.IsNaN ∨ z₂.IsNaN then nans F [z₁, z₂]
  else if z₁.IsInf ∧ z₂.IsInf ∧ z₁.neg ≠ z₂.neg then nans F []
  else if z₁.IsInf ∧ z₂.IsInf then {z₁}
  else if z₁.IsInf then {z₁}
  else if z₂.IsInf then {z₂}
  else if z₁.IsZero ∧ z₂.IsZero ∧ z₁.neg ≠ z₂.neg then {posZero}
  else if z₁.IsZero ∧ z₂.IsZero then {z₁}
  else if z₁.IsZero then {z₂}
  else if z₂.IsZero then {z₁}
  else if z₁.toReal F = -z₂.toReal F then {posZero}
  else ieee F (z₁.toReal F + z₂.toReal F)

/-- `fsub_N(z₁, z₂)`. -/
noncomputable def fsub (F : FloatFormat) (z₁ z₂ : FVal) : Set FVal :=
  if z₁.IsNaN ∨ z₂.IsNaN then nans F [z₁, z₂]
  else if z₁.IsInf ∧ z₂.IsInf ∧ z₁.neg = z₂.neg then nans F []
  else if z₁.IsInf ∧ z₂.IsInf then {z₁}
  else if z₁.IsInf then {z₁}
  else if z₂.IsInf then {z₂.withSign (!z₂.neg)}
  else if z₁.IsZero ∧ z₂.IsZero ∧ z₁.neg = z₂.neg then {posZero}
  else if z₁.IsZero ∧ z₂.IsZero then {z₁}
  else if z₂.IsZero then {z₁}
  else if z₁.IsZero then {z₂.withSign (!z₂.neg)}
  else if z₁.toReal F = z₂.toReal F then {posZero}
  else ieee F (z₁.toReal F - z₂.toReal F)

/-- `fmul_N(z₁, z₂)`. A zero times a number has the XOR sign, per IEEE 754 §6.3 and the official
tests (`f32.wast`: `mul -0x0p+0 0x1p+0 = -0x0p+0`); the spec's equations cover only two zeros and
send `±0·q` to `ieee_N(0) = +0`. -/
noncomputable def fmul (F : FloatFormat) (z₁ z₂ : FVal) : Set FVal :=
  if z₁.IsNaN ∨ z₂.IsNaN then nans F [z₁, z₂]
  else if (z₁.IsZero ∧ z₂.IsInf) ∨ (z₁.IsInf ∧ z₂.IsZero) then nans F []
  else if z₁.IsInf ∧ z₂.IsInf then {inf (z₁.neg != z₂.neg)}
  else if z₁.IsInf ∨ z₂.IsInf then {inf (z₁.neg != z₂.neg)}
  else if z₁.IsZero ∨ z₂.IsZero then {subnormal (z₁.neg != z₂.neg) 0}
  else ieee F (z₁.toReal F * z₂.toReal F)

/-- `fdiv_N(z₁, z₂)`. -/
noncomputable def fdiv (F : FloatFormat) (z₁ z₂ : FVal) : Set FVal :=
  if z₁.IsNaN ∨ z₂.IsNaN then nans F [z₁, z₂]
  else if z₁.IsInf ∧ z₂.IsInf then nans F []
  else if z₁.IsZero ∧ z₂.IsZero then nans F [z₁, z₂]
  else if z₁.IsInf then {inf (z₁.neg != z₂.neg)}
  else if z₂.IsInf then {subnormal (z₁.neg != z₂.neg) 0}
  else if z₁.IsZero then {subnormal (z₁.neg != z₂.neg) 0}
  else if z₂.IsZero then {inf (z₁.neg != z₂.neg)}
  else ieee F (z₁.toReal F / z₂.toReal F)

/-- `fmin_N(z₁, z₂)`. -/
noncomputable def fmin (F : FloatFormat) (z₁ z₂ : FVal) : Set FVal :=
  if z₁.IsNaN ∨ z₂.IsNaN then nans F [z₁, z₂]
  else if z₁ = inf true ∨ z₂ = inf true then {inf true}
  else if z₁ = inf false then {z₂}
  else if z₂ = inf false then {z₁}
  else if z₁.IsZero ∧ z₂.IsZero ∧ z₁.neg ≠ z₂.neg then {negZero}
  else if z₁.toReal F ≤ z₂.toReal F then {z₁} else {z₂}

/-- `fmax_N(z₁, z₂)`. -/
noncomputable def fmax (F : FloatFormat) (z₁ z₂ : FVal) : Set FVal :=
  if z₁.IsNaN ∨ z₂.IsNaN then nans F [z₁, z₂]
  else if z₁ = inf false ∨ z₂ = inf false then {inf false}
  else if z₁ = inf true then {z₂}
  else if z₂ = inf true then {z₁}
  else if z₁.IsZero ∧ z₂.IsZero ∧ z₁.neg ≠ z₂.neg then {posZero}
  else if z₁.toReal F ≥ z₂.toReal F then {z₁} else {z₂}

/-- `fcopysign_N(z₁, z₂)`: `z₁` with the sign of `z₂` (NaN payloads kept). -/
def fcopysign (z₁ z₂ : FVal) : FVal := z₁.withSign z₂.neg

/-- `fabs_N(z)`: positive sign (NaN payloads kept). -/
def fabs (z : FVal) : FVal := z.withSign false

/-- `fneg_N(z)`: negated sign (NaN payloads kept). -/
def fneg (z : FVal) : FVal := z.withSign (!z.neg)

/-- `fsqrt_N(z)`. -/
noncomputable def fsqrt (F : FloatFormat) (z : FVal) : Set FVal :=
  if z.IsNaN then nans F [z]
  else if z = inf true then nans F []
  else if z = inf false then {inf false}
  else if z.IsZero then {z}
  else if z.neg then nans F []
  else ieee F (Real.sqrt (z.toReal F))

/-- An integral real. -/
def IsIntegral (r : ℝ) : Prop := ∃ k : ℤ, r = k

/-- `fceil_N(z)`. -/
noncomputable def fceil (F : FloatFormat) (z : FVal) : Set FVal :=
  if z.IsNaN then nans F [z]
  else if z.IsInf ∨ z.IsZero then {z}
  else if -1 < z.toReal F ∧ z.toReal F < 0 then {negZero}
  else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ⌈z.toReal F⌉}

/-- `ffloor_N(z)`. -/
noncomputable def ffloor (F : FloatFormat) (z : FVal) : Set FVal :=
  if z.IsNaN then nans F [z]
  else if z.IsInf ∨ z.IsZero then {z}
  else if 0 < z.toReal F ∧ z.toReal F < 1 then {posZero}
  else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = ⌊z.toReal F⌋}

/-- `trunc(r)`: the integer part of `r` (rounded toward zero). -/
noncomputable def truncR (r : ℝ) : ℤ := if 0 ≤ r then ⌊r⌋ else ⌈r⌉

/-- `ftrunc_N(z)`. -/
noncomputable def ftrunc (F : FloatFormat) (z : FVal) : Set FVal :=
  if z.IsNaN then nans F [z]
  else if z.IsInf ∨ z.IsZero then {z}
  else if 0 < z.toReal F ∧ z.toReal F < 1 then {posZero}
  else if -1 < z.toReal F ∧ z.toReal F < 0 then {negZero}
  else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = truncR (z.toReal F)}

/-- The integer nearest to `r`, ties to the even one. -/
noncomputable def roundEven (r : ℝ) : ℤ :=
  if r - ⌊r⌋ < 1 / 2 then ⌊r⌋
  else if r - ⌊r⌋ > 1 / 2 then ⌈r⌉
  else if ⌊r⌋ % 2 = 0 then ⌊r⌋ else ⌈r⌉

/-- `fnearest_N(z)`. -/
noncomputable def fnearest (F : FloatFormat) (z : FVal) : Set FVal :=
  if z.IsNaN then nans F [z]
  else if z.IsInf ∨ z.IsZero then {z}
  else if 0 < z.toReal F ∧ z.toReal F ≤ 1 / 2 then {posZero}
  else if -1 / 2 ≤ z.toReal F ∧ z.toReal F < 0 then {negZero}
  else {v | v.WF F ∧ v.IsNum ∧ v.toReal F = roundEven (z.toReal F)}

/-- `feq_N(z₁, z₂)`. -/
noncomputable def feq (z₁ z₂ : FVal) : BitVec 32 :=
  if z₁.IsNaN ∨ z₂.IsNaN then 0
  else if z₁.IsZero ∧ z₂.IsZero then 1
  else if z₁ = z₂ then 1 else 0

/-- `fne_N(z₁, z₂)`. -/
noncomputable def fne (z₁ z₂ : FVal) : BitVec 32 :=
  if z₁.IsNaN ∨ z₂.IsNaN then 1
  else if z₁.IsZero ∧ z₂.IsZero then 0
  else if z₁ = z₂ then 0 else 1

/-- `flt_N(z₁, z₂)`. -/
noncomputable def flt (F : FloatFormat) (z₁ z₂ : FVal) : BitVec 32 :=
  if z₁.IsNaN ∨ z₂.IsNaN then 0
  else if z₁ = z₂ then 0
  else if z₁ = inf false then 0
  else if z₁ = inf true then 1
  else if z₂ = inf false then 1
  else if z₂ = inf true then 0
  else if z₁.IsZero ∧ z₂.IsZero then 0
  else if z₁.toReal F < z₂.toReal F then 1 else 0

/-- `fgt_N(z₁, z₂)`. -/
noncomputable def fgt (F : FloatFormat) (z₁ z₂ : FVal) : BitVec 32 :=
  if z₁.IsNaN ∨ z₂.IsNaN then 0
  else if z₁ = z₂ then 0
  else if z₁ = inf false then 1
  else if z₁ = inf true then 0
  else if z₂ = inf false then 0
  else if z₂ = inf true then 1
  else if z₁.IsZero ∧ z₂.IsZero then 0
  else if z₁.toReal F > z₂.toReal F then 1 else 0

/-- `fle_N(z₁, z₂)`. -/
noncomputable def fle (F : FloatFormat) (z₁ z₂ : FVal) : BitVec 32 :=
  if z₁.IsNaN ∨ z₂.IsNaN then 0
  else if z₁ = z₂ then 1
  else if z₁ = inf false then 0
  else if z₁ = inf true then 1
  else if z₂ = inf false then 1
  else if z₂ = inf true then 0
  else if z₁.IsZero ∧ z₂.IsZero then 1
  else if z₁.toReal F ≤ z₂.toReal F then 1 else 0

/-- `fge_N(z₁, z₂)`; the last case follows the spec's equation `bool(z₁ ≥ z₂)` (its prose says
"smaller than or equal", a copy of `fle`). -/
noncomputable def fge (F : FloatFormat) (z₁ z₂ : FVal) : BitVec 32 :=
  if z₁.IsNaN ∨ z₂.IsNaN then 0
  else if z₁ = z₂ then 1
  else if z₁ = inf false then 1
  else if z₁ = inf true then 0
  else if z₂ = inf false then 0
  else if z₂ = inf true then 1
  else if z₁.IsZero ∧ z₂.IsZero then 1
  else if z₁.toReal F ≥ z₂.toReal F then 1 else 0

/-! ## Conversions (§4.3.4) -/

/-- `trunc_u_{M,N}(z)`: `none` (undefined: the instruction traps) on NaN, infinity, or a
truncation outside `[0, 2^N)`. -/
noncomputable def ftruncU (F : FloatFormat) (N : Nat) (z : FVal) : Option (BitVec N) :=
  if z.IsNaN ∨ z.IsInf then none
  else if -1 < truncR (z.toReal F) ∧ truncR (z.toReal F) < 2 ^ N then
    some (BitVec.ofInt N (truncR (z.toReal F)))
  else none

/-- `trunc_s_{M,N}(z)`: `none` on NaN, infinity, or a truncation outside
`[−2^(N−1), 2^(N−1))`. -/
noncomputable def ftruncS (F : FloatFormat) (N : Nat) (z : FVal) : Option (BitVec N) :=
  if z.IsNaN ∨ z.IsInf then none
  else if -(2 ^ (N - 1)) - 1 < truncR (z.toReal F) ∧ truncR (z.toReal F) < 2 ^ (N - 1) then
    some (BitVec.ofInt N (truncR (z.toReal F)))
  else none

/-- `sat_u_N(i)`: `i` clamped to `[0, 2^N − 1]`. -/
def satU (N : Nat) (i : ℤ) : BitVec N :=
  if i < 0 then 0 else if i > 2 ^ N - 1 then BitVec.ofInt N (2 ^ N - 1) else BitVec.ofInt N i

/-- `sat_s_N(i)`: `i` clamped to `[−2^(N−1), 2^(N−1) − 1]`. -/
def satS (N : Nat) (i : ℤ) : BitVec N :=
  if i < -(2 ^ (N - 1)) then BitVec.ofInt N (-(2 ^ (N - 1)))
  else if i > 2 ^ (N - 1) - 1 then BitVec.ofInt N (2 ^ (N - 1) - 1) else BitVec.ofInt N i

/-- `trunc_sat_u_{M,N}(z)`. -/
noncomputable def ftruncSatU (F : FloatFormat) (N : Nat) (z : FVal) : BitVec N :=
  if z.IsNaN then 0
  else if z = inf true then 0
  else if z = inf false then BitVec.ofInt N (2 ^ N - 1)
  else satU N (truncR (z.toReal F))

/-- `trunc_sat_s_{M,N}(z)`. -/
noncomputable def ftruncSatS (F : FloatFormat) (N : Nat) (z : FVal) : BitVec N :=
  if z.IsNaN then 0
  else if z = inf true then BitVec.ofInt N (-(2 ^ (N - 1)))
  else if z = inf false then BitVec.ofInt N (2 ^ (N - 1) - 1)
  else satS N (truncR (z.toReal F))

/-- `promote_{32,64}(z)`: a canonical NaN gives `nans{}` (canonical in the target), another NaN
any arithmetic NaN of the target; a number keeps its exact value. Canonicality is judged in the
source format. -/
noncomputable def fpromote (z : FVal) : Set FVal :=
  if ∃ s, z = nan s f32fmt.canon then nans f64fmt []
  else if z.IsNaN then nans f64fmt [nan false 1]
  else if z.IsInf then {z}
  else {v | v.WF f64fmt ∧ v.IsNum ∧ v.neg = z.neg ∧ v.toReal f64fmt = z.toReal f32fmt}

/-- `demote_{64,32}(z)`: NaNs as for `promote` (judged in the source format); infinities and
zeros keep their sign; other numbers are rounded. -/
noncomputable def fdemote (z : FVal) : Set FVal :=
  if ∃ s, z = nan s f64fmt.canon then nans f32fmt []
  else if z.IsNaN then nans f32fmt [nan false 1]
  else if z.IsInf ∨ z.IsZero then {z}
  else ieee f32fmt (z.toReal f64fmt)

/-- `convert_u_{M,N}(i) = ieee_N(i)`. -/
def fconvertU (F : FloatFormat) {M : Nat} (i : BitVec M) : Set FVal := ieee F i.toNat

/-- `convert_s_{M,N}(i) = ieee_N(signed_M(i))`. -/
def fconvertS (F : FloatFormat) {M : Nat} (i : BitVec M) : Set FVal := ieee F (signed i)

/-! ## Operators on bit patterns (the representation U4 stores) -/

/-- A unary operator on bit patterns. -/
def onBits₁ (F : FloatFormat) (op : FVal → Set FVal) (b : BitVec F.N) : Set (BitVec F.N) :=
  fbits F '' op (ofBits F b)

/-- A binary operator on bit patterns. -/
def onBits₂ (F : FloatFormat) (op : FVal → FVal → Set FVal) (b₁ b₂ : BitVec F.N) :
    Set (BitVec F.N) :=
  fbits F '' op (ofBits F b₁) (ofBits F b₂)

end FVA.Wasm.Num
