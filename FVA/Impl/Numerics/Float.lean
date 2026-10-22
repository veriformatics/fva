import FVA.Spec.Numerics.Float

/-!
# Executable float operations

Computes each operator of `FVA.Spec.Numerics.Float` on `FVal`s with natural-number arithmetic:
exact results are dyadic rationals `±(n / d)·2^e`, rounded once by `roundDyadic` (round to
nearest, ties to even, at the ulp of the result's binade). NaN results pick one member of the
spec's set: the canonical NaN when every NaN input is canonical, else the first NaN input's
payload with its top bit set. `FVA.Proof.Numerics` proves each result is allowed by the spec.
Kernel-shaped (see `FVA.Impl.Decode.Reader`): tests are `bif` on `Nat.blt`/`Nat.beq`.
-/

namespace FVA.Wasm.Num.Impl

open FVal

variable (F : FloatFormat)

/-- `⌊log₂(n / d)⌋` for `n, d > 0`. -/
def log2Frac (n d : Nat) : Int :=
  let a := Nat.log2 n
  let b := Nat.log2 d
  -- n / d lies in (2^(a−b−1), 2^(a−b+1)): it is a − b exactly when n·2^b' ≥ d·2^a'
  bif Nat.blt (n * 2 ^ (b - a)) (d * 2 ^ (a - b)) then (a : Int) - b - 1 else (a : Int) - b

/-- Round-half-even of `num / den` (`den > 0`) from the quotient and the remainder. -/
def rneDiv (num den : Nat) : Nat :=
  let m₀ := num / den
  let r := num % den
  bif Nat.blt (2 * r) den then m₀ else bif Nat.blt den (2 * r) then m₀ + 1 else m₀ + m₀ % 2

/-- The float `±m·2^q` for a rounded significand `m` at ulp exponent `q`: `±∞` once `m·2^q`
reaches `limit_N = 2^(emax + 1)`, subnormal below `2^M`, else normal (`m = 2^(M+1)` carries into
the next binade). -/
def encode (s : Bool) (m : Nat) (q : Int) : FVal :=
  bif Nat.blt 0 m && decide (((2 ^ (F.E - 1) : Nat) : Int) ≤ q + Nat.log2 m) then inf s
  else bif Nat.blt m (2 ^ F.M) then subnormal s m
  else bif Nat.blt m (2 ^ (F.M + 1)) then normal s (m - 2 ^ F.M) (q + F.M)
  else normal s 0 (q + F.M + 1)

/-- Round `(n / d)·2^e` (`n, d > 0`) to `F`, ties to even; `s` = negative. Returns the value
`gridRound` gives. -/
def roundDyadic (s : Bool) (n d : Nat) (e : Int) : FVal :=
  let q := max (log2Frac n d + e) F.emin - F.M
  let t := e - q
  -- (n / d)·2^e / 2^q = num / den (one of the two powers is 2^0)
  encode F s (rneDiv (n * 2 ^ t.toNat) (d * 2 ^ (-t).toNat)) q

/-! ## Classification and decomposition -/

/-- `IsNaN`, decided. -/
def isNaN : FVal → Bool
  | nan _ _ => true
  | _ => false

/-- `IsInf`, decided. -/
def isInf : FVal → Bool
  | inf _ => true
  | _ => false

/-- `IsZero`, decided. -/
def isZero : FVal → Bool
  | subnormal _ m => Nat.beq m 0
  | _ => false

/-- A number's magnitude is `sig·2^ex`: normal `(2^M + m)·2^(e − M)`, subnormal
`m·2^(emin − M)`. -/
def sig : FVal → Nat
  | normal _ m _ => 2 ^ F.M + m
  | subnormal _ m => m
  | _ => 0

/-- See `sig`. -/
def ex : FVal → Int
  | normal _ _ e => e - F.M
  | _ => F.emin - F.M

/-- A number's signed value in units of `2^e` (`e ≤ ex`). -/
def units (z : FVal) (e : Int) : Int :=
  let u : Int := sig F z * 2 ^ (ex F z - e).toNat
  bif z.neg then -u else u

/-- `toReal z₁ < toReal z₂` for numbers, decided on the grid of the smaller exponent. -/
def ltNum (z₁ z₂ : FVal) : Bool :=
  let e := min (ex F z₁) (ex F z₂)
  decide (units F z₁ e < units F z₂ e)

/-- `toReal z₁ ≤ toReal z₂` for numbers. -/
def leNum (z₁ z₂ : FVal) : Bool := !ltNum F z₂ z₁

/-! ## NaN results -/

/-- The NaN an operator returns: the first NaN input with its payload's top bit set, else the
positive canonical NaN; an element of `nans F zs` for well-formed inputs. -/
def nanOf : List FVal → FVal
  | [] => nan false F.canon
  | nan s n :: _ => nan s (Nat.lor n F.canon)
  | _ :: zs => nanOf zs

/-! ## Arithmetic (case order of `FVA.Spec.Numerics.Float`) -/

/-- The rounded exact sum of two nonzero numbers; `+0` when they cancel. -/
def addNum (z₁ z₂ : FVal) : FVal :=
  let e := min (ex F z₁) (ex F z₂)
  match units F z₁ e + units F z₂ e with
  | .ofNat n => bif Nat.beq n 0 then posZero else roundDyadic F false n 1 e
  | .negSucc n => roundDyadic F true (n + 1) 1 e

/-- `fadd_N`. -/
def fadd (z₁ z₂ : FVal) : FVal :=
  bif isNaN z₁ || isNaN z₂ then nanOf F [z₁, z₂]
  else bif isInf z₁ && isInf z₂ && z₁.neg != z₂.neg then nanOf F []
  else bif isInf z₁ then z₁
  else bif isInf z₂ then z₂
  else bif isZero z₁ && isZero z₂ && z₁.neg != z₂.neg then posZero
  else bif isZero z₁ then z₂
  else bif isZero z₂ then z₁
  else addNum F z₁ z₂

/-- `fsub_N`: the spec's cases are those of `fadd_N` with `z₂` negated. -/
def fsub (z₁ z₂ : FVal) : FVal := fadd F z₁ (fneg z₂)

/-- `fmul_N`. -/
def fmul (z₁ z₂ : FVal) : FVal :=
  let s := z₁.neg != z₂.neg
  bif isNaN z₁ || isNaN z₂ then nanOf F [z₁, z₂]
  else bif (isZero z₁ && isInf z₂) || (isInf z₁ && isZero z₂) then nanOf F []
  else bif isInf z₁ || isInf z₂ then inf s
  else bif isZero z₁ || isZero z₂ then subnormal s 0
  else roundDyadic F s (sig F z₁ * sig F z₂) 1 (ex F z₁ + ex F z₂)

/-- `fdiv_N`. -/
def fdiv (z₁ z₂ : FVal) : FVal :=
  let s := z₁.neg != z₂.neg
  bif isNaN z₁ || isNaN z₂ then nanOf F [z₁, z₂]
  else bif isInf z₁ && isInf z₂ then nanOf F []
  else bif isZero z₁ && isZero z₂ then nanOf F [z₁, z₂]
  else bif isInf z₁ then inf s
  else bif isInf z₂ then subnormal s 0
  else bif isZero z₁ then subnormal s 0
  else bif isZero z₂ then inf s
  else roundDyadic F s (sig F z₁) (sig F z₂) (ex F z₁ - ex F z₂)

/-- `fmin_N`. -/
def fmin (z₁ z₂ : FVal) : FVal :=
  bif isNaN z₁ || isNaN z₂ then nanOf F [z₁, z₂]
  else bif (isInf z₁ && z₁.neg) || (isInf z₂ && z₂.neg) then inf true
  else bif isInf z₁ then z₂
  else bif isInf z₂ then z₁
  else bif isZero z₁ && isZero z₂ && z₁.neg != z₂.neg then negZero
  else bif leNum F z₁ z₂ then z₁ else z₂

/-- `fmax_N`. -/
def fmax (z₁ z₂ : FVal) : FVal :=
  bif isNaN z₁ || isNaN z₂ then nanOf F [z₁, z₂]
  else bif (isInf z₁ && !z₁.neg) || (isInf z₂ && !z₂.neg) then inf false
  else bif isInf z₁ then z₂
  else bif isInf z₂ then z₁
  else bif isZero z₁ && isZero z₂ && z₁.neg != z₂.neg then posZero
  else bif leNum F z₂ z₁ then z₁ else z₂

/-- `⌊√n⌋` digit by digit, correct once `n < 4^fuel`: `⌊√n⌋` is `2⌊√(n/4)⌋` or one more. -/
def isqrtAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    let r := 2 * isqrtAux fuel (n / 4)
    bif Nat.blt n ((r + 1) * (r + 1)) then r else r + 1

/-- `⌊√n⌋`. -/
def isqrt (n : Nat) : Nat := isqrtAux (Nat.log2 n / 2 + 1) n

/-- The rounded square root of a positive number `sig·2^ex = a·4^h` (`a = sig·2^(ex mod 2)`):
`√(a·4^k)·2^(h−k)` with `k = M + 2`, so the integer root `r ≥ 2^(M+2)` is finer than half an
ulp; an inexact root lies strictly between `r` and `r + 1`, where no rounding boundary falls, and
rounds as `r + 1/2`. -/
def sqrtNum (z : FVal) : FVal :=
  let e := ex F z
  let p := e % 2
  let h := (e - p) / 2
  let k := F.M + 2
  let n := sig F z * 2 ^ p.toNat * 4 ^ k
  let r := isqrt n
  bif Nat.beq (r * r) n then roundDyadic F false r 1 (h - k)
  else roundDyadic F false (2 * r + 1) 2 (h - k)

/-- `fsqrt_N`. -/
def fsqrt (z : FVal) : FVal :=
  bif isNaN z then nanOf F [z]
  else bif isInf z && z.neg then nanOf F []
  else bif isInf z then inf false
  else bif isZero z then z
  else bif z.neg then nanOf F []
  else sqrtNum F z

/-! ## Integral rounding -/

/-- The integral result of a nonzero number with magnitude `sig·2^ex`: unchanged when `ex ≥ 0`,
else the magnitude `k` that `pick i f d` chooses from the integer part `i`, the fraction `f / d`
and the sign; `k = 0` gives the zero of the input's sign. -/
def roundIntegral (pick : Bool → Nat → Nat → Nat → Nat) (z : FVal) : FVal :=
  match ex F z with
  | .ofNat _ => z
  | .negSucc j =>
    let d := 2 ^ (j + 1)
    let a := sig F z
    let k := pick z.neg (a / d) (a % d) d
    bif Nat.beq k 0 then subnormal z.neg 0 else roundDyadic F z.neg k 1 0

/-- `fceil_N`. -/
def fceil (z : FVal) : FVal :=
  bif isNaN z then nanOf F [z]
  else bif isInf z || isZero z then z
  else roundIntegral F (fun s i f _ => bif !s && Nat.blt 0 f then i + 1 else i) z

/-- `ffloor_N`. -/
def ffloor (z : FVal) : FVal :=
  bif isNaN z then nanOf F [z]
  else bif isInf z || isZero z then z
  else roundIntegral F (fun s i f _ => bif s && Nat.blt 0 f then i + 1 else i) z

/-- `ftrunc_N`. -/
def ftrunc (z : FVal) : FVal :=
  bif isNaN z then nanOf F [z]
  else bif isInf z || isZero z then z
  else roundIntegral F (fun _ i _ _ => i) z

/-- `fnearest_N`. -/
def fnearest (z : FVal) : FVal :=
  bif isNaN z then nanOf F [z]
  else bif isInf z || isZero z then z
  else roundIntegral F (fun _ i f d => rneDiv (i * d + f) d) z

/-! ## Comparisons -/

/-- `feq_N`. -/
def feq (z₁ z₂ : FVal) : BitVec 32 :=
  bif isNaN z₁ || isNaN z₂ then 0
  else bif isZero z₁ && isZero z₂ then 1
  else bif decide (z₁ = z₂) then 1 else 0

/-- `fne_N`. -/
def fne (z₁ z₂ : FVal) : BitVec 32 :=
  bif isNaN z₁ || isNaN z₂ then 1
  else bif isZero z₁ && isZero z₂ then 0
  else bif decide (z₁ = z₂) then 0 else 1

/-- `flt_N`. -/
def flt (z₁ z₂ : FVal) : BitVec 32 :=
  bif isNaN z₁ || isNaN z₂ then 0
  else bif decide (z₁ = z₂) then 0
  else bif isInf z₁ && !z₁.neg then 0
  else bif isInf z₁ then 1
  else bif isInf z₂ && !z₂.neg then 1
  else bif isInf z₂ then 0
  else bif isZero z₁ && isZero z₂ then 0
  else bif ltNum F z₁ z₂ then 1 else 0

/-- `fgt_N`. -/
def fgt (z₁ z₂ : FVal) : BitVec 32 :=
  bif isNaN z₁ || isNaN z₂ then 0
  else bif decide (z₁ = z₂) then 0
  else bif isInf z₁ && !z₁.neg then 1
  else bif isInf z₁ then 0
  else bif isInf z₂ && !z₂.neg then 0
  else bif isInf z₂ then 1
  else bif isZero z₁ && isZero z₂ then 0
  else bif ltNum F z₂ z₁ then 1 else 0

/-- `fle_N`. -/
def fle (z₁ z₂ : FVal) : BitVec 32 :=
  bif isNaN z₁ || isNaN z₂ then 0
  else bif decide (z₁ = z₂) then 1
  else bif isInf z₁ && !z₁.neg then 0
  else bif isInf z₁ then 1
  else bif isInf z₂ && !z₂.neg then 1
  else bif isInf z₂ then 0
  else bif isZero z₁ && isZero z₂ then 1
  else bif leNum F z₁ z₂ then 1 else 0

/-- `fge_N`. -/
def fge (z₁ z₂ : FVal) : BitVec 32 :=
  bif isNaN z₁ || isNaN z₂ then 0
  else bif decide (z₁ = z₂) then 1
  else bif isInf z₁ && !z₁.neg then 1
  else bif isInf z₁ then 0
  else bif isInf z₂ && !z₂.neg then 0
  else bif isInf z₂ then 1
  else bif isZero z₁ && isZero z₂ then 1
  else bif leNum F z₂ z₁ then 1 else 0

/-! ## Conversions -/

/-- `trunc(z)` of a number, toward zero. -/
def truncInt (z : FVal) : Int :=
  let k : Nat := match ex F z with
    | .ofNat j => sig F z * 2 ^ j
    | .negSucc j => sig F z / 2 ^ (j + 1)
  bif z.neg then -(k : Int) else k

/-- `trunc_u_{M,N}`. -/
def ftruncU (N : Nat) (z : FVal) : Option (BitVec N) :=
  bif isNaN z || isInf z then none
  else
    let t := truncInt F z
    bif decide (-1 < t) && decide (t < 2 ^ N) then some (BitVec.ofInt N t) else none

/-- `trunc_s_{M,N}`. -/
def ftruncS (N : Nat) (z : FVal) : Option (BitVec N) :=
  bif isNaN z || isInf z then none
  else
    let t := truncInt F z
    bif decide (-(2 ^ (N - 1)) - 1 < t) && decide (t < 2 ^ (N - 1)) then some (BitVec.ofInt N t)
    else none

/-- `trunc_sat_u_{M,N}`. -/
def ftruncSatU (N : Nat) (z : FVal) : BitVec N :=
  bif isNaN z then 0
  else bif isInf z && z.neg then 0
  else bif isInf z then BitVec.ofInt N (2 ^ N - 1)
  else satU N (truncInt F z)

/-- `trunc_sat_s_{M,N}`. -/
def ftruncSatS (N : Nat) (z : FVal) : BitVec N :=
  bif isNaN z then 0
  else bif isInf z && z.neg then BitVec.ofInt N (-(2 ^ (N - 1)))
  else bif isInf z then BitVec.ofInt N (2 ^ (N - 1) - 1)
  else satS N (truncInt F z)

/-- The float nearest to the integer `i`. -/
def ofInt (i : Int) : FVal :=
  match i with
  | .ofNat n => bif Nat.beq n 0 then posZero else roundDyadic F false n 1 0
  | .negSucc n => roundDyadic F true (n + 1) 1 0

/-- `convert_u_{M,N}`. -/
def fconvertU {M : Nat} (i : BitVec M) : FVal := ofInt F i.toNat

/-- `convert_s_{M,N}`. -/
def fconvertS {M : Nat} (i : BitVec M) : FVal := ofInt F (signed i)

/-- `promote_{32,64}`: the payload shifted into the wider field with its top bit set (a
canonical NaN stays canonical); numbers exactly. -/
def fpromote (z : FVal) : FVal :=
  match z with
  | nan s n => nan s (Nat.lor (n * 2 ^ (f64fmt.M - f32fmt.M)) f64fmt.canon)
  | inf s => inf s
  | z => bif isZero z then z else roundDyadic f64fmt z.neg (sig f32fmt z) 1 (ex f32fmt z)

/-- `demote_{64,32}`: the payload's high bits with the top bit set; numbers rounded. -/
def fdemote (z : FVal) : FVal :=
  match z with
  | nan s n => nan s (Nat.lor (n / 2 ^ (f64fmt.M - f32fmt.M)) f32fmt.canon)
  | inf s => inf s
  | z => bif isZero z then z else roundDyadic f32fmt z.neg (sig f64fmt z) 1 (ex f64fmt z)

end FVA.Wasm.Num.Impl
