import FVA.Spec.Numerics.Float

/-!
# WAST literals and seeded generators

Exact WAST literals for numbers (floats as hex floats or NaN payloads) and a splitmix64
generator with boundary-biased operand choices, shared by the float differential test and
`fva difftest`.
-/

namespace FVA.Tool.Wast

open FVA.Wasm.Num

/-- splitmix64 state. -/
abbrev Gen := StateM UInt64

/-- The next 64 random bits. -/
def next : Gen UInt64 := do
  let s := (← get) + 0x9E3779B97F4A7C15
  set s
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  return z ^^^ (z >>> 31)

/-- A random natural below `n` (`n > 0`). -/
def below (n : Nat) : Gen Nat := do
  let a ← next
  let b ← next
  return (a.toNat * 2 ^ 64 + b.toNat) % n

/-- Boundary bit patterns of a format, positive and negative. -/
def specials (F : FloatFormat) : List Nat :=
  let bias := 2 ^ (F.E - 1) - 1
  let inf := (2 ^ F.E - 1) * 2 ^ F.M
  let pos := [0, 1, 2, 2 ^ F.M - 1, 2 ^ F.M, 2 ^ F.M + 1, inf - 1, inf - 2, inf, inf + F.canon,
    inf + F.canon + 1, inf + 1, inf + 2 ^ F.M - 1, bias * 2 ^ F.M, bias * 2 ^ F.M + 1,
    bias * 2 ^ F.M - 1, (bias + 1) * 2 ^ F.M, (bias - 1) * 2 ^ F.M,
    (bias - 1) * 2 ^ F.M + 2 ^ (F.M - 1),
    (bias + F.M) * 2 ^ F.M, (bias + F.M + 1) * 2 ^ F.M - 1]
  pos ++ pos.map (· + 2 ^ (F.E + F.M))

/-- A boundary-biased operand; `near` = another operand whose exponent it may share. -/
def operand (F : FloatFormat) (near : Option Nat) : Gen Nat := do
  let sign := (← below 2) * 2 ^ (F.E + F.M)
  let bias := 2 ^ (F.E - 1) - 1
  match ← below 10 with
  | 0 | 1 => let s := specials F; return s[← below s.length]!
  | 2 | 3 => return sign + (← below (2 ^ F.M))
  | 4 | 5 => return ← below (2 ^ (1 + F.E + F.M))
  | 6 | 7 => return sign + (bias - 30 + (← below 61)) * 2 ^ F.M + (← below (2 ^ F.M))
  | _ => match near with
    | some b =>
      -- a quarter of these are ±b exactly (cancellation, equality)
      if (← below 4) = 0 then return b % 2 ^ (F.E + F.M) + sign
      let e := b / 2 ^ F.M % 2 ^ F.E
      let up ← below 2
      let k ← below (F.M + 4)
      let e' := if up = 0 then min (2 ^ F.E - 2) (e + k) else e - min e k
      let low := ← below (2 ^ (← below (F.M + 1)))
      return sign + e' * 2 ^ F.M + (b % 2 ^ F.M ^^^ low)
    | none => return ← below (2 ^ (1 + F.E + F.M))

/-- Integer operands for conversions: boundary values, then random bits. -/
def intOperand (N : Nat) : Gen Nat := do
  if (← below 4) = 0 then
    let s := [0, 1, 2, 2 ^ (N - 1) - 1, 2 ^ (N - 1), 2 ^ (N - 1) + 1, 2 ^ N - 1, 2 ^ N - 2,
      2 ^ 24 - 1, 2 ^ 24 + 1, 2 ^ 53 - 1, 2 ^ 53 + 1, 2 ^ 63 - 1].map (· % 2 ^ N)
    return s[← below s.length]!
  else
    let k ← below (N + 1)
    return ← below (2 ^ k)

/-- `n` as exactly `w` hex digits. -/
def hex (n w : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- An exact WAST float literal of a bit pattern. -/
def lit (F : FloatFormat) (b : Nat) : String :=
  let sg := if b / 2 ^ (F.E + F.M) % 2 = 1 then "-" else ""
  let e := b / 2 ^ F.M % 2 ^ F.E
  let m := b % 2 ^ F.M
  let bias := 2 ^ (F.E - 1) - 1
  -- hex digits hold the significand left-aligned: 23 bits → 6 digits, 52 bits → 13 digits
  let digits := (F.M + 3) / 4
  let frac := hex (m * 2 ^ (4 * digits - F.M)) digits
  if e = 2 ^ F.E - 1 then
    if m = 0 then sg ++ "inf" else sg ++ "nan:0x" ++ hex m 1
  else if e = 0 then s!"{sg}0x0.{frac}p-{bias - 1}"
  else if e ≥ bias then s!"{sg}0x1.{frac}p+{e - bias}"
  else s!"{sg}0x1.{frac}p-{bias - e}"

/-- A NaN payload of a bit pattern (`none` for other values). -/
def payload (F : FloatFormat) (b : Nat) : Option Nat :=
  if b / 2 ^ F.M % 2 ^ F.E = 2 ^ F.E - 1 ∧ b % 2 ^ F.M ≠ 0 then some (b % 2 ^ F.M) else none

end FVA.Tool.Wast
