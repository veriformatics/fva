/-! Mutation-check fixture (U12 E1): one site per operator spelling, every exclusion, Unicode
offsets and a zero-site declaration; `ops.expected` = the reviewed listing. -/

namespace Fix.Ops

def ror (a b : Nat) : Bool :=
  decide (a < b) && decide (a ≤ b) && decide (b > a) && decide (b ≥ a) && Nat.blt a b &&
    Nat.ble a b && Nat.beq a b

def eqn (a b : Nat) : Bool := (a == b || a != b) && decide (a = b) && decide (a ≠ b)

def lcr (p q : Bool) : Bool := (p && q || !p) && decide (p = q ∧ p = true ∨ q = false)

def aor (a b : Nat) : Nat :=
  a + b - a * b / (b % 3) + Nat.add a b + Nat.sub a b + Nat.mul a b + Nat.div a b +
    Nat.mod a b + min a b + max a b

def idiv (x y : Int) : Int := x.tdiv y + Int.fdiv x y + x.tmod y + Int.fmod x y + x.ediv y +
  x.emod y + (x + y).tdiv y

def bit (a b : Nat) : Nat :=
  (a &&& b) ||| (a ^^^ b) ||| (a <<< 1) ||| (a >>> 1) ||| Nat.land a b ||| Nat.lor a b |||
    Nat.xor a b ||| Nat.shiftLeft a 1 ||| Nat.shiftRight a 1

def lit : Nat := 0 + 1 + 0x1f + 0b10 + 0o7 + 41

def gib (b : Bool) (n : Nat) : Nat :=
  (if b then n else 0) + (bif b then 1 else 2) + (if _h : n = 0 then 3 else 4)

def gme : Nat → Nat
  | 0 => 10
  | 1 => 11
  | _ => 12

def lst (xs : List Nat) : List Nat := (1 :: xs) ++ [2, 3] ++ xs.reverse ++ List.reverse xs

def opt (n : Nat) : Option Nat := if n = 0 then some n else Option.some 1

def neg (i : Int) : Int := -i + -(i + 1)

/-- Excluded: this docstring's `1 + 2`, the signature, patterns, the string, the ascription
type, the `by` block; kept: the ascribed terms. -/
def excl (n : Nat) (_h : n + 1 > 0 := by omega) : Nat :=
  match n with
  | k + 1 => (k : Nat) + ("5 + 6".length : Nat) +
      (⟨k, by have : k < k + 1 + 1 := by omega
              exact this⟩ : Fin (k + 2)).val
  | 0 => (0 : Nat)
-- 7 + 8 is a comment

def zero (n : Nat) : Nat := n

def uni (α₁ : Nat) : Nat := α₁ + 1

theorem thm : (1 : Nat) + 1 = 2 := rfl

end Fix.Ops
