import FVA.Spec.Rel.Sort

/-!
# `SortedPerm` checker (verified implementation; contract U9 C1)

Evaluated by the kernel on a certificate's two blobs, so it follows the decoder's kernel-cost
rules: bytes read off the packed numeral with `Nat.land`/`shiftRight`, tests by `bif` on `Bool`
functions, structural recursion, tail calls where a list is long. The parser may accept any
spelling: the checker then reprints the integers and compares the bytes, so soundness never
rests on it.
-/

namespace FVA.Cert

namespace Impl

/-- `a ≤ b` on integers, by cases (no `Decidable` instance to unfold). -/
def intLe : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.ble a b
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc a, .negSucc b => Nat.ble b a

/-- `a = b` on integers, by cases. -/
def intEq : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

/-- Lists of integers equal, elementwise. -/
def listEq : List Int → List Int → Bool
  | [], [] => true
  | a :: as, b :: bs => intEq a b && listEq as bs
  | _, _ => false

/-- Insert `x` before the first element it is at most. -/
def insert (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => bif intLe x y then x :: y :: ys else y :: insert x ys

/-- Insertion sort into an accumulator (tail calls: the kernel never nests one per element). -/
def isort : List Int → List Int → List Int
  | [], acc => acc
  | x :: xs, acc => isort xs (insert x acc)

/-- Integers from `n` bytes packed in `v`: an optional `-`, decimal digits, a line feed each;
`none` on any other byte or a number left open at the end. -/
def parseInts : (n v : Nat) → (neg : Bool) → (val digits : Nat) → (acc : List Int) →
    Option (List Int)
  | 0, _, neg, _, digits, acc => bif !neg && Nat.beq digits 0 then some acc.reverse else none
  | n + 1, v, neg, val, digits, acc =>
    let b := Nat.land v 255
    let v := Nat.shiftRight v 8
    bif Nat.beq b 10 then
      bif Nat.beq digits 0 then none
      else parseInts n v false 0 0 ((bif neg then -(val : Int) else val) :: acc)
    else bif Nat.beq b 45 then
      bif neg || !Nat.beq digits 0 then none else parseInts n v true val digits acc
    else bif Nat.ble 48 b && Nat.ble b 57 then
      parseInts n v neg (val * 10 + (b - 48)) (digits + 1) acc
    else none

/-- The ASCII decimal digits of `n`, most significant first, before `acc` (`fuel` above the
digit count). -/
def digitsOf : (fuel n : Nat) → List UInt8 → List UInt8
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    bif Nat.blt n 10 then (48 + n).toUInt8 :: acc
    else digitsOf fuel (n / 10) ((48 + n % 10).toUInt8 :: acc)

/-- One integer's line: `-` before a negative one, its digits, a line feed. -/
def intText : Int → List UInt8
  | .ofNat n => digitsOf (n + 1) n [10]
  | .negSucc n => 45 :: digitsOf (n + 2) (n + 1) [10]

/-- `bs` are the next bytes of the `n` bytes packed in `v`: the count and numeral after them. -/
def takeBytes : List UInt8 → (n v : Nat) → Option (Nat × Nat)
  | [], n, v => some (n, v)
  | _ :: _, 0, _ => none
  | b :: bs, n + 1, v =>
    bif Nat.beq b.toNat (Nat.land v 255) then takeBytes bs n (Nat.shiftRight v 8) else none

/-- The `n` bytes packed in `v` are exactly the lines of `xs` (one integer at a time: the kernel
never builds the whole text). -/
def printsAs : List Int → (n v : Nat) → Bool
  | [], n, _ => Nat.beq n 0
  | x :: xs, n, v =>
    match takeBytes (intText x) n v with
    | some (n, v) => printsAs xs n v
    | none => false

end Impl

section
open Impl

/-- Both blobs are `IntLines`, and the output's integers are the input's, sorted. -/
def SortedPerm.check (i o : Blob) : Bool :=
  match parseInts i.len i.bytes false 0 0 [], parseInts o.len o.bytes false 0 0 [] with
  | some xs, some ys =>
    printsAs xs i.len i.bytes && printsAs ys o.len o.bytes && listEq (isort xs []) ys
  | _, _ => false

end

end FVA.Cert
