import FVA.Spec.Rel.Compile
import FVA.Impl.Cert.Sort
import FVA.Impl.Decode

/-!
# `Compiled` checker (verified implementation; contract U9 C1)

Kernel-evaluated on a certificate's two blobs. The input is parsed by any means, then reprinted
and compared byte for byte (soundness never rests on the parser); the output is decoded by the
verified decoder, checked against the toy profile, and evaluated symbolically: the body's stack
of expression trees must end as the parsed expression (constants compared modulo 2^32). Sound
and intentionally incomplete: `x + 0` compiled to `local.get 0` is rejected.
-/

namespace FVA.Cert

open FVA.Wasm

namespace Impl

/-- A parse result: the value, then the count and numeral of the bytes after it. -/
abbrev PRes (α : Type) := Option (α × Nat × Nat)

/-- A decimal number's digits (at least one) from the packed input. -/
def parseNat : (fuel n v acc digits : Nat) → PRes Nat
  | 0, _, _, _, _ => none
  | fuel + 1, n, v, acc, digits =>
    match n with
    | 0 => bif Nat.beq digits 0 then none else some (acc, 0, v)
    | n' + 1 =>
      let b := Nat.land v 255
      bif Nat.ble 48 b && Nat.ble b 57 then
        parseNat fuel n' (Nat.shiftRight v 8) (acc * 10 + (b - 48)) (digits + 1)
      else bif Nat.beq digits 0 then none else some (acc, n, v)

/-- `x`, a decimal constant, or `(a op b)` with `op` in `+ - *`. -/
def parseArith : (fuel n v : Nat) → PRes Arith
  | 0, _, _ => none
  | fuel + 1, n, v =>
    match n with
    | 0 => none
    | n' + 1 =>
      let b := Nat.land v 255
      let v' := Nat.shiftRight v 8
      bif Nat.beq b 120 then some (.x, n', v')
      else bif Nat.beq b 40 then
        match parseArith fuel n' v' with
        | some (a, n₁, v₁) =>
          match n₁ with
          | 0 => none
          | n₂ + 1 =>
            let op := Nat.land v₁ 255
            match parseArith fuel n₂ (Nat.shiftRight v₁ 8) with
            | some (c, n₃, v₃) =>
              match n₃ with
              | 0 => none
              | n₄ + 1 =>
                bif Nat.beq (Nat.land v₃ 255) 41 then
                  let rest := Nat.shiftRight v₃ 8
                  bif Nat.beq op 43 then some (.add a c, n₄, rest)
                  else bif Nat.beq op 45 then some (.sub a c, n₄, rest)
                  else bif Nat.beq op 42 then some (.mul a c, n₄, rest)
                  else none
                else none
            | none => none
        | none => none
      else (parseNat (n + 1) n v 0 0).map fun (k, n, v) => (.const k, n, v)

/-- The expression's text, digits by `digitsOf`. -/
def arithText : Arith → List UInt8
  | .x => [120]
  | .const k => digitsOf (k + 1) k []
  | .add a b => [40] ++ arithText a ++ [43] ++ arithText b ++ [41]
  | .sub a b => [40] ++ arithText a ++ [45] ++ arithText b ++ [41]
  | .mul a b => [40] ++ arithText a ++ [42] ++ arithText b ++ [41]

/-- Expression trees equal, constants modulo 2^32. -/
def arithEq : Arith → Arith → Bool
  | .x, .x => true
  | .const a, .const b => Nat.beq (a % 4294967296) (b % 4294967296)
  | .add a b, .add c d | .sub a b, .sub c d | .mul a b, .mul c d => arithEq a c && arithEq b d
  | _, _ => false

/-- Symbolic run of a toy body on a stack of trees (top first). -/
def symRun : List Instr → List Arith → Option (List Arith)
  | [], st => some st
  | .localGet 0 :: rest, st => symRun rest (.x :: st)
  | .iconst .w32 n :: rest, st => symRun rest (.const n :: st)
  | .ibinop .w32 .add :: rest, b :: a :: st => symRun rest (.add a b :: st)
  | .ibinop .w32 .sub :: rest, b :: a :: st => symRun rest (.sub a b :: st)
  | .ibinop .w32 .mul :: rest, b :: a :: st => symRun rest (.mul a b :: st)
  | _, _ => none

/-- The decoded module is `toyModule` of its one body (`some body`). -/
def toyBody (m : Module) : Option (List Instr) :=
  match m.funcs with
  | [f] =>
    bif decide (m.types = [⟨[.num .i32], [.num .i32]⟩]) && Nat.beq f.type 0 && f.locals.isEmpty &&
        m.tables.isEmpty && m.mems.isEmpty && m.globals.isEmpty && m.elems.isEmpty &&
        m.datas.isEmpty && m.start.isNone && m.imports.isEmpty &&
        decide (m.exports = [⟨"f", .func 0⟩]) then some f.body
    else none
  | _ => none

end Impl

section
open Impl

/-- The input is an expression's text and a line feed, the output a valid `toyModule` whose
body evaluates symbolically to that expression. -/
def Compiled.check (i o : Blob) : Bool :=
  match parseArith (i.len + 1) i.len i.bytes with
  | some (e, _, _) =>
    match takeBytes (arithText e ++ [10]) i.len i.bytes with
    | some (0, _) =>
      bif Nat.blt o.bytes (2 ^ (8 * o.len)) then
        match Decode.decode o.bytes o.len with
        | .ok m =>
          match toyBody m with
          | some body =>
            bif decide (toyHeight body 0 = some 1) then
              match symRun body [] with
              | some [t] => arithEq t e
              | _ => false
            else false
          | none => false
        | .error _ => false
      else false
    | _ => false
  | none => false

end

end FVA.Cert
