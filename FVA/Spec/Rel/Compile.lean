import FVA.Spec.Rel.Text
import FVA.Spec.Binary.Module
import FVA.Spec.CAbi

/-!
# A toy compiler's outputs (reviewed once; contract U9 B2)

The compiler turns an arithmetic expression over one 32-bit input `x` into a WebAssembly module
exporting `f`, with `f(x)` = the expression's value at `x`. A certificate states this of one
output for every input `x`; the module stays inside a profile (`toyModule`, `ToyValid`) that
WebAssembly validation accepts, so an engine runs the certified binary.
-/

namespace FVA.Cert

open FVA.Wasm FVA.Wasm.Binary FVA.Wasm.Exec

/-- Arithmetic over one 32-bit input `x`. -/
inductive Arith where
  | x
  | const (n : Nat)
  | add (a b : Arith)
  | sub (a b : Arith)
  | mul (a b : Arith)

/-- The expression's value at `x`, wrapped to 32 bits (a constant counts modulo 2^32). -/
def Arith.eval : Arith → BitVec 32 → BitVec 32
  | .x, v => v
  | .const n, _ => BitVec.ofNat 32 n
  | .add a b, v => a.eval v + b.eval v
  | .sub a b, v => a.eval v - b.eval v
  | .mul a b, v => a.eval v * b.eval v

/-- The expression as ASCII text, fully parenthesized: `x`, decimal constants, `(a+b)`,
`(a-b)`, `(a*b)`. -/
def Arith.text : Arith → List UInt8
  | .x => [120]
  | .const n => decimal n
  | .add a b => [40] ++ a.text ++ [43] ++ b.text ++ [41]
  | .sub a b => [40] ++ a.text ++ [45] ++ b.text ++ [41]
  | .mul a b => [40] ++ a.text ++ [42] ++ b.text ++ [41]

/-- The compiler's module: one function of type `[i32] → [i32]` with no declared locals and
the given body, exported as `f`, and nothing else. -/
def toyModule (body : List Instr) : Module :=
  { types := [⟨[.num .i32], [.num .i32]⟩], funcs := [{ type := 0, locals := [], body }],
    exports := [⟨"f", .func 0⟩] }

/-- The stack height after `body` from height `h`: `local.get 0` and an in-range `i32.const`
push one value, `i32.add`, `i32.sub` and `i32.mul` pop two and push one; any other instruction,
or an operator without two values, leaves the profile (`none`). -/
def toyHeight : List Instr → Nat → Option Nat
  | [], h => some h
  | .localGet 0 :: rest, h => toyHeight rest (h + 1)
  | .iconst .w32 n :: rest, h => if n < 2 ^ 32 then toyHeight rest (h + 1) else none
  | .ibinop .w32 .add :: rest, h | .ibinop .w32 .sub :: rest, h | .ibinop .w32 .mul :: rest, h =>
    if 2 ≤ h then toyHeight rest (h - 1) else none
  | _, _ => none

/-- The body stays in the profile and ends with exactly one value: what WebAssembly validation
asks of a function of type `[i32] → [i32]` built from these instructions. -/
def ToyValid (body : List Instr) : Prop := toyHeight body 0 = some 1

/-- The output encodes the toy compiler's module for the input expression: the input is the
expression's text and a line feed, the output is the binary encoding (`ModuleB`) of a valid
`toyModule`, and its `f` returns the expression's value for every 32-bit `x`. -/
def Compiled (i o : List UInt8) : Prop :=
  ∃ (e : Arith) (body : List Instr), i = e.text ++ [10] ∧ ModuleB (toyModule body) o ∧
    ToyValid body ∧ ∀ x : BitVec 32, Returns (toyModule body) "f" [.i32 x] [.i32 (e.eval x)]

end FVA.Cert
