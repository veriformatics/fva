import FVA.Spec.Syntax
import FVA.Spec.Binary.Leb

/-!
# Values and types in the binary format (reviewed spec)

Spec §5.1–§5.3. Every relation `R a bs` reads: the complete byte list `bs` encodes `a`.
-/

namespace FVA.Wasm.Binary

open FVA.Wasm

/-- Concatenated encodings of a list, each element by `R` (no length prefix). -/
inductive Seq {α : Type} (R : α → List UInt8 → Prop) : List α → List UInt8 → Prop where
  | nil : Seq R [] []
  | cons {a : α} {as : List α} {b₁ b₂ : List UInt8} (ha : R a b₁) (hs : Seq R as b₂) :
      Seq R (a :: as) (b₁ ++ b₂)

/-- `vec(B)`: a `u32` element count followed by the elements (spec §5.1.3). -/
def Vec {α : Type} (R : α → List UInt8 → Prop) (xs : List α) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, ULeb 32 xs.length b₁ ∧ Seq R xs b₂ ∧ bs = b₁ ++ b₂

/-- A single byte stands for itself. -/
def Byte (x : UInt8) (bs : List UInt8) : Prop := bs = [x]

/-- `name`: `vec(byte)` holding exactly the UTF-8 encoding of the string (spec §5.2.4). -/
def Name (s : String) (bs : List UInt8) : Prop := Vec Byte s.toUTF8.toList bs

/-- Little-endian bytes of the low `8·k` bits of `n`. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: leBytes k (n / 256)

/-- `f32`/`f64` constants: IEEE-754 bits, little-endian (spec §5.2.3). -/
def FloatBits (w : Width) (bits : Nat) (bs : List UInt8) : Prop :=
  let k := match w with | .w32 => 4 | .w64 => 8
  bits < 2 ^ (8 * k) ∧ bs = leBytes k bits

/-- Number types (spec §5.3.1). -/
def NumTypeB : NumType → List UInt8 → Prop
  | .i32, bs => bs = [0x7F]
  | .i64, bs => bs = [0x7E]
  | .f32, bs => bs = [0x7D]
  | .f64, bs => bs = [0x7C]

/-- Reference types (spec §5.3.3). -/
def RefTypeB : RefType → List UInt8 → Prop
  | .funcref, bs => bs = [0x70]
  | .externref, bs => bs = [0x6F]

/-- Value types (spec §5.3.4). -/
def ValTypeB : ValType → List UInt8 → Prop
  | .num t, bs => NumTypeB t bs
  | .ref t, bs => RefTypeB t bs

/-- Result types: `vec(valtype)` (spec §5.3.5). -/
def ResultTypeB (ts : List ValType) (bs : List UInt8) : Prop := Vec ValTypeB ts bs

/-- Function types: `0x60 rt₁ rt₂` (spec §5.3.6). -/
def FuncTypeB (ft : FuncType) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, ResultTypeB ft.params b₁ ∧ ResultTypeB ft.results b₂ ∧
    bs = ([0x60] : List UInt8) ++ b₁ ++ b₂

/-- Limits (spec §5.3.7). -/
def LimitsB (l : Limits) (bs : List UInt8) : Prop :=
  match l.max with
  | none => ∃ b, ULeb 32 l.min b ∧ bs = ([0x00] : List UInt8) ++ b
  | some m => ∃ b₁ b₂, ULeb 32 l.min b₁ ∧ ULeb 32 m b₂ ∧
      bs = ([0x01] : List UInt8) ++ b₁ ++ b₂

/-- Table types: `reftype limits` (spec §5.3.9). -/
def TableTypeB (t : TableType) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, RefTypeB t.elem b₁ ∧ LimitsB t.limits b₂ ∧ bs = b₁ ++ b₂

/-- Global types: `valtype mut` with `0x00` const, `0x01` var (spec §5.3.10). -/
def GlobalTypeB (g : GlobalType) (bs : List UInt8) : Prop :=
  ∃ b, ValTypeB g.val b ∧
    bs = b ++ [(match g.mutability with | .const => 0x00 | .var => 0x01 : UInt8)]

end FVA.Wasm.Binary
