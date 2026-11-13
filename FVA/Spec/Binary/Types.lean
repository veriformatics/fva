import FVA.Spec.Syntax
import FVA.Spec.Binary.Leb

/-!
# Values and types in the binary format (reviewed spec)

Wasm 3.0 `5.1-binary.values` + `5.2-binary.types` (SpecTec `859d3232`) restricted to P′. Every
relation `R a bs` reads: the complete byte list `bs` encodes `a`.
-/

namespace FVA.Wasm.Binary

open FVA.Wasm

/-- Concatenated encodings of a list, each element by `R` (no length prefix). -/
inductive Seq {α : Type} (R : α → List UInt8 → Prop) : List α → List UInt8 → Prop where
  | nil : Seq R [] []
  | cons {a : α} {as : List α} {b₁ b₂ : List UInt8} (ha : R a b₁) (hs : Seq R as b₂) :
      Seq R (a :: as) (b₁ ++ b₂)

/-- `vec(B)`: a `u32` element count followed by the elements (`Blist`). -/
def Vec {α : Type} (R : α → List UInt8 → Prop) (xs : List α) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, ULeb 32 xs.length b₁ ∧ Seq R xs b₂ ∧ bs = b₁ ++ b₂

/-- A single byte stands for itself. -/
def Byte (x : UInt8) (bs : List UInt8) : Prop := bs = [x]

/-- `name`: `vec(byte)` holding exactly the UTF-8 encoding of the string (`Bname`). -/
def Name (s : String) (bs : List UInt8) : Prop := Vec Byte s.toUTF8.toList bs

/-- Little-endian packing of a byte list into one number: the representation `decode` reads and
`fva trust` recomputes from the file. -/
def pack : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * pack bs

/-- Little-endian bytes of the low `8·k` bits of `n`. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: leBytes k (n / 256)

/-- `f32`/`f64` constants: IEEE-754 bits, little-endian (`Bf32`, `Bf64`). -/
def FloatBits (w : Width) (bits : Nat) (bs : List UInt8) : Prop :=
  let k := match w with | .w32 => 4 | .w64 => 8
  bits < 2 ^ (8 * k) ∧ bs = leBytes k bits

/-- Number types (`Bnumtype`). -/
def NumTypeB : NumType → List UInt8 → Prop
  | .i32, bs => bs = [0x7F]
  | .i64, bs => bs = [0x7E]
  | .f32, bs => bs = [0x7D]
  | .f64, bs => bs = [0x7C]

/-- Abstract heap types of P′ (`Babsheaptype`); the other bytes of 3.0's table are GC types. -/
def absHeapOps : List (UInt8 × AbsHeapType) := [(0x70, .func), (0x6F, .extern), (0x69, .exn)]

/-- Heap types (`Bheaptype`): an abstract heap type's byte, or a type index as a non-negative
`s33` (whose one-byte encodings of the abstract types are negative, so the two never overlap). -/
def HeapTypeB : HeapType → List UInt8 → Prop
  | .abs a, bs => ∃ b, (b, a) ∈ absHeapOps ∧ bs = [b]
  | .idx x, bs => SLeb 33 x bs

/-- Reference types (`Breftype`): `0x63 ht` (nullable), `0x64 ht` (non-null), or an abstract
heap type's byte alone (nullable). -/
inductive RefTypeB : RefType → List UInt8 → Prop where
  | null {ht : HeapType} {b : List UInt8} (h : HeapTypeB ht b) : RefTypeB ⟨true, ht⟩ (0x63 :: b)
  | nonNull {ht : HeapType} {b : List UInt8} (h : HeapTypeB ht b) :
      RefTypeB ⟨false, ht⟩ (0x64 :: b)
  | short {a : AbsHeapType} {b : UInt8} (h : (b, a) ∈ absHeapOps) : RefTypeB ⟨true, .abs a⟩ [b]

/-- Value types (`Bvaltype`). -/
def ValTypeB : ValType → List UInt8 → Prop
  | .num t, bs => NumTypeB t bs
  | .ref t, bs => RefTypeB t bs

/-- Result types: `vec(valtype)` (`Bresulttype`). -/
def ResultTypeB (ts : List ValType) (bs : List UInt8) : Prop := Vec ValTypeB ts bs

/-- Function types: `0x60 rt₁ rt₂` (`Bcomptype`'s function form). -/
def FuncTypeB (ft : FuncType) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, ResultTypeB ft.params b₁ ∧ ResultTypeB ft.results b₂ ∧
    bs = ([0x60] : List UInt8) ++ b₁ ++ b₂

/-- Sub types of P′ (`Bsubtype`): final, no declared supertype — a bare function type, or
`0x4F`, an empty supertype list and a function type (both `sub final ε (func ft)`). -/
def SubTypeB (ft : FuncType) (bs : List UInt8) : Prop :=
  FuncTypeB ft bs ∨ ∃ b₀ b, ULeb 32 0 b₀ ∧ FuncTypeB ft b ∧ bs = 0x4F :: b₀ ++ b

/-- Recursive types (`Brectype`): `0x4E vec(subtype)` or one subtype alone. -/
def RecTypeB (rt : RecType) (bs : List UInt8) : Prop :=
  (∃ b, Vec SubTypeB rt b ∧ bs = 0x4E :: b) ∨ (∃ ft, rt = [ft] ∧ SubTypeB ft bs)

/-- Limits (`Blimits`, 32-bit addresses): `0x00 min` or `0x01 min max`, each a `u64`
(validation bounds them). -/
def LimitsB (l : Limits) (bs : List UInt8) : Prop :=
  match l.max with
  | none => ∃ b, ULeb 64 l.min b ∧ bs = ([0x00] : List UInt8) ++ b
  | some m => ∃ b₁ b₂, ULeb 64 l.min b₁ ∧ ULeb 64 m b₂ ∧
      bs = ([0x01] : List UInt8) ++ b₁ ++ b₂

/-- Table types: `reftype limits` (`Btabletype`). -/
def TableTypeB (t : TableType) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, RefTypeB t.elem b₁ ∧ LimitsB t.limits b₂ ∧ bs = b₁ ++ b₂

/-- Tag types (`Btagtype`): `0x00` and a function type index. -/
def TagTypeB (x : Nat) (bs : List UInt8) : Prop := ∃ b, ULeb 32 x b ∧ bs = 0x00 :: b

/-- Global types: `valtype mut` with `0x00` const, `0x01` var (`Bglobaltype`). -/
def GlobalTypeB (g : GlobalType) (bs : List UInt8) : Prop :=
  ∃ b, ValTypeB g.val b ∧
    bs = b ++ [(match g.mutability with | .const => 0x00 | .var => 0x01 : UInt8)]

end FVA.Wasm.Binary
