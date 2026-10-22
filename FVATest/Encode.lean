import FVA.Spec.Binary.Module
import Std.Data.HashMap
import FVA.Tool.Lift

/-!
# Re-encoder for the decoder differential (E2)

Writes a decoded module back to bytes from the spec's opcode tables (`FVA.Wasm.Binary.plainOps`,
…), independent of the decoder's dispatch, so `wasm-tools print` of the original (custom
sections stripped) and of the re-encoding agree exactly when the decoder kept every field.
Encoding choices the syntax does not record: minimal LEBs, no explicit empty `else`, element
segments in function-index form whenever every initializer is `ref.func`.
-/

namespace FVA.Test.Encode

open FVA.Wasm FVA.Wasm.Binary

/-- Unsigned LEB128. -/
def uleb (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: uleb (n / 128)
termination_by n
decreasing_by omega

/-- Signed LEB128 (`Int.div` rounds toward −∞ here: `Int./` is `Int.div`'s floor variant). -/
partial def sleb (i : Int) : List UInt8 :=
  let b := (i % 128).toNat
  let rest := (i - b) / 128
  if (rest = 0 ∧ b < 64) ∨ (rest = -1 ∧ 64 ≤ b) then [b.toUInt8]
  else (b + 128).toUInt8 :: sleb rest

/-- `vec(B)`. -/
def vec {α : Type} (f : α → List UInt8) (xs : List α) : List UInt8 :=
  uleb xs.length ++ xs.flatMap f

/-- `name`. -/
def name (s : String) : List UInt8 := vec (fun b => [b]) s.toUTF8.toList

/-- Value types. -/
def valType : ValType → List UInt8
  | .num .i32 => [0x7F] | .num .i64 => [0x7E] | .num .f32 => [0x7D] | .num .f64 => [0x7C]
  | .ref .funcref => [0x70] | .ref .externref => [0x6F]

/-- Reference types. -/
def refType : RefType → List UInt8 | .funcref => [0x70] | .externref => [0x6F]

/-- Block types. -/
def blockType : BlockType → List UInt8
  | .empty => [0x40] | .val t => valType t | .idx x => sleb x

/-- Memory arguments. -/
def memArg (m : MemArg) : List UInt8 := uleb m.align ++ uleb m.offset

/-- Instructions compare by their rendering (the syntax has no `DecidableEq`). -/
def key (i : Instr) : String := FVA.Tool.Lift.instr i

/-- Opcodes of instructions without immediates. -/
def plainMap : Std.HashMap String UInt8 :=
  plainOps.foldl (fun m (op, i) => m.insert (key i) op) {}

/-- `0xFC` sub-opcodes of saturating truncations. -/
def fcPlainMap : Std.HashMap String Nat :=
  fcPlainOps.foldl (fun m (n, i) => m.insert (key i) n) {}

/-- Opcodes of memory instructions, keyed with a zero `memarg`. -/
def memMap : Std.HashMap String UInt8 :=
  memOps.foldl (fun m (op, mk) => m.insert (key (mk ⟨0, 0⟩)) op) {}

/-- Opcodes of one-index instructions, keyed with index 0. -/
def idxMap : Std.HashMap String UInt8 :=
  idxOps.foldl (fun m (op, mk) => m.insert (key (mk 0)) op) {}

/-- `0xFC` sub-opcodes of one-index instructions, keyed with index 0. -/
def fcIdxMap : Std.HashMap String Nat :=
  fcIdxOps.foldl (fun m (n, mk) => m.insert (key (mk 0)) n) {}

/-- Signed value of `bits` as a `w`-bit two's complement integer. -/
def signed (w : Nat) (bits : Nat) : Int :=
  if bits < 2 ^ (w - 1) then bits else (bits : Int) - 2 ^ w

mutual
/-- One instruction, looked up in the spec tables. -/
partial def instr (i : Instr) : List UInt8 :=
  match plainMap[key i]?, fcPlainMap[key i]? with
  | some op, _ => [op]
  | none, some n => 0xFC :: uleb n
  | none, none =>
  match i with
  | .load t m => memOp (.load t ⟨0, 0⟩) m
  | .loadPacked w p x m => memOp (.loadPacked w p x ⟨0, 0⟩) m
  | .store t m => memOp (.store t ⟨0, 0⟩) m
  | .storePacked w p m => memOp (.storePacked w p ⟨0, 0⟩) m
  | .block bt b => [0x02] ++ blockType bt ++ seq b ++ [0x0B]
  | .loop bt b => [0x03] ++ blockType bt ++ seq b ++ [0x0B]
  | .if_ bt t [] => [0x04] ++ blockType bt ++ seq t ++ [0x0B]
  | .if_ bt t e => [0x04] ++ blockType bt ++ seq t ++ [0x05] ++ seq e ++ [0x0B]
  | .brTable ls l => [0x0E] ++ vec uleb ls ++ uleb l
  | .callIndirect x y => [0x11] ++ uleb y ++ uleb x
  | .select (some ts) => 0x1C :: vec valType ts
  | .refNull t => 0xD0 :: refType t
  | .memorySize => [0x3F, 0x00] | .memoryGrow => [0x40, 0x00]
  | .memoryInit x => [0xFC] ++ uleb 8 ++ uleb x ++ [0x00]
  | .memoryCopy => [0xFC] ++ uleb 10 ++ [0x00, 0x00]
  | .memoryFill => [0xFC] ++ uleb 11 ++ [0x00]
  | .tableInit x y => [0xFC] ++ uleb 12 ++ uleb y ++ uleb x
  | .tableCopy x y => [0xFC] ++ uleb 14 ++ uleb x ++ uleb y
  | .iconst .w32 n => 0x41 :: sleb (signed 32 n)
  | .iconst .w64 n => 0x42 :: sleb (signed 64 n)
  | .fconst .w32 n => 0x43 :: leBytes 4 n
  | .fconst .w64 n => 0x44 :: leBytes 8 n
  | .br x => idx .br x | .brIf x => idx .brIf x | .call x => idx .call x
  | .refFunc x => idx .refFunc x | .localGet x => idx .localGet x
  | .localSet x => idx .localSet x | .localTee x => idx .localTee x
  | .globalGet x => idx .globalGet x | .globalSet x => idx .globalSet x
  | .tableGet x => idx .tableGet x | .tableSet x => idx .tableSet x
  | .dataDrop x => idx .dataDrop x | .elemDrop x => idx .elemDrop x
  | .tableGrow x => idx .tableGrow x | .tableSize x => idx .tableSize x
  | .tableFill x => idx .tableFill x
  | _ => panic! s!"no encoding for {key i}"
/-- A memory instruction from its zero-`memarg` form and its `memarg`. -/
partial def memOp (i₀ : Instr) (m : MemArg) : List UInt8 :=
  match memMap[key i₀]? with
  | some op => op :: memArg m
  | none => panic! s!"no memory opcode for {key i₀}"
/-- A one-index instruction. -/
partial def idx (mk : Nat → Instr) (x : Nat) : List UInt8 :=
  match idxMap[key (mk 0)]?, fcIdxMap[key (mk 0)]? with
  | some op, _ => op :: uleb x
  | none, some n => 0xFC :: uleb n ++ uleb x
  | none, none => panic! s!"no index opcode for {key (mk 0)}"
/-- An instruction sequence. -/
partial def seq (is : List Instr) : List UInt8 := is.flatMap instr
end

/-- An expression. -/
def expr (e : Expr) : List UInt8 := seq e ++ [0x0B]

/-- Limits. -/
def limits (l : Limits) : List UInt8 :=
  match l.max with
  | none => 0x00 :: uleb l.min
  | some m => 0x01 :: uleb l.min ++ uleb m

/-- Global types. -/
def globalType (g : GlobalType) : List UInt8 :=
  valType g.val ++ [(match g.mutability with | .const => 0x00 | .var => 0x01 : UInt8)]

/-- Table types. -/
def tableType (t : TableType) : List UInt8 := refType t.elem ++ limits t.limits

/-- Function indices when every initializer is `ref.func y`. -/
def funcIdxs : List Expr → Option (List Nat)
  | [] => some []
  | [.refFunc y] :: es => (funcIdxs es).map (y :: ·)
  | _ => none

/-- Element segments. -/
def elem (e : Elem) : List UInt8 :=
  match e.type, funcIdxs e.init, e.mode with
  | .funcref, some ys, .active 0 off => uleb 0 ++ expr off ++ vec uleb ys
  | .funcref, some ys, .passive => uleb 1 ++ [0x00] ++ vec uleb ys
  | .funcref, some ys, .active x off => uleb 2 ++ uleb x ++ expr off ++ [0x00] ++ vec uleb ys
  | .funcref, some ys, .declarative => uleb 3 ++ [0x00] ++ vec uleb ys
  | .funcref, none, .active 0 off => uleb 4 ++ expr off ++ vec expr e.init
  | t, _, .passive => uleb 5 ++ refType t ++ vec expr e.init
  | t, _, .active x off => uleb 6 ++ uleb x ++ expr off ++ refType t ++ vec expr e.init
  | t, _, .declarative => uleb 7 ++ refType t ++ vec expr e.init

/-- Data segments. -/
def data (d : Data) : List UInt8 :=
  match d.mode with
  | .active 0 off => uleb 0 ++ expr off ++ vec (fun b => [b]) d.init
  | .passive => uleb 1 ++ vec (fun b => [b]) d.init
  | .active x off => uleb 2 ++ uleb x ++ expr off ++ vec (fun b => [b]) d.init

/-- Code entries. -/
def code (f : Func) : List UInt8 :=
  let c := vec (fun (k, t) => uleb k ++ valType t) f.locals ++ expr f.body
  uleb c.length ++ c

/-- A section, omitted when `content` is `none`. -/
def section_ (id : UInt8) : Option (List UInt8) → List UInt8
  | none => []
  | some c => id :: uleb c.length ++ c

/-- A `vec` section, omitted when empty. -/
def vecSec {α : Type} (id : UInt8) (f : α → List UInt8) (xs : List α) : List UInt8 :=
  section_ id (if xs.isEmpty then none else some (vec f xs))

/-- Whether any function body uses a data index. -/
def needsDataCount (m : Module) : Bool := m.funcs.any fun f => FVA.Wasm.Decode.usesDataList f.body

/-- The whole module. -/
def module (m : Module) : List UInt8 :=
  preamble ++ vecSec 1 (fun ft => [0x60] ++ vec valType ft.params ++ vec valType ft.results) m.types
    ++ vecSec 2 (fun im => name im.module ++ name im.name ++ match im.desc with
        | .func x => 0x00 :: uleb x | .table t => 0x01 :: tableType t
        | .mem l => 0x02 :: limits l | .global g => 0x03 :: globalType g) m.imports
    ++ vecSec 3 (fun f => uleb f.type) m.funcs
    ++ vecSec 4 tableType m.tables ++ vecSec 5 limits m.mems
    ++ vecSec 6 (fun g => globalType g.type ++ expr g.init) m.globals
    ++ vecSec 7 (fun ex => name ex.name ++ match ex.desc with
        | .func x => 0x00 :: uleb x | .table x => 0x01 :: uleb x
        | .mem x => 0x02 :: uleb x | .global x => 0x03 :: uleb x) m.exports
    ++ section_ 8 (m.start.map uleb) ++ vecSec 9 elem m.elems
    ++ section_ 12 (if needsDataCount m then some (uleb m.datas.length) else none)
    ++ vecSec 10 code m.funcs ++ vecSec 11 data m.datas

end FVA.Test.Encode
