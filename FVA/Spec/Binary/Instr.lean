import FVA.Spec.Binary.Types

/-!
# Instructions in the binary format (reviewed spec)

Spec §5.4. Opcodes without immediates are listed as tables in the spec's order, so each entry
can be checked against the spec's listing line by line.
-/

namespace FVA.Wasm.Binary

open FVA.Wasm

/-- Block types: `0x40`, a value type, or a non-negative `s33` type index (spec §5.4.1). -/
def BlockTypeB : BlockType → List UInt8 → Prop
  | .empty, bs => bs = [0x40]
  | .val t, bs => ValTypeB t bs
  | .idx x, bs => SLeb 33 x bs

/-- Memory arguments: `align:u32 offset:u32` (spec §5.4.6). -/
def MemArgB (m : MemArg) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, ULeb 32 m.align b₁ ∧ ULeb 32 m.offset b₂ ∧ bs = b₁ ++ b₂

/-- Signed LEB value of an integer constant, as its two's-complement bits of width `w`. -/
def constBits (w : Width) (n : Int) : Nat :=
  match w with
  | .w32 => (n % 2 ^ 32).toNat
  | .w64 => (n % 2 ^ 64).toNat

/-- One-byte opcodes without immediates (spec §5.4.1–§5.4.7, numeric `0x45`–`0xC4`). -/
def plainOps : List (UInt8 × Instr) :=
  [ (0x00, .unreachable), (0x01, .nop), (0x0F, .return_), (0x1A, .drop), (0x1B, .select none),
    (0xD1, .refIsNull),
    (0x45, .itestEqz .w32), (0x46, .irelop .w32 .eq), (0x47, .irelop .w32 .ne),
    (0x48, .irelop .w32 (.lt .s)), (0x49, .irelop .w32 (.lt .u)),
    (0x4A, .irelop .w32 (.gt .s)), (0x4B, .irelop .w32 (.gt .u)),
    (0x4C, .irelop .w32 (.le .s)), (0x4D, .irelop .w32 (.le .u)),
    (0x4E, .irelop .w32 (.ge .s)), (0x4F, .irelop .w32 (.ge .u)),
    (0x50, .itestEqz .w64), (0x51, .irelop .w64 .eq), (0x52, .irelop .w64 .ne),
    (0x53, .irelop .w64 (.lt .s)), (0x54, .irelop .w64 (.lt .u)),
    (0x55, .irelop .w64 (.gt .s)), (0x56, .irelop .w64 (.gt .u)),
    (0x57, .irelop .w64 (.le .s)), (0x58, .irelop .w64 (.le .u)),
    (0x59, .irelop .w64 (.ge .s)), (0x5A, .irelop .w64 (.ge .u)),
    (0x5B, .frelop .w32 .eq), (0x5C, .frelop .w32 .ne), (0x5D, .frelop .w32 .lt),
    (0x5E, .frelop .w32 .gt), (0x5F, .frelop .w32 .le), (0x60, .frelop .w32 .ge),
    (0x61, .frelop .w64 .eq), (0x62, .frelop .w64 .ne), (0x63, .frelop .w64 .lt),
    (0x64, .frelop .w64 .gt), (0x65, .frelop .w64 .le), (0x66, .frelop .w64 .ge),
    (0x67, .iunop .w32 .clz), (0x68, .iunop .w32 .ctz), (0x69, .iunop .w32 .popcnt),
    (0x6A, .ibinop .w32 .add), (0x6B, .ibinop .w32 .sub), (0x6C, .ibinop .w32 .mul),
    (0x6D, .ibinop .w32 (.div .s)), (0x6E, .ibinop .w32 (.div .u)),
    (0x6F, .ibinop .w32 (.rem .s)), (0x70, .ibinop .w32 (.rem .u)),
    (0x71, .ibinop .w32 .and), (0x72, .ibinop .w32 .or), (0x73, .ibinop .w32 .xor),
    (0x74, .ibinop .w32 .shl), (0x75, .ibinop .w32 (.shr .s)), (0x76, .ibinop .w32 (.shr .u)),
    (0x77, .ibinop .w32 .rotl), (0x78, .ibinop .w32 .rotr),
    (0x79, .iunop .w64 .clz), (0x7A, .iunop .w64 .ctz), (0x7B, .iunop .w64 .popcnt),
    (0x7C, .ibinop .w64 .add), (0x7D, .ibinop .w64 .sub), (0x7E, .ibinop .w64 .mul),
    (0x7F, .ibinop .w64 (.div .s)), (0x80, .ibinop .w64 (.div .u)),
    (0x81, .ibinop .w64 (.rem .s)), (0x82, .ibinop .w64 (.rem .u)),
    (0x83, .ibinop .w64 .and), (0x84, .ibinop .w64 .or), (0x85, .ibinop .w64 .xor),
    (0x86, .ibinop .w64 .shl), (0x87, .ibinop .w64 (.shr .s)), (0x88, .ibinop .w64 (.shr .u)),
    (0x89, .ibinop .w64 .rotl), (0x8A, .ibinop .w64 .rotr),
    (0x8B, .funop .w32 .abs), (0x8C, .funop .w32 .neg), (0x8D, .funop .w32 .ceil),
    (0x8E, .funop .w32 .floor), (0x8F, .funop .w32 .trunc), (0x90, .funop .w32 .nearest),
    (0x91, .funop .w32 .sqrt), (0x92, .fbinop .w32 .add), (0x93, .fbinop .w32 .sub),
    (0x94, .fbinop .w32 .mul), (0x95, .fbinop .w32 .div), (0x96, .fbinop .w32 .min),
    (0x97, .fbinop .w32 .max), (0x98, .fbinop .w32 .copysign),
    (0x99, .funop .w64 .abs), (0x9A, .funop .w64 .neg), (0x9B, .funop .w64 .ceil),
    (0x9C, .funop .w64 .floor), (0x9D, .funop .w64 .trunc), (0x9E, .funop .w64 .nearest),
    (0x9F, .funop .w64 .sqrt), (0xA0, .fbinop .w64 .add), (0xA1, .fbinop .w64 .sub),
    (0xA2, .fbinop .w64 .mul), (0xA3, .fbinop .w64 .div), (0xA4, .fbinop .w64 .min),
    (0xA5, .fbinop .w64 .max), (0xA6, .fbinop .w64 .copysign),
    (0xA7, .cvtop .wrap),
    (0xA8, .cvtop (.trunc .w32 .w32 .s)), (0xA9, .cvtop (.trunc .w32 .w32 .u)),
    (0xAA, .cvtop (.trunc .w32 .w64 .s)), (0xAB, .cvtop (.trunc .w32 .w64 .u)),
    (0xAC, .cvtop (.extend .s)), (0xAD, .cvtop (.extend .u)),
    (0xAE, .cvtop (.trunc .w64 .w32 .s)), (0xAF, .cvtop (.trunc .w64 .w32 .u)),
    (0xB0, .cvtop (.trunc .w64 .w64 .s)), (0xB1, .cvtop (.trunc .w64 .w64 .u)),
    (0xB2, .cvtop (.convert .w32 .w32 .s)), (0xB3, .cvtop (.convert .w32 .w32 .u)),
    (0xB4, .cvtop (.convert .w32 .w64 .s)), (0xB5, .cvtop (.convert .w32 .w64 .u)),
    (0xB6, .cvtop .demote),
    (0xB7, .cvtop (.convert .w64 .w32 .s)), (0xB8, .cvtop (.convert .w64 .w32 .u)),
    (0xB9, .cvtop (.convert .w64 .w64 .s)), (0xBA, .cvtop (.convert .w64 .w64 .u)),
    (0xBB, .cvtop .promote),
    (0xBC, .cvtop (.reinterpret .w32 true)), (0xBD, .cvtop (.reinterpret .w64 true)),
    (0xBE, .cvtop (.reinterpret .w32 false)), (0xBF, .cvtop (.reinterpret .w64 false)),
    (0xC0, .iunop .w32 .extend8s), (0xC1, .iunop .w32 .extend16s),
    (0xC2, .iunop .w64 .extend8s), (0xC3, .iunop .w64 .extend16s),
    (0xC4, .iunop .w64 .extend32s) ]

/-- `0xFC`-prefixed opcodes (sub-opcode is a `u32`) without immediates: saturating truncation. -/
def fcPlainOps : List (Nat × Instr) :=
  [ (0, .cvtop (.truncSat .w32 .w32 .s)), (1, .cvtop (.truncSat .w32 .w32 .u)),
    (2, .cvtop (.truncSat .w32 .w64 .s)), (3, .cvtop (.truncSat .w32 .w64 .u)),
    (4, .cvtop (.truncSat .w64 .w32 .s)), (5, .cvtop (.truncSat .w64 .w32 .u)),
    (6, .cvtop (.truncSat .w64 .w64 .s)), (7, .cvtop (.truncSat .w64 .w64 .u)) ]

/-- Load/store opcodes with a `memarg` (spec §5.4.6); the function builds the instruction. -/
def memOps : List (UInt8 × (MemArg → Instr)) :=
  [ (0x28, .load .i32), (0x29, .load .i64), (0x2A, .load .f32), (0x2B, .load .f64),
    (0x2C, .loadPacked .w32 .p8 .s), (0x2D, .loadPacked .w32 .p8 .u),
    (0x2E, .loadPacked .w32 .p16 .s), (0x2F, .loadPacked .w32 .p16 .u),
    (0x30, .loadPacked .w64 .p8 .s), (0x31, .loadPacked .w64 .p8 .u),
    (0x32, .loadPacked .w64 .p16 .s), (0x33, .loadPacked .w64 .p16 .u),
    (0x34, .loadPacked .w64 .p32 .s), (0x35, .loadPacked .w64 .p32 .u),
    (0x36, .store .i32), (0x37, .store .i64), (0x38, .store .f32), (0x39, .store .f64),
    (0x3A, .storePacked .w32 .p8), (0x3B, .storePacked .w32 .p16),
    (0x3C, .storePacked .w64 .p8), (0x3D, .storePacked .w64 .p16),
    (0x3E, .storePacked .w64 .p32) ]

/-- One-byte opcodes taking one `u32` index (variable instructions, `table.get/set`,
`ref.func`, `call`, `br`, `br_if`). -/
def idxOps : List (UInt8 × (Nat → Instr)) :=
  [ (0x0C, .br), (0x0D, .brIf), (0x10, .call), (0xD2, .refFunc),
    (0x20, .localGet), (0x21, .localSet), (0x22, .localTee),
    (0x23, .globalGet), (0x24, .globalSet), (0x25, .tableGet), (0x26, .tableSet) ]

/-- `0xFC`-prefixed table opcodes taking one `u32` index. -/
def fcIdxOps : List (Nat × (Nat → Instr)) :=
  [ (9, .dataDrop), (13, .elemDrop), (15, .tableGrow), (16, .tableSize), (17, .tableFill) ]

mutual

/-- `InstrB i bs`: the bytes `bs` encode the instruction `i`. -/
inductive InstrB : Instr → List UInt8 → Prop where
  | plain {i : Instr} {op : UInt8} (h : (op, i) ∈ plainOps) : InstrB i [op]
  | fcPlain {i : Instr} {n : Nat} {b : List UInt8} (h : (n, i) ∈ fcPlainOps) (hn : ULeb 32 n b) :
      InstrB i (0xFC :: b)
  | mem {mk : MemArg → Instr} {op : UInt8} {m : MemArg} {b : List UInt8}
      (h : (op, mk) ∈ memOps) (hm : MemArgB m b) : InstrB (mk m) (op :: b)
  | idx {mk : Nat → Instr} {op : UInt8} {x : Nat} {b : List UInt8}
      (h : (op, mk) ∈ idxOps) (hx : ULeb 32 x b) : InstrB (mk x) (op :: b)
  | fcIdx {mk : Nat → Instr} {n x : Nat} {b₁ b₂ : List UInt8}
      (h : (n, mk) ∈ fcIdxOps) (hn : ULeb 32 n b₁) (hx : ULeb 32 x b₂) :
      InstrB (mk x) (0xFC :: b₁ ++ b₂)
  /-- `0x02 bt instr* 0x0B`. -/
  | block {bt : BlockType} {body : Instrs} {b₁ b₂ : List UInt8}
      (ht : BlockTypeB bt b₁) (hb : InstrsB body b₂) :
      InstrB (.block bt body) ([0x02] ++ b₁ ++ b₂ ++ [0x0B])
  /-- `0x03 bt instr* 0x0B`. -/
  | loop {bt : BlockType} {body : Instrs} {b₁ b₂ : List UInt8}
      (ht : BlockTypeB bt b₁) (hb : InstrsB body b₂) :
      InstrB (.loop bt body) ([0x03] ++ b₁ ++ b₂ ++ [0x0B])
  /-- `0x04 bt instr* 0x0B` (empty else branch). -/
  | ifNoElse {bt : BlockType} {thn : Instrs} {b₁ b₂ : List UInt8}
      (ht : BlockTypeB bt b₁) (hb : InstrsB thn b₂) :
      InstrB (.if_ bt thn .nil) ([0x04] ++ b₁ ++ b₂ ++ [0x0B])
  /-- `0x04 bt instr* 0x05 instr* 0x0B`. -/
  | ifElse {bt : BlockType} {thn els : Instrs} {b₁ b₂ b₃ : List UInt8}
      (ht : BlockTypeB bt b₁) (hb : InstrsB thn b₂) (he : InstrsB els b₃) :
      InstrB (.if_ bt thn els) ([0x04] ++ b₁ ++ b₂ ++ [0x05] ++ b₃ ++ [0x0B])
  /-- `0x0E l*:vec(labelidx) l:labelidx`. -/
  | brTable {ls : List Nat} {l : Nat} {b₁ b₂ : List UInt8}
      (hs : Vec (ULeb 32) ls b₁) (hl : ULeb 32 l b₂) :
      InstrB (.brTable ls l) ([0x0E] ++ b₁ ++ b₂)
  /-- `0x11 y:typeidx x:tableidx` is `call_indirect x y`. -/
  | callIndirect {x y : Nat} {b₁ b₂ : List UInt8} (hy : ULeb 32 y b₁) (hx : ULeb 32 x b₂) :
      InstrB (.callIndirect x y) ([0x11] ++ b₁ ++ b₂)
  /-- `0x1C t*:vec(valtype)`. -/
  | selectT {ts : List ValType} {b : List UInt8} (h : Vec ValTypeB ts b) :
      InstrB (.select (some ts)) (0x1C :: b)
  /-- `0xD0 t:reftype`. -/
  | refNull {t : RefType} {b : List UInt8} (h : RefTypeB t b) : InstrB (.refNull t) (0xD0 :: b)
  /-- `0x3F 0x00`. -/
  | memorySize : InstrB .memorySize [0x3F, 0x00]
  /-- `0x40 0x00`. -/
  | memoryGrow : InstrB .memoryGrow [0x40, 0x00]
  /-- `0xFC 8:u32 x:dataidx 0x00`. -/
  | memoryInit {x : Nat} {b₁ b₂ : List UInt8} (hn : ULeb 32 8 b₁) (hx : ULeb 32 x b₂) :
      InstrB (.memoryInit x) ([0xFC] ++ b₁ ++ b₂ ++ [0x00])
  /-- `0xFC 10:u32 0x00 0x00`. -/
  | memoryCopy {b : List UInt8} (hn : ULeb 32 10 b) :
      InstrB .memoryCopy ([0xFC] ++ b ++ [0x00, 0x00])
  /-- `0xFC 11:u32 0x00`. -/
  | memoryFill {b : List UInt8} (hn : ULeb 32 11 b) : InstrB .memoryFill ([0xFC] ++ b ++ [0x00])
  /-- `0xFC 12:u32 y:elemidx x:tableidx` is `table.init x y`. -/
  | tableInit {x y : Nat} {b₁ b₂ b₃ : List UInt8} (hn : ULeb 32 12 b₁) (hy : ULeb 32 y b₂)
      (hx : ULeb 32 x b₃) : InstrB (.tableInit x y) ([0xFC] ++ b₁ ++ b₂ ++ b₃)
  /-- `0xFC 14:u32 x:tableidx y:tableidx`. -/
  | tableCopy {x y : Nat} {b₁ b₂ b₃ : List UInt8} (hn : ULeb 32 14 b₁) (hx : ULeb 32 x b₂)
      (hy : ULeb 32 y b₃) : InstrB (.tableCopy x y) ([0xFC] ++ b₁ ++ b₂ ++ b₃)
  /-- `0x41 n:s32`. -/
  | i32Const {n : Int} {b : List UInt8} (h : SLeb 32 n b) :
      InstrB (.iconst .w32 (constBits .w32 n)) (0x41 :: b)
  /-- `0x42 n:s64`. -/
  | i64Const {n : Int} {b : List UInt8} (h : SLeb 64 n b) :
      InstrB (.iconst .w64 (constBits .w64 n)) (0x42 :: b)
  /-- `0x43 z:f32`. -/
  | f32Const {bits : Nat} {b : List UInt8} (h : FloatBits .w32 bits b) :
      InstrB (.fconst .w32 bits) (0x43 :: b)
  /-- `0x44 z:f64`. -/
  | f64Const {bits : Nat} {b : List UInt8} (h : FloatBits .w64 bits b) :
      InstrB (.fconst .w64 bits) (0x44 :: b)

/-- Concatenated instruction encodings (no terminator). -/
inductive InstrsB : Instrs → List UInt8 → Prop where
  | nil : InstrsB .nil []
  | cons {i : Instr} {is : Instrs} {b₁ b₂ : List UInt8} (hi : InstrB i b₁)
      (hs : InstrsB is b₂) : InstrsB (.cons i is) (b₁ ++ b₂)

end

/-- `expr`: instructions followed by `end` (`0x0B`) (spec §5.4.9). -/
def ExprB (e : Expr) (bs : List UInt8) : Prop :=
  ∃ b, InstrsB e b ∧ bs = b ++ [0x0B]

end FVA.Wasm.Binary
