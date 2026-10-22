/-!
# Wasm abstract syntax (reviewed spec)

Mirrors the Wasm 2.0 specification §2 (Structure) for FVA's binary profile, SIMD excluded.
Decoding yields this syntax; it carries no validity guarantee (index ranges, typing, memory
count and constant-expression rules belong to validation, U6). Indices are `Nat`; the binary
grammar (`FVA.Spec.Binary`) bounds them by 2^32.
-/

namespace FVA.Wasm

/-- Number types. -/
inductive NumType where
  | i32 | i64 | f32 | f64
  deriving DecidableEq, Repr

/-- Reference types. -/
inductive RefType where
  | funcref | externref
  deriving DecidableEq, Repr

/-- Value types. -/
inductive ValType where
  | num (t : NumType)
  | ref (t : RefType)
  deriving DecidableEq, Repr

/-- Function types: parameter and result value types. -/
structure FuncType where
  /-- Parameter types. -/
  params : List ValType
  /-- Result types. -/
  results : List ValType
  deriving DecidableEq, Repr

/-- Limits of a memory (in pages) or a table (in elements). -/
structure Limits where
  /-- Minimum size. -/
  min : Nat
  /-- Optional maximum size. -/
  max : Option Nat
  deriving DecidableEq, Repr

/-- Table types. -/
structure TableType where
  /-- Size limits. -/
  limits : Limits
  /-- Element reference type. -/
  elem : RefType
  deriving DecidableEq, Repr

/-- Global mutability. -/
inductive Mut where
  | const | var
  deriving DecidableEq, Repr

/-- Global types. -/
structure GlobalType where
  /-- Mutability. -/
  mutability : Mut
  /-- Value type. -/
  val : ValType
  deriving DecidableEq, Repr

/-- Block types: no result, one value type, or a function type index. -/
inductive BlockType where
  | empty
  | val (t : ValType)
  | idx (x : Nat)
  deriving DecidableEq, Repr

/-- Memory operand immediates: alignment exponent and byte offset. -/
structure MemArg where
  /-- Alignment exponent (log2 of the alignment hint). -/
  align : Nat
  /-- Static byte offset. -/
  offset : Nat
  deriving DecidableEq, Repr

/-- Integer and float widths used by numeric instruction families. -/
inductive Width where
  | w32 | w64
  deriving DecidableEq, Repr

/-- Signedness of integer operations. -/
inductive Sx where
  | s | u
  deriving DecidableEq, Repr

/-- Integer unary operators (`clz`, `ctz`, `popcnt`, sign extension of the low 8/16/32 bits). -/
inductive IUnOp where
  | clz | ctz | popcnt | extend8s | extend16s | extend32s
  deriving DecidableEq, Repr

/-- Integer binary operators. -/
inductive IBinOp where
  | add | sub | mul | div (sx : Sx) | rem (sx : Sx)
  | and | or | xor | shl | shr (sx : Sx) | rotl | rotr
  deriving DecidableEq, Repr

/-- Integer relational operators. -/
inductive IRelOp where
  | eq | ne | lt (sx : Sx) | gt (sx : Sx) | le (sx : Sx) | ge (sx : Sx)
  deriving DecidableEq, Repr

/-- Float unary operators. -/
inductive FUnOp where
  | abs | neg | sqrt | ceil | floor | trunc | nearest
  deriving DecidableEq, Repr

/-- Float binary operators. -/
inductive FBinOp where
  | add | sub | mul | div | min | max | copysign
  deriving DecidableEq, Repr

/-- Float relational operators. -/
inductive FRelOp where
  | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- Conversion operators (spec §2.4.1 `cvtop`), with source and target widths where needed. -/
inductive CvtOp where
  /-- `i32.wrap_i64`. -/
  | wrap
  /-- `i64.extend_i32_sx`. -/
  | extend (sx : Sx)
  /-- `iN.trunc_fM_sx` (traps on NaN or out of range). -/
  | trunc (dst src : Width) (sx : Sx)
  /-- `iN.trunc_sat_fM_sx` (saturating). -/
  | truncSat (dst src : Width) (sx : Sx)
  /-- `fN.convert_iM_sx`. -/
  | convert (dst src : Width) (sx : Sx)
  /-- `f32.demote_f64`. -/
  | demote
  /-- `f64.promote_f32`. -/
  | promote
  /-- `iN.reinterpret_fN` (`toInt := true`) or `fN.reinterpret_iN`. -/
  | reinterpret (w : Width) (toInt : Bool)
  deriving DecidableEq, Repr

/-- Packed memory access sizes for integer loads and stores. -/
inductive PackSize where
  | p8 | p16 | p32
  deriving DecidableEq, Repr

/-- Instructions of the profile (spec §2.4); structured control carries nested bodies. -/
inductive Instr where
  -- numeric
  /-- Integer constant of the given width (two's-complement bits). -/
  | iconst (w : Width) (bits : Nat)
  /-- Float constant of the given width (IEEE-754 bits). -/
  | fconst (w : Width) (bits : Nat)
  /-- Integer unary operator. -/
  | iunop (w : Width) (op : IUnOp)
  /-- Integer binary operator. -/
  | ibinop (w : Width) (op : IBinOp)
  /-- Integer `eqz`. -/
  | itestEqz (w : Width)
  /-- Integer comparison. -/
  | irelop (w : Width) (op : IRelOp)
  /-- Float unary operator. -/
  | funop (w : Width) (op : FUnOp)
  /-- Float binary operator. -/
  | fbinop (w : Width) (op : FBinOp)
  /-- Float comparison. -/
  | frelop (w : Width) (op : FRelOp)
  /-- Conversion. -/
  | cvtop (op : CvtOp)
  -- reference
  /-- `ref.null t`. -/
  | refNull (t : RefType)
  /-- `ref.is_null`. -/
  | refIsNull
  /-- `ref.func x`. -/
  | refFunc (x : Nat)
  -- parametric
  /-- `drop`. -/
  | drop
  /-- `select`, optionally annotated with result types. -/
  | select (ts : Option (List ValType))
  -- variable
  /-- `local.get x`. -/
  | localGet (x : Nat)
  /-- `local.set x`. -/
  | localSet (x : Nat)
  /-- `local.tee x`. -/
  | localTee (x : Nat)
  /-- `global.get x`. -/
  | globalGet (x : Nat)
  /-- `global.set x`. -/
  | globalSet (x : Nat)
  -- table
  /-- `table.get x`. -/
  | tableGet (x : Nat)
  /-- `table.set x`. -/
  | tableSet (x : Nat)
  /-- `table.size x`. -/
  | tableSize (x : Nat)
  /-- `table.grow x`. -/
  | tableGrow (x : Nat)
  /-- `table.fill x`. -/
  | tableFill (x : Nat)
  /-- `table.copy x y` (destination `x`, source `y`). -/
  | tableCopy (x y : Nat)
  /-- `table.init x y` (table `x`, element segment `y`). -/
  | tableInit (x y : Nat)
  /-- `elem.drop x`. -/
  | elemDrop (x : Nat)
  -- memory
  /-- Full-width load of a number type. -/
  | load (t : NumType) (m : MemArg)
  /-- Packed integer load with sign or zero extension. -/
  | loadPacked (w : Width) (p : PackSize) (sx : Sx) (m : MemArg)
  /-- Full-width store of a number type. -/
  | store (t : NumType) (m : MemArg)
  /-- Packed integer store. -/
  | storePacked (w : Width) (p : PackSize) (m : MemArg)
  /-- `memory.size`. -/
  | memorySize
  /-- `memory.grow`. -/
  | memoryGrow
  /-- `memory.fill`. -/
  | memoryFill
  /-- `memory.copy`. -/
  | memoryCopy
  /-- `memory.init x`. -/
  | memoryInit (x : Nat)
  /-- `data.drop x`. -/
  | dataDrop (x : Nat)
  -- control
  /-- `unreachable`. -/
  | unreachable
  /-- `nop`. -/
  | nop
  /-- `block bt body end`. -/
  | block (bt : BlockType) (body : List Instr)
  /-- `loop bt body end`. -/
  | loop (bt : BlockType) (body : List Instr)
  /-- `if bt thn else els end`. -/
  | if_ (bt : BlockType) (thn els : List Instr)
  /-- `br l`. -/
  | br (l : Nat)
  /-- `br_if l`. -/
  | brIf (l : Nat)
  /-- `br_table ls l`. -/
  | brTable (ls : List Nat) (l : Nat)
  /-- `return`. -/
  | return_
  /-- `call x`. -/
  | call (x : Nat)
  /-- `call_indirect x y` (table `x`, type `y`). -/
  | callIndirect (x y : Nat)
  deriving Repr

/-- Expressions: instruction sequences (the trailing `end` is implicit). -/
abbrev Expr := List Instr

/-- Functions: type index, declared locals (expanded), body. -/
structure Func where
  /-- Type index. -/
  type : Nat
  /-- Locals, one entry per local (run-length groups expanded). -/
  locals : List ValType
  /-- Body. -/
  body : Expr

/-- Globals. -/
structure Global where
  /-- Type. -/
  type : GlobalType
  /-- Initializer expression. -/
  init : Expr

/-- Element segment modes. -/
inductive ElemMode where
  | passive
  | active (table : Nat) (offset : Expr)
  | declarative

/-- Element segments. -/
structure Elem where
  /-- Element reference type. -/
  type : RefType
  /-- Initializer expressions, one per element. -/
  init : List Expr
  /-- Mode. -/
  mode : ElemMode

/-- Data segment modes. -/
inductive DataMode where
  | passive
  | active (mem : Nat) (offset : Expr)

/-- Data segments. -/
structure Data where
  /-- Bytes. -/
  init : List UInt8
  /-- Mode. -/
  mode : DataMode

/-- Import descriptions. -/
inductive ImportDesc where
  | func (x : Nat)
  | table (t : TableType)
  | mem (t : Limits)
  | global (t : GlobalType)

/-- Imports. -/
structure Import where
  /-- Module name. -/
  module : String
  /-- Field name. -/
  name : String
  /-- Description. -/
  desc : ImportDesc

/-- Export descriptions. -/
inductive ExportDesc where
  | func (x : Nat)
  | table (x : Nat)
  | mem (x : Nat)
  | global (x : Nat)

/-- Exports. -/
structure Export where
  /-- Name. -/
  name : String
  /-- Description. -/
  desc : ExportDesc

/-- Modules (spec §2.5). Custom sections are not part of the abstract syntax. -/
structure Module where
  /-- Function types. -/
  types : List FuncType := []
  /-- Functions defined by the module. -/
  funcs : List Func := []
  /-- Tables. -/
  tables : List TableType := []
  /-- Memories. -/
  mems : List Limits := []
  /-- Globals. -/
  globals : List Global := []
  /-- Element segments. -/
  elems : List Elem := []
  /-- Data segments. -/
  datas : List Data := []
  /-- Start function. -/
  start : Option Nat := none
  /-- Imports. -/
  imports : List Import := []
  /-- Exports. -/
  exports : List Export := []

end FVA.Wasm
