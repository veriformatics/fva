/-!
# Wasm abstract syntax (reviewed spec)

Mirrors the Wasm 3.0 specification §2 (Structure; SpecTec `859d3232`) for FVA's profile P′
(`FVA.Profile`): Wasm 2.0 without SIMD, plus exception handling, tail calls, function references
and recursive groups of function types. Decoding yields this syntax; it carries no validity
guarantee (index ranges, typing, memory count and constant-expression rules belong to
validation). Indices are `Nat`; the binary grammar (`FVA.Spec.Binary`) bounds them by 2^32.
Instruction sequences are `List Instr` nested in `Instr`; Lean derives neither `DecidableEq` nor
`Repr` for that nesting, and nothing needs them: `decode_eq` is checked by kernel defeq.
-/

namespace FVA.Wasm

/-- Number types. -/
inductive NumType where
  | i32 | i64 | f32 | f64
  deriving DecidableEq, Repr

/-- Abstract heap types of the profile (3.0 `absheaptype`): functions, external references,
exceptions. -/
inductive AbsHeapType where
  | func | extern | exn
  deriving DecidableEq, Repr

mutual
/-- Heap types (`heaptype`): abstract; a type index (source syntax); a closed defined type
(`def_`: what closure puts in place of a type index for runtime and validation); the `i`-th type
of the enclosing recursive group (`rec_`: only inside a rolled group, A2). -/
inductive HeapType where
  | abs (a : AbsHeapType)
  | idx (x : Nat)
  | def_ (d : DefType)
  | rec_ (i : Nat)

/-- Reference types (`reftype`): `ref null? ht`. -/
structure RefType where
  /-- Whether `null` is a value of the type. -/
  null : Bool
  /-- The referenced heap type. -/
  heap : HeapType

/-- Value types. -/
inductive ValType where
  | num (t : NumType)
  | ref (t : RefType)

/-- Function types: parameter and result value types. -/
structure FuncType where
  /-- Parameter types. -/
  params : List ValType
  /-- Result types. -/
  results : List ValType

/-- Defined types (3.0 `deftype` = `_DEF rectype n`): type `idx` of the rolled recursive group
`group`, whose members refer to each other by `rec_` and to earlier types by `def_`. Two defined
types are the same type exactly when they are equal terms (canonical group + projection). -/
structure DefType where
  /-- The rolled recursive group. -/
  group : List FuncType
  /-- The projection. -/
  idx : Nat
end

/-- `funcref` = `ref null func`. -/
@[match_pattern] abbrev RefType.funcref : RefType := ⟨true, .abs .func⟩
/-- `externref` = `ref null extern`. -/
@[match_pattern] abbrev RefType.externref : RefType := ⟨true, .abs .extern⟩
/-- `exnref` = `ref null exn`. -/
@[match_pattern] abbrev RefType.exnref : RefType := ⟨true, .abs .exn⟩

/-- The nullable reference type of the same heap type. -/
def RefType.nullable (t : RefType) : RefType := { t with null := true }

/-- Recursive types (`rectype`), in P′: function types defined together, each the final subtype of
no declared supertype (`sub final ε (func ft)`); they refer to each other and to earlier types by
type index. -/
abbrev RecType := List FuncType

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

/-- Block types: no result, one value type, or a function type index. -/
inductive BlockType where
  | empty
  | val (t : ValType)
  | idx (x : Nat)

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

/-- Handler clauses of `try_table` (`catch`): catch exceptions of tag `x`, or any exception, with
the exception reference (`…Ref`) or without, and branch to label `l`. -/
inductive Catch where
  | tag (x l : Nat)
  | tagRef (x l : Nat)
  | all (l : Nat)
  | allRef (l : Nat)
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
  /-- `ref.null ht`. -/
  | refNull (ht : HeapType)
  /-- `ref.is_null`. -/
  | refIsNull
  /-- `ref.func x`. -/
  | refFunc (x : Nat)
  /-- `ref.as_non_null`. -/
  | refAsNonNull
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
  /-- `call_ref x` (type `x`). -/
  | callRef (x : Nat)
  /-- `return_call x`. -/
  | returnCall (x : Nat)
  /-- `return_call_indirect x y` (table `x`, type `y`). -/
  | returnCallIndirect (x y : Nat)
  /-- `return_call_ref x` (type `x`). -/
  | returnCallRef (x : Nat)
  /-- `br_on_null l`. -/
  | brOnNull (l : Nat)
  /-- `br_on_non_null l`. -/
  | brOnNonNull (l : Nat)
  /-- `throw x` (tag `x`). -/
  | throw (x : Nat)
  /-- `throw_ref`. -/
  | throwRef
  /-- `try_table bt catches body end`. -/
  | tryTable (bt : BlockType) (catches : List Catch) (body : List Instr)

/-- Expressions: instruction sequences (the trailing `end` is implicit). -/
abbrev Expr := List Instr

/-- Functions: type index, declared locals, body. -/
structure Func where
  /-- Type index. -/
  type : Nat
  /-- Locals as the encoded runs `(count, type)`; a run of 2^32 − 1 locals stays one entry. -/
  locals : List (Nat × ValType)
  /-- Body. -/
  body : Expr

/-- Tables (`table`): a type and the initializer every element starts as. -/
structure Table where
  /-- Type. -/
  type : TableType
  /-- Initializer expression. -/
  init : Expr

/-- Tags (`tag`): the function type index of the exceptions' parameters. -/
structure Tag where
  /-- Type index. -/
  type : Nat
  deriving DecidableEq, Repr

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
  /-- A tag of the function type with this index. -/
  | tag (x : Nat)

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
  | tag (x : Nat)
  deriving DecidableEq, Repr

/-- Exports. -/
structure Export where
  /-- Name. -/
  name : String
  /-- Description. -/
  desc : ExportDesc
  deriving DecidableEq, Repr

/-- Modules (spec §2.5). Custom sections are not part of the abstract syntax. -/
structure Module where
  /-- Recursive type groups, in definition order (`typeList` = the type index space). -/
  types : List RecType := []
  /-- Functions defined by the module. -/
  funcs : List Func := []
  /-- Tables. -/
  tables : List Table := []
  /-- Memories. -/
  mems : List Limits := []
  /-- Tags. -/
  tags : List Tag := []
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

/-- The type index space: every recursive group's members in definition order. -/
def Module.typeList (m : Module) : List FuncType := m.types.flatten

end FVA.Wasm
