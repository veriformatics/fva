import FVA.Tool.Decode

/-!
# `fva lift`: render a decoded module as a Lean file whose `decode_eq` the kernel re-checks

The printer is untrusted: `decode_eq : decode bytes len = .ok module` is proved by the kernel
evaluating the verified decoder on the byte literal, so a printer bug fails the proof instead of
misstating the module.
-/

namespace FVA.Tool.Lift

open FVA.Wasm

/-- Lean syntax for a list, one rendered element per entry. -/
def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- Parenthesize a rendering that contains a space. -/
def paren (s : String) : String := if s.contains ' ' then s!"({s})" else s

/-- Widths. -/
def width : Width → String | .w32 => ".w32" | .w64 => ".w64"
/-- Signedness. -/
def sx : Sx → String | .s => ".s" | .u => ".u"
/-- Number types. -/
def numType : NumType → String | .i32 => ".i32" | .i64 => ".i64" | .f32 => ".f32" | .f64 => ".f64"
/-- Reference types. -/
def refType : RefType → String | .funcref => ".funcref" | .externref => ".externref"
/-- Value types. -/
def valType : ValType → String
  | .num t => s!".num {numType t}" | .ref t => s!".ref {refType t}"
/-- Block types. -/
def blockType : BlockType → String
  | .empty => ".empty" | .val t => s!"(.val ({valType t}))" | .idx x => s!"(.idx {x})"
/-- Memory arguments. -/
def memArg (m : MemArg) : String := s!"\{ align := {m.align}, offset := {m.offset} }"
/-- Packed sizes. -/
def packSize : PackSize → String | .p8 => ".p8" | .p16 => ".p16" | .p32 => ".p32"

/-- Integer unary operators. -/
def iunop : IUnOp → String
  | .clz => ".clz" | .ctz => ".ctz" | .popcnt => ".popcnt"
  | .extend8s => ".extend8s" | .extend16s => ".extend16s" | .extend32s => ".extend32s"
/-- Integer binary operators. -/
def ibinop : IBinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div s => s!"(.div {sx s})"
  | .rem s => s!"(.rem {sx s})" | .and => ".and" | .or => ".or" | .xor => ".xor"
  | .shl => ".shl" | .shr s => s!"(.shr {sx s})" | .rotl => ".rotl" | .rotr => ".rotr"
/-- Integer relational operators. -/
def irelop : IRelOp → String
  | .eq => ".eq" | .ne => ".ne" | .lt s => s!"(.lt {sx s})" | .gt s => s!"(.gt {sx s})"
  | .le s => s!"(.le {sx s})" | .ge s => s!"(.ge {sx s})"
/-- Float unary operators. -/
def funop : FUnOp → String
  | .abs => ".abs" | .neg => ".neg" | .sqrt => ".sqrt" | .ceil => ".ceil" | .floor => ".floor"
  | .trunc => ".trunc" | .nearest => ".nearest"
/-- Float binary operators. -/
def fbinop : FBinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div" | .min => ".min"
  | .max => ".max" | .copysign => ".copysign"
/-- Float relational operators. -/
def frelop : FRelOp → String
  | .eq => ".eq" | .ne => ".ne" | .lt => ".lt" | .gt => ".gt" | .le => ".le" | .ge => ".ge"
/-- Conversions. -/
def cvtop : CvtOp → String
  | .wrap => ".wrap" | .extend s => s!"(.extend {sx s})"
  | .trunc d r s => s!"(.trunc {width d} {width r} {sx s})"
  | .truncSat d r s => s!"(.truncSat {width d} {width r} {sx s})"
  | .convert d r s => s!"(.convert {width d} {width r} {sx s})"
  | .demote => ".demote" | .promote => ".promote"
  | .reinterpret w b => s!"(.reinterpret {width w} {b})"

mutual
/-- One instruction. -/
def instr : Instr → String
  | .iconst w n => s!".iconst {width w} {n}"
  | .fconst w n => s!".fconst {width w} {n}"
  | .iunop w op => s!".iunop {width w} {iunop op}"
  | .ibinop w op => s!".ibinop {width w} {ibinop op}"
  | .itestEqz w => s!".itestEqz {width w}"
  | .irelop w op => s!".irelop {width w} {irelop op}"
  | .funop w op => s!".funop {width w} {funop op}"
  | .fbinop w op => s!".fbinop {width w} {fbinop op}"
  | .frelop w op => s!".frelop {width w} {frelop op}"
  | .cvtop op => s!".cvtop {cvtop op}"
  | .refNull t => s!".refNull {refType t}"
  | .refIsNull => ".refIsNull"
  | .refFunc x => s!".refFunc {x}"
  | .drop => ".drop"
  | .select none => ".select none"
  | .select (some ts) => s!".select (some {list (ts.map fun t => paren (valType t))})"
  | .localGet x => s!".localGet {x}" | .localSet x => s!".localSet {x}"
  | .localTee x => s!".localTee {x}" | .globalGet x => s!".globalGet {x}"
  | .globalSet x => s!".globalSet {x}" | .tableGet x => s!".tableGet {x}"
  | .tableSet x => s!".tableSet {x}" | .tableSize x => s!".tableSize {x}"
  | .tableGrow x => s!".tableGrow {x}" | .tableFill x => s!".tableFill {x}"
  | .tableCopy x y => s!".tableCopy {x} {y}" | .tableInit x y => s!".tableInit {x} {y}"
  | .elemDrop x => s!".elemDrop {x}"
  | .load t m => s!".load {numType t} {memArg m}"
  | .loadPacked w p s m => s!".loadPacked {width w} {packSize p} {sx s} {memArg m}"
  | .store t m => s!".store {numType t} {memArg m}"
  | .storePacked w p m => s!".storePacked {width w} {packSize p} {memArg m}"
  | .memorySize => ".memorySize" | .memoryGrow => ".memoryGrow"
  | .memoryFill => ".memoryFill" | .memoryCopy => ".memoryCopy"
  | .memoryInit x => s!".memoryInit {x}" | .dataDrop x => s!".dataDrop {x}"
  | .unreachable => ".unreachable" | .nop => ".nop"
  | .block bt b => s!".block {blockType bt} {instrs b}"
  | .loop bt b => s!".loop {blockType bt} {instrs b}"
  | .if_ bt t e => s!".if_ {blockType bt} {instrs t} {instrs e}"
  | .br l => s!".br {l}" | .brIf l => s!".brIf {l}"
  | .brTable ls l => s!".brTable {list (ls.map toString)} {l}"
  | .return_ => ".return_"
  | .call x => s!".call {x}" | .callIndirect x y => s!".callIndirect {x} {y}"
/-- An instruction sequence, as `(.ofList [...])`. -/
def instrs (is : Instrs) : String := s!"(.ofList {list (instrList is)})"
/-- Rendered instructions of a sequence. -/
def instrList : Instrs → List String
  | .nil => []
  | .cons i is => instr i :: instrList is
end

/-- Limits. -/
def limits (l : Limits) : String :=
  s!"\{ min := {l.min}, max := {match l.max with | none => "none" | some m => s!"some {m}"} }"
/-- Global types. -/
def globalType (g : GlobalType) : String :=
  s!"\{ mutability := {match g.mutability with | .const => ".const" | .var => ".var"}, " ++
  s!"val := {valType g.val} }"
/-- Function types. -/
def funcType (f : FuncType) : String :=
  s!"\{ params := {list (f.params.map valType)}, results := {list (f.results.map valType)} }"
/-- String literal. -/
def str (s : String) : String := s.quote
/-- Import descriptions. -/
def importDesc : ImportDesc → String
  | .func x => s!".func {x}"
  | .table t => s!".table \{ limits := {limits t.limits}, elem := {refType t.elem} }"
  | .mem l => s!".mem {limits l}"
  | .global g => s!".global {globalType g}"
/-- Export descriptions. -/
def exportDesc : ExportDesc → String
  | .func x => s!".func {x}" | .table x => s!".table {x}"
  | .mem x => s!".mem {x}" | .global x => s!".global {x}"
/-- Element modes. -/
def elemMode : ElemMode → String
  | .passive => ".passive" | .declarative => ".declarative"
  | .active t off => s!".active {t} {instrs off}"
/-- Data modes. -/
def dataMode : DataMode → String
  | .passive => ".passive" | .active m off => s!".active {m} {instrs off}"

/-- The whole `Lifted.lean` file for namespace `ns`. -/
def file (ns : String) (bytes : Nat) (len : Nat) (m : Module) : String := Id.run do
  let mut out := s!"/-! Generated by `fva lift` from {len} bytes; `decode_eq` re-checks it.
      -/\n\n" ++
    "import FVA.Impl.Decode\n\nopen FVA.Wasm FVA.Wasm.Decode\n\n" ++
    s!"set_option maxRecDepth 100000\n\nnamespace {ns}\n\n" ++
    s!"/-- The artifact's bytes, little-endian. -/\ndef bytes : Nat := {bytes}\n\n" ++
    s!"/-- The artifact's length in bytes. -/\ndef len : Nat := {len}\n\n"
  for (f, i) in m.funcs.zipIdx do
    out := out ++ s!"/-- Function {i}. -/\ndef func{i} : Func :=\n  \{ type := {f.type}, " ++
      s!"locals := {list (f.locals.map valType)},\n    body := {instrs f.body} }\n\n"
  let funcs := list ((List.range m.funcs.length).map fun i => s!"func{i}")
  out := out ++ "/-- The decoded module. -/\ndef module : Module :=\n" ++
    s!"  \{ types := {list (m.types.map funcType)},\n" ++
    s!"    funcs := {funcs},\n" ++
    s!"    tables := {list (m.tables.map fun t =>
      s!"\{ limits := {limits t.limits}, elem := {refType t.elem} }")},\n" ++
    s!"    mems := {list (m.mems.map limits)},\n" ++
    s!"    globals := {list (m.globals.map fun g =>
      s!"\{ type := {globalType g.type}, init := {instrs g.init} }")},\n" ++
    s!"    elems := {list (m.elems.map fun e =>
      s!"\{ type := {refType e.type}, init := {list (e.init.map instrs)}, " ++
      s!"mode := {elemMode e.mode} }")},\n" ++
    s!"    datas := {list (m.datas.map fun d =>
      s!"\{ init := {list (d.init.map toString)}, mode := {dataMode d.mode} }")},\n" ++
    s!"    start := {match m.start with | none => "none" | some x => s!"some {x}"},\n" ++
    s!"    imports := {list (m.imports.map fun im =>
      s!"\{ module := {str im.module}, name := {str im.name}, desc := {importDesc im.desc}
          }")},\n" ++
    s!"    exports := {list (m.exports.map fun ex =>
      s!"\{ name := {str ex.name}, desc := {exportDesc ex.desc} }")} }\n\n" ++
    "/-- The kernel evaluates the verified decoder on `bytes`. -/\n" ++
    "theorem decode_eq : decode bytes len = .ok module := by decide +kernel\n\n" ++
    s!"end {ns}\n"
  return out

end FVA.Tool.Lift
