import FVA.Tool.Decode

/-!
# `fva lift`: render a decoded module as a Lean file whose `decode_eq` the kernel re-checks

The printer is untrusted: `decode_eq : decode bytes len = .ok module` is proved by the kernel
evaluating the verified decoder on the byte literal, so a printer bug fails the proof instead of
misstating the module. Constructors print fully qualified (`Instr.localGet 0`): on 6,000
instructions dot notation (`.localGet 0`) costs 6.2 s of parsing and 3.3 s of elaboration,
qualified names 0.1 s and 1.8 s. Definitions are `noncomputable` because nothing runs them and
code generation for a large module term costs more than its elaboration.
-/

namespace FVA.Tool.Lift

open FVA.Wasm

/-- Lean syntax for a list, one rendered element per entry. -/
def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- A constructor applied to rendered arguments, parenthesized when it has any. -/
def app (c : String) : List String → String
  | [] => c
  | args => "(" ++ " ".intercalate (c :: args) ++ ")"

/-- Widths. -/
def width : Width → String | .w32 => "Width.w32" | .w64 => "Width.w64"
/-- Signedness. -/
def sx : Sx → String | .s => "Sx.s" | .u => "Sx.u"
/-- Number types. -/
def numType : NumType → String
  | .i32 => "NumType.i32" | .i64 => "NumType.i64" | .f32 => "NumType.f32" | .f64 => "NumType.f64"
/-- Reference types. -/
def refType : RefType → String | .funcref => "RefType.funcref" | .externref => "RefType.externref"
/-- Value types. -/
def valType : ValType → String
  | .num t => app "ValType.num" [numType t] | .ref t => app "ValType.ref" [refType t]
/-- Block types. -/
def blockType : BlockType → String
  | .empty => "BlockType.empty" | .val t => app "BlockType.val" [valType t]
  | .idx x => app "BlockType.idx" [toString x]
/-- Memory arguments. -/
def memArg (m : MemArg) : String := app "MemArg.mk" [toString m.align, toString m.offset]
/-- Packed sizes. -/
def packSize : PackSize → String
  | .p8 => "PackSize.p8" | .p16 => "PackSize.p16" | .p32 => "PackSize.p32"

/-- Integer unary operators. -/
def iunop : IUnOp → String
  | .clz => "IUnOp.clz" | .ctz => "IUnOp.ctz" | .popcnt => "IUnOp.popcnt"
  | .extend8s => "IUnOp.extend8s" | .extend16s => "IUnOp.extend16s"
  | .extend32s => "IUnOp.extend32s"
/-- Integer binary operators. -/
def ibinop : IBinOp → String
  | .add => "IBinOp.add" | .sub => "IBinOp.sub" | .mul => "IBinOp.mul"
  | .div x => app "IBinOp.div" [sx x] | .rem x => app "IBinOp.rem" [sx x]
  | .and => "IBinOp.and" | .or => "IBinOp.or" | .xor => "IBinOp.xor" | .shl => "IBinOp.shl"
  | .shr x => app "IBinOp.shr" [sx x] | .rotl => "IBinOp.rotl" | .rotr => "IBinOp.rotr"
/-- Integer relational operators. -/
def irelop : IRelOp → String
  | .eq => "IRelOp.eq" | .ne => "IRelOp.ne" | .lt x => app "IRelOp.lt" [sx x]
  | .gt x => app "IRelOp.gt" [sx x] | .le x => app "IRelOp.le" [sx x]
  | .ge x => app "IRelOp.ge" [sx x]
/-- Float unary operators. -/
def funop : FUnOp → String
  | .abs => "FUnOp.abs" | .neg => "FUnOp.neg" | .sqrt => "FUnOp.sqrt" | .ceil => "FUnOp.ceil"
  | .floor => "FUnOp.floor" | .trunc => "FUnOp.trunc" | .nearest => "FUnOp.nearest"
/-- Float binary operators. -/
def fbinop : FBinOp → String
  | .add => "FBinOp.add" | .sub => "FBinOp.sub" | .mul => "FBinOp.mul" | .div => "FBinOp.div"
  | .min => "FBinOp.min" | .max => "FBinOp.max" | .copysign => "FBinOp.copysign"
/-- Float relational operators. -/
def frelop : FRelOp → String
  | .eq => "FRelOp.eq" | .ne => "FRelOp.ne" | .lt => "FRelOp.lt" | .gt => "FRelOp.gt"
  | .le => "FRelOp.le" | .ge => "FRelOp.ge"
/-- Conversions. -/
def cvtop : CvtOp → String
  | .wrap => "CvtOp.wrap" | .extend x => app "CvtOp.extend" [sx x]
  | .trunc d r x => app "CvtOp.trunc" [width d, width r, sx x]
  | .truncSat d r x => app "CvtOp.truncSat" [width d, width r, sx x]
  | .convert d r x => app "CvtOp.convert" [width d, width r, sx x]
  | .demote => "CvtOp.demote" | .promote => "CvtOp.promote"
  | .reinterpret w b => app "CvtOp.reinterpret" [width w, toString b]

/-- `Instr.c` applied to rendered arguments. -/
def ins (c : String) (args : List String) : String := app ("Instr." ++ c) args

mutual
/-- One instruction. -/
def instr : Instr → String
  | .iconst w n => ins "iconst" [width w, toString n]
  | .fconst w n => ins "fconst" [width w, toString n]
  | .iunop w op => ins "iunop" [width w, iunop op]
  | .ibinop w op => ins "ibinop" [width w, ibinop op]
  | .itestEqz w => ins "itestEqz" [width w]
  | .irelop w op => ins "irelop" [width w, irelop op]
  | .funop w op => ins "funop" [width w, funop op]
  | .fbinop w op => ins "fbinop" [width w, fbinop op]
  | .frelop w op => ins "frelop" [width w, frelop op]
  | .cvtop op => ins "cvtop" [cvtop op]
  | .refNull t => ins "refNull" [refType t]
  | .refIsNull => ins "refIsNull" []
  | .refFunc x => ins "refFunc" [toString x]
  | .drop => ins "drop" []
  | .select none => ins "select" ["none"]
  | .select (some ts) => ins "select" [app "some" [list (ts.map valType)]]
  | .localGet x => ins "localGet" [toString x] | .localSet x => ins "localSet" [toString x]
  | .localTee x => ins "localTee" [toString x] | .globalGet x => ins "globalGet" [toString x]
  | .globalSet x => ins "globalSet" [toString x] | .tableGet x => ins "tableGet" [toString x]
  | .tableSet x => ins "tableSet" [toString x] | .tableSize x => ins "tableSize" [toString x]
  | .tableGrow x => ins "tableGrow" [toString x] | .tableFill x => ins "tableFill" [toString x]
  | .tableCopy x y => ins "tableCopy" [toString x, toString y]
  | .tableInit x y => ins "tableInit" [toString x, toString y]
  | .elemDrop x => ins "elemDrop" [toString x]
  | .load t m => ins "load" [numType t, memArg m]
  | .loadPacked w p x m => ins "loadPacked" [width w, packSize p, sx x, memArg m]
  | .store t m => ins "store" [numType t, memArg m]
  | .storePacked w p m => ins "storePacked" [width w, packSize p, memArg m]
  | .memorySize => ins "memorySize" [] | .memoryGrow => ins "memoryGrow" []
  | .memoryFill => ins "memoryFill" [] | .memoryCopy => ins "memoryCopy" []
  | .memoryInit x => ins "memoryInit" [toString x] | .dataDrop x => ins "dataDrop" [toString x]
  | .unreachable => ins "unreachable" [] | .nop => ins "nop" []
  | .block bt b => ins "block" [blockType bt, list (instrList b)]
  | .loop bt b => ins "loop" [blockType bt, list (instrList b)]
  | .if_ bt t e => ins "if_" [blockType bt, list (instrList t), list (instrList e)]
  | .br l => ins "br" [toString l] | .brIf l => ins "brIf" [toString l]
  | .brTable ls l => ins "brTable" [list (ls.map toString), toString l]
  | .return_ => ins "return_" []
  | .call x => ins "call" [toString x]
  | .callIndirect x y => ins "callIndirect" [toString x, toString y]
/-- Rendered instructions of a sequence. -/
def instrList : List Instr → List String
  | [] => []
  | i :: is => instr i :: instrList is
end

/-- An instruction sequence. -/
def instrs (is : List Instr) : String := list (instrList is)

/-- Limits. -/
def limits (l : Limits) : String :=
  app "Limits.mk" [toString l.min,
    match l.max with | none => "none" | some m => app "some" [toString m]]
/-- Global types. -/
def globalType (g : GlobalType) : String :=
  app "GlobalType.mk" [match g.mutability with | .const => "Mut.const" | .var => "Mut.var",
    valType g.val]
/-- Function types. -/
def funcType (f : FuncType) : String :=
  app "FuncType.mk" [list (f.params.map valType), list (f.results.map valType)]
/-- Table types. -/
def tableType (t : TableType) : String := app "TableType.mk" [limits t.limits, refType t.elem]
/-- Import descriptions. -/
def importDesc : ImportDesc → String
  | .func x => app "ImportDesc.func" [toString x]
  | .table t => app "ImportDesc.table" [tableType t]
  | .mem l => app "ImportDesc.mem" [limits l]
  | .global g => app "ImportDesc.global" [globalType g]
/-- Export descriptions. -/
def exportDesc : ExportDesc → String
  | .func x => app "ExportDesc.func" [toString x] | .table x => app "ExportDesc.table" [toString x]
  | .mem x => app "ExportDesc.mem" [toString x] | .global x => app "ExportDesc.global" [toString x]
/-- Element modes. -/
def elemMode : ElemMode → String
  | .passive => "ElemMode.passive" | .declarative => "ElemMode.declarative"
  | .active t off => app "ElemMode.active" [toString t, instrs off]
/-- Data modes. -/
def dataMode : DataMode → String
  | .passive => "DataMode.passive" | .active m off => app "DataMode.active" [toString m, instrs off]
/-- Data bytes as the `leBytes` numeral the decoder produces. -/
def dataBytes (bs : List UInt8) : String :=
  app "Binary.leBytes" [toString bs.length, s!"(wasm_bytes% \"{toHex ⟨bs.toArray⟩}\")"]
/-- `(count, type)` local runs. -/
def localRuns (ls : List (Nat × ValType)) : String :=
  list (ls.map fun (k, t) => s!"({k}, {valType t})")

/-- The whole `Lifted.lean` file for namespace `ns`. -/
def file (ns : String) (bytes : ByteArray) (m : Module) (source : String := "") :
    String := Id.run do
  let len := bytes.size
  let mut out := "import FVA.Lifted\n\n" ++
    s!"/-! Generated by `fva lift` from {len} bytes; `decode_eq` re-checks it. -/\n\n" ++
    "open FVA.Wasm FVA.Wasm.Decode\n\n" ++
    "set_option maxRecDepth 100000\nset_option linter.all false\n\n" ++
    s!"namespace {ns}\n\n" ++
    "/-- The artifact's bytes (hex in file order), packed little-endian. -/\n" ++
    s!"def bytes : Nat := wasm_bytes% \"{toHex bytes}\"\n\n" ++
    s!"/-- The artifact's length in bytes. -/\ndef len : Nat := {len}\n\n" ++
    "/-- The artifact's path from the project root (`fva trust` compares its bytes). -/\n" ++
    s!"def source : String := {source.quote}\n\n"
  for (f, i) in m.funcs.zipIdx do
    out := out ++ s!"/-- Function {i}. -/\nnoncomputable def func{i} : Func :=\n" ++
      s!"  \{ type := {f.type}, locals := {localRuns f.locals},\n" ++
      s!"    body := {instrs f.body} }\n\n"
  let funcs := list ((List.range m.funcs.length).map fun i => s!"func{i}")
  out := out ++ "/-- The decoded module. -/\nnoncomputable def module : Module :=\n" ++
    s!"  \{ types := {list (m.types.map funcType)},\n" ++
    s!"    funcs := {funcs},\n" ++
    s!"    tables := {list (m.tables.map tableType)},\n" ++
    s!"    mems := {list (m.mems.map limits)},\n" ++
    s!"    globals := {list (m.globals.map fun g =>
      app "Global.mk" [globalType g.type, instrs g.init])},\n" ++
    s!"    elems := {list (m.elems.map fun e =>
      app "Elem.mk" [refType e.type, list (e.init.map instrs), elemMode e.mode])},\n" ++
    s!"    datas := {list (m.datas.map fun d =>
      app "Data.mk" [dataBytes d.init, dataMode d.mode])},\n" ++
    s!"    start := {match m.start with | none => "none" | some x => app "some" [toString x]},\n" ++
    s!"    imports := {list (m.imports.map fun im =>
      app "Import.mk" [im.module.quote, im.name.quote, importDesc im.desc])},\n" ++
    s!"    exports := {list (m.exports.map fun ex =>
      app "Export.mk" [ex.name.quote, exportDesc ex.desc])} }\n\n" ++
    "/-- The kernel evaluates the verified decoder on `bytes`. -/\n" ++
    "theorem decode_eq : decode bytes len = .ok module := by kernel_rfl\n\n" ++
    s!"end {ns}\n"
  return out

end FVA.Tool.Lift
