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
/-- Abstract heap types. -/
def absHeapType : AbsHeapType → String
  | .func => "AbsHeapType.func" | .extern => "AbsHeapType.extern" | .exn => "AbsHeapType.exn"
mutual
/-- Heap types (a decoded module never holds a closed form; printed for totality). -/
def heapType : HeapType → String
  | .abs a => app "HeapType.abs" [absHeapType a]
  | .idx x => app "HeapType.idx" [toString x]
  | .def_ d => app "HeapType.def_" [defType d]
  | .rec_ i => app "HeapType.rec_" [toString i]
  termination_by structural h => h
/-- Reference types (the 2.0 abbreviations where one applies). -/
def refType : RefType → String
  | ⟨true, .abs .func⟩ => "RefType.funcref"
  | ⟨true, .abs .extern⟩ => "RefType.externref"
  | ⟨true, .abs .exn⟩ => "RefType.exnref"
  | ⟨n, h⟩ => app "RefType.mk" [toString n, heapType h]
  termination_by structural t => t
/-- Value types. -/
def valType : ValType → String
  | .num t => app "ValType.num" [numType t]
  | .ref t => app "ValType.ref" [refType t]
  termination_by structural t => t
/-- Value types, one rendered entry each. -/
def valTypes : List ValType → List String
  | [] => []
  | t :: ts => valType t :: valTypes ts
  termination_by structural ts => ts
/-- Function types. -/
def funcType : FuncType → String
  | ⟨ps, rs⟩ => app "FuncType.mk" [list (valTypes ps), list (valTypes rs)]
  termination_by structural f => f
/-- Function types, one rendered entry each. -/
def funcTypes : List FuncType → List String
  | [] => []
  | f :: fs => funcType f :: funcTypes fs
  termination_by structural fs => fs
/-- Defined types. -/
def defType : DefType → String
  | ⟨g, i⟩ => app "DefType.mk" [list (funcTypes g), toString i]
  termination_by structural d => d
end
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

/-- Handler clauses. -/
def catch_ : Catch → String
  | .tag x l => app "Catch.tag" [toString x, toString l]
  | .tagRef x l => app "Catch.tagRef" [toString x, toString l]
  | .all l => app "Catch.all" [toString l] | .allRef l => app "Catch.allRef" [toString l]

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
  | .refNull t => ins "refNull" [heapType t]
  | .refIsNull => ins "refIsNull" []
  | .refFunc x => ins "refFunc" [toString x]
  | .refAsNonNull => ins "refAsNonNull" []
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
  | .callRef x => ins "callRef" [toString x] | .returnCall x => ins "returnCall" [toString x]
  | .returnCallIndirect x y => ins "returnCallIndirect" [toString x, toString y]
  | .returnCallRef x => ins "returnCallRef" [toString x]
  | .brOnNull l => ins "brOnNull" [toString l] | .brOnNonNull l => ins "brOnNonNull" [toString l]
  | .throw x => ins "throw" [toString x] | .throwRef => ins "throwRef" []
  | .tryTable bt cs b => ins "tryTable" [blockType bt, list (cs.map catch_), list (instrList b)]
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
/-- Table types. -/
def tableType (t : TableType) : String := app "TableType.mk" [limits t.limits, refType t.elem]
/-- Import descriptions. -/
def importDesc : ImportDesc → String
  | .func x => app "ImportDesc.func" [toString x]
  | .table t => app "ImportDesc.table" [tableType t]
  | .mem l => app "ImportDesc.mem" [limits l]
  | .global g => app "ImportDesc.global" [globalType g]
  | .tag x => app "ImportDesc.tag" [toString x]
/-- Export descriptions. -/
def exportDesc : ExportDesc → String
  | .func x => app "ExportDesc.func" [toString x] | .table x => app "ExportDesc.table" [toString x]
  | .mem x => app "ExportDesc.mem" [toString x] | .global x => app "ExportDesc.global" [toString x]
  | .tag x => app "ExportDesc.tag" [toString x]
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

/-- When `decode_eq` is assembled from chunks (U29c, frozen after its measurements): one kernel
evaluation of the decoder stops near 0.5 MB of code in a 16 GiB kernel, so a code section whose
content exceeds `threshold` bytes is split into greedy chunks of whole entries (an entry = its
size LEB + content), each at most `target` bytes or one larger entry alone. Boundaries follow
from the bytes + policy alone, so a re-lift (`fva trust`) reproduces the file. -/
structure Chunking where
  /-- Code section content, in bytes, above which `decode_eq` is assembled from chunks. -/
  threshold : Nat := 131072
  /-- Entry bytes per chunk. -/
  target : Nat := 32768

/-- Byte `i` (`0` past the end: the walks below read a module that decoded). -/
def byteAt (bs : ByteArray) (i : Nat) : Nat := (bs.data.getD i 0).toNat

/-- The unsigned LEB128 at `o` (at most 5 bytes, as the decoder's `u32`): value and width. -/
def leb (bs : ByteArray) (o : Nat) : Nat × Nat := Id.run do
  let mut v := 0
  for i in [0:5] do
    let b := byteAt bs (o + i)
    v := v + b % 128 * 128 ^ i
    if b < 128 then return (v, i + 1)
  return (v, 5)

/-- A section: its id, the offset of its id byte, the width of its size LEB, its size. -/
structure Sec where
  id : Nat
  off : Nat
  w : Nat
  size : Nat

/-- The offset of a section's content. -/
def Sec.start (s : Sec) : Nat := s.off + 1 + s.w

/-- The offset past a section's end. -/
def Sec.stop (s : Sec) : Nat := s.start + s.size

/-- The sections after the 8-byte header, in file order. -/
def sections (bs : ByteArray) : Array Sec := Id.run do
  let mut o := 8
  let mut out := #[]
  for _ in [0:bs.size] do
    if bs.size ≤ o then break
    let (size, w) := leb bs (o + 1)
    let s : Sec := { id := byteAt bs o, off := o, w, size }
    out := out.push s
    o := s.stop
  return out

/-- A code section's entries: file offset + bytes (size LEB + content) each. -/
def codeEntries (bs : ByteArray) (s : Sec) : Array (Nat × Nat) := Id.run do
  let (count, cw) := leb bs s.start
  let mut o := s.start + cw
  let mut out := #[]
  for _ in [0:count] do
    if s.stop ≤ o then break
    let (k, w) := leb bs o
    out := out.push (o, w + k)
    o := o + w + k
  return out

/-- Consecutive code entries: the first one's index, their count, file offset and bytes. -/
structure Chunk where
  first : Nat
  count : Nat
  off : Nat
  size : Nat

/-- Greedy chunks: each takes entries while it stays within `target` bytes; an entry larger than
`target` forms a chunk alone. -/
def chunks (target : Nat) (es : Array (Nat × Nat)) : Array Chunk := Id.run do
  let mut out := #[]
  let mut cur : Option Chunk := none
  let mut i := 0
  for (o, k) in es do
    match cur with
    | some c =>
      if c.size + k ≤ target then
        cur := some { c with count := c.count + 1, size := c.size + k }
      else
        out := out.push c
        cur := some { first := i, count := 1, off := o, size := k }
    | none => cur := some { first := i, count := 1, off := o, size := k }
    i := i + 1
  if let some c := cur then out := out.push c
  return out

/-- The accumulator after section `id`, from the previous one `a` (`sectionInto`'s update, its
value taken from the rendered module). -/
def accAfter (m : Module) (id : Nat) (a codes : String) : String :=
  let field (f : String) := s!"\{ {a} with m := \{ {a}.m with {f} := module.{f} } }"
  match id with
  | 1 => field "types" | 2 => field "imports" | 4 => field "tables" | 5 => field "mems"
  | 13 => field "tags" | 6 => field "globals" | 7 => field "exports" | 8 => field "start"
  | 9 => field "elems" | 11 => field "datas"
  | 3 => s!"\{ {a} with typeIdxs := module.funcs.map Func.type }"
  | 12 => s!"\{ {a} with dataCount := some {m.datas.length} }"
  | _ => s!"\{ {a} with codes := {codes} }"

/-- The chunked proof of `decode_eq`, when the code section exceeds `c.threshold` bytes: per
chunk a numeral of its entry bytes + their decoding (`kernel_rfl`), stitched by
`Chunk.two_chunks`; per section slot a `Chunk.slot_take`/`slot_skip` step whose facts the kernel
checks on the input's suffixes `tailAt o`; then `Chunk.decode_of_steps`. -/
def chunked (c : Chunking) (bs : ByteArray) (m : Module) : Option String := do
  let secs := sections bs
  let code ← secs.find? (·.id == 10)
  guard (c.threshold < code.size)
  let cs := chunks c.target (codeEntries bs code)
  guard (!cs.isEmpty)
  let entries (k : Chunk) := list ((List.range k.count).map fun i =>
    s!"(func{k.first + i}.locals, func{k.first + i}.body)")
  -- chunks 0…j packed in `two_chunks`' own shape, so each statement matches its proof
  -- syntactically (the elaborator evaluates nothing)
  let offs := cs.foldl (fun acc k => acc.push (acc.back?.getD 0 + k.size)) #[]
  let packed (j : Nat) := " + ".intercalate ((List.range (j + 1)).map fun i =>
    if i == 0 then "code0" else s!"code{i} <<< (8 * {offs[i - 1]!})")
  let codesEqOf (j : Nat) := if j == 0 then "chunk0_eq" else s!"codes{j}_eq"
  let joined (j : Nat) := " ++ ".intercalate ((List.range (j + 1)).map (s!"entries{·}"))
  let mut out := s!"/-! `decode_eq` from {cs.size} chunks: the code section's {code.size} " ++
    s!"bytes exceed {c.threshold}; chunks of at most {c.target} entry bytes. -/\n\n" ++
    "/-- The input after its first `o` bytes. -/\n" ++
    "noncomputable def tailAt (o : Nat) : Nat := Nat.shiftRight bytes (8 * o)\n\n" ++
    "/-- The input's length after its first `o` bytes. -/\n" ++
    "noncomputable def remAt (o : Nat) : Nat := len - o\n\n"
  -- chunks, then their running concatenation
  let mut count := 0
  let mut size := 0
  for (k, j) in cs.toList.zipIdx do
    out := out ++ s!"/-- Code entries {k.first}–{k.first + k.count - 1}. -/\n" ++
      s!"noncomputable def code{j} : Nat := " ++
      s!"wasm_bytes% \"{toHex (bs.extract k.off (k.off + k.size))}\"\n\n" ++
      s!"noncomputable def entries{j} : List (List (Nat × ValType) × Expr) :=\n" ++
      s!"  {entries k}\n\n" ++
      s!"theorem chunk{j}_eq : many code {k.count} code{j} {k.size} = .ok entries{j} 0 0 := " ++
      "by kernel_rfl\n\n"
    if j > 0 then
      out := out ++ s!"theorem codes{j}_eq :\n    many code {count + k.count} ({packed j}) " ++
        s!"{size + k.size} =\n      .ok ({joined j}) 0 0 :=\n" ++
        s!"  Chunk.two_chunks (lo := {packed (j - 1)}) (hi := code{j}) (m := {size}) " ++
        s!"(n := {k.size}) (a := {count}) (b := {k.count})\n" ++
        s!"    (by kernel_rfl) (by kernel_rfl) {codesEqOf (j - 1)} chunk{j}_eq\n\n"
    count := count + k.count
    size := size + k.size
  let last := cs.size - 1
  let (total, cw) := leb bs code.start
  let all := s!"({joined last})"
  out := out ++ "/-- The code section's content: the entry count, then the entries. -/\n" ++
    s!"noncomputable def codeSec : Nat := {packRange bs code.start (code.start + cw)} + " ++
    s!"({packed last}) <<< (8 * {cw})\n\n" ++
    s!"theorem codeVec_eq : vec code codeSec {code.size} = .ok {all} 0 0 :=\n" ++
    s!"  Chunk.vec_of_count (v' := {packed last}) (n' := {size}) (c := {total}) " ++
    s!"(by kernel_rfl) (by decide +kernel)\n    {codesEqOf last}\n\n" ++
    "noncomputable def acc0 : Acc := {}\n\n"
  -- the slot walk, as `slots` reads the input: customs, then the slot's section if present
  let mut o := 8
  let mut acc := 0
  let mut steps : Array String := #[]
  let mut ids := FVA.Wasm.Decode.slotIds
  let mut rest := secs.toList.dropWhile (·.off < 8)
  while true do
    let rest' := rest.dropWhile (·.id == 0)
    let o' := rest'.head?.map (·.off) |>.getD bs.size
    match ids with
    | [] => break
    | id :: more =>
      let v := s!"(v := tailAt {o}) (n := remAt {o}) (v' := tailAt {o'}) (n' := remAt {o'})"
      match rest' with
      | s :: rest'' =>
        if s.id == id then
          let a := s!"acc{acc}"
          out := out ++ s!"noncomputable def acc{acc + 1} : Acc :=\n  {accAfter m id a all}\n\n"
          let hs := if id == 10 then
              s!"(Chunk.sub_of_leNat (v := tailAt {s.start}) (n := remAt {s.start}) " ++
              s!"(r := tailAt {s.stop}) (by kernel_rfl) (Chunk.code_section codeVec_eq))"
            else "(by kernel_rfl)"
          steps := steps.push (s!"    _ = slots {more} acc{acc + 1} (tailAt {s.stop}) " ++
            s!"(remAt {s.stop}) :=\n      Chunk.slot_take (id := {id}) (ids := {more}) " ++
            s!"(a := {a}) (a' := acc{acc + 1}) {v} (w := tailAt {s.off + 1}) " ++
            s!"(r := remAt {s.off + 1}) (s := {s.size}) (x := tailAt {s.start}) " ++
            s!"(y := remAt {s.start}) (t := tailAt {s.stop})\n        (by kernel_rfl) " ++
            s!"(by kernel_rfl) (by kernel_rfl) (by kernel_rfl) {hs}")
          acc := acc + 1
          o := s.stop
          rest := rest''
          ids := more
          continue
      | [] => pure ()
      steps := steps.push (s!"    _ = slots {more} acc{acc} (tailAt {o'}) (remAt {o'}) :=\n" ++
        s!"      Chunk.slot_skip (id := {id}) (ids := {more}) (a := acc{acc}) {v}\n" ++
        "        (by kernel_rfl) (by kernel_rfl)")
      o := o'
      rest := rest'
      ids := more
  out := out ++ s!"theorem slots_eq : slots slotIds acc0 (tailAt 8) (remAt 8) = " ++
    s!".ok acc{acc} 0 0 :=\n  calc\n" ++ "\n".intercalate steps.toList ++
    s!"\n    _ = .ok acc{acc} 0 0 := by kernel_rfl\n\n" ++
    "/-- The kernel checks the header, the slot walk and `finish`; each chunk's decoding " ++
    "above. -/\n" ++
    "theorem decode_eq : decode bytes len = .ok module :=\n" ++
    "  Chunk.decode_of_steps (v₁ := tailAt 4) (n₁ := remAt 4) (by kernel_rfl) (by kernel_rfl)\n" ++
    "    slots_eq (by kernel_rfl)\n\n"
  return out

/-- The whole `Lifted.lean` file for namespace `ns`. -/
def file (ns : String) (bytes : ByteArray) (m : Module) (source : String := "")
    (chunking : Chunking := {}) : String := Id.run do
  let len := bytes.size
  let proof := chunked chunking bytes m
  -- one import line either way: `scripts/check-format` finds the header on line 3
  let mut out :=
    (if proof.isSome then "import FVA.Proof.Decode.Chunk\n\n" else "import FVA.Lifted\n\n") ++
    s!"/-! Generated by `fva lift` from {len} bytes; `decode_eq` re-checks it. -/\n\n" ++
    "open FVA.Wasm FVA.Wasm.Decode\n\n" ++
    "set_option maxRecDepth 100000\nset_option linter.all false\n\n" ++
    s!"namespace {ns}\n\n" ++
    "/-- The artifact's bytes (hex in file order), packed little-endian. -/\n" ++
    -- compiling a numeral costs time quadratic in its size (64 KB 7 s, 160 KB 39 s; bustools'
    -- 627 KB: 9 min of a Lake build): a chunked module's runs read its file, so it stays uncompiled
    (if proof.isSome then "noncomputable " else "") ++
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
    s!"  \{ types := {list (m.types.map fun g => list (g.map funcType))},\n" ++
    s!"    funcs := {funcs},\n" ++
    s!"    tables := {list (m.tables.map fun t =>
      app "Table.mk" [tableType t.type, instrs t.init])},\n" ++
    s!"    mems := {list (m.mems.map limits)},\n" ++
    s!"    tags := {list (m.tags.map fun t => app "Tag.mk" [toString t.type])},\n" ++
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
    proof.getD ("/-- The kernel evaluates the verified decoder on `bytes`. -/\n" ++
      "theorem decode_eq : decode bytes len = .ok module := by kernel_rfl\n\n") ++
    s!"end {ns}\n"
  return out

end FVA.Tool.Lift
