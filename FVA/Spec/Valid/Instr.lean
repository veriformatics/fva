import FVA.Spec.Exec.Step

/-!
# Instruction typing (reviewed spec; contracts U6 T1, U28c V1–V4)

Transcribes WebAssembly 3.0 SpecTec `859d3232` `2.3` (validation of instructions) for profile P′,
rule by rule, SIMD and GC excluded. Contexts hold closed types (`docs/contracts/U28a-profile.md`
A2): a source annotation is valid when it names defined types by index in range (`ValType.Src`),
and typing closes it (`Context.close`). Stack types range over operand types: a value type, `⊥`
(3.0 valtype `BOT`: unconstrained in unreachable code), or the non-null reference of the bottom
heap type (3.0 `REF BOT`: what `ref.as_non_null` and `br_on_null` leave of an unconstrained
operand); a stack matches another pointwise by subtyping (3.0 `2.2`). Stacks list their operands
bottom first, the top last. Locals carry an initialization state (3.0 `SET`/`UNSET`): parameters
and defaultable declared locals start set; `local.set` and `local.tee` set a local for the rest of
their sequence (`Instrs_ok/seq`), never past the end of the enclosing block. The raw syntax
carries unbounded `Nat`s, so typing also asks what the binary format guarantees: constants below
2^N, memory offsets below 2^32, and only the width/operator combinations the format has.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

/-- Operand types (3.0 `2.3`): a value type; bottom (`⊥`: unconstrained); the non-null
reference of the bottom heap type (`REF BOT`). -/
inductive OpType where
  | val (t : ValType)
  | bot
  | refBot

/-- `⊢ t ≤ t'` (3.0 `Valtype_sub`, `/bot`, `Heaptype_sub/bot`): bottom matches every operand
type; the bottom reference matches itself and every reference type; value types by subtyping. -/
def OpType.Matches : OpType → OpType → Prop
  | .bot, _ => True
  | .refBot, .refBot => True
  | .refBot, .val (.ref _) => True
  | .val t, .val t' => t.Sub t'
  | _, _ => False

/-- `⊢ [t*] ≤ [t'*]`: pointwise matching. -/
def Matches (ts ts' : List OpType) : Prop := List.Forall₂ OpType.Matches ts ts'

/-- Value types as operand types. -/
def ops (ts : List ValType) : List OpType := ts.map .val

/-- A reference operand of heap type `h`, `none` = the bottom heap type: non-null whatever
`null` says, as no P′ rule produces a nullable bottom (contract X4). -/
def refOp (null : Bool) : Option HeapType → OpType
  | some h => .val (.ref ⟨null, h⟩)
  | none => .refBot

/-- Stack types `[t₁*] → [t₂*]` (3.0 `instrtype`), operands bottom first. An instruction's
initialization effect (3.0 `->_(x*)`) is its syntax's (`Instr.sets`), so stack types carry none
(contract X1). -/
structure StackType where
  /-- The operands consumed. -/
  ins : List OpType
  /-- The operands produced. -/
  outs : List OpType

/-- `i32` as an operand type. -/
abbrev i32 : OpType := .val (.num .i32)

/-- The integer number type of a width. -/
def _root_.FVA.Wasm.Width.int : Width → NumType
  | .w32 => .i32
  | .w64 => .i64

/-- The float number type of a width. -/
def _root_.FVA.Wasm.Width.float : Width → NumType
  | .w32 => .f32
  | .w64 => .f64

/-- The bit width. -/
def _root_.FVA.Wasm.Width.bits : Width → Nat
  | .w32 => 32
  | .w64 => 64

/-- Integer operand of a width. -/
abbrev int (w : Width) : OpType := .val (.num w.int)

/-- Float operand of a width. -/
abbrev flt (w : Width) : OpType := .val (.num w.float)

/-- The operand and result types of a conversion (`CVTOP nt₁ nt₂ cvtop : nt₂ → nt₁`). -/
def _root_.FVA.Wasm.CvtOp.types : CvtOp → NumType × NumType
  | .wrap => (.i64, .i32)
  | .extend _ => (.i32, .i64)
  | .trunc dst src _ | .truncSat dst src _ => (src.float, dst.int)
  | .convert dst src _ => (src.int, dst.float)
  | .demote => (.f64, .f32)
  | .promote => (.f32, .f64)
  | .reinterpret w true => (w.float, w.int)
  | .reinterpret w false => (w.int, w.float)

/-- Integer unary operators the format has for a width: `i32.extend32_s` does not exist. -/
def _root_.FVA.Wasm.IUnOp.Legal : Width → IUnOp → Prop
  | .w32, .extend32s => False
  | _, _ => True

/-- Packed accesses the format has for a width: `i32.load32_*`/`i32.store32` do not exist. -/
def _root_.FVA.Wasm.PackSize.Legal : Width → PackSize → Prop
  | .w32, .p32 => False
  | _, _ => True

/-- A local's type and initialization state (3.0 `localtype` = `init t`). -/
structure LocalType where
  /-- `SET`: readable from the function's entry. -/
  set : Bool
  /-- The value type. -/
  type : ValType

/-- Validation contexts (3.0 `context`), closed types throughout. Locals are kept as
`(count, type)` runs, as functions declare them; `sets` lists the locals the current sequence
has initialized so far (`$with_locals`). -/
structure Context where
  /-- Defined types. -/
  types : List DefType := []
  /-- Defined types of the functions (imports first). -/
  funcs : List DefType := []
  /-- Defined types of the tags (imports first). -/
  tags : List DefType := []
  /-- Table types (imports first). -/
  tables : List TableType := []
  /-- Memory types (imports first). -/
  mems : List Limits := []
  /-- Global types (imports first). -/
  globals : List GlobalType := []
  /-- Reference types of the element segments. -/
  elems : List RefType := []
  /-- Number of data segments (each `ok`). -/
  datas : Nat := 0
  /-- Locals, as runs `(count, type)` in order. -/
  locals : List (Nat × LocalType) := []
  /-- Locals initialized since the start of the current block. -/
  sets : List Nat := []
  /-- Runtime typing alone (contract X9): the sequence so far holds a `trap` or `throw_ref`, so
  what follows never runs and reads any local. Static typing never sets it. -/
  dead : Bool := false
  /-- Label result types, innermost first. -/
  labels : List (List ValType) := []
  /-- The return type, if a `return` is allowed. -/
  return_ : Option (List ValType) := none
  /-- Function indices `ref.func` may name. -/
  refs : List Nat := []

/-- The type of local `x` among the runs: `C.locals[x]`. -/
def localAt : List (Nat × LocalType) → Nat → Option LocalType
  | [], _ => none
  | (n, t) :: rest, x => if x < n then some t else localAt rest (x - n)

/-- `C, labels [ts]`: a new innermost label. -/
def Context.withLabel (C : Context) (ts : List ValType) : Context :=
  { C with labels := ts :: C.labels }

/-- `$with_locals(C, x*, SET*)`: locals `xs` initialized too (newest first: typing reads
membership alone). -/
def Context.addSets (C : Context) (xs : List Nat) : Context :=
  { C with sets := xs.reverse ++ C.sets }

/-- A source value type closed under the context's defined types (`$clos_valtype`). -/
def Context.close (C : Context) (t : ValType) : ValType := t.mapHeap (closeHeap C.types)

/-- `Expand: C.TYPES[x] ~~ FUNC t₁* → t₂*`. -/
def Context.typeAt (C : Context) (x : Nat) : Option FuncType := C.types[x]?.bind DefType.expand

/-- `Expand: C.FUNCS[x] ~~ FUNC t₁* → t₂*`. -/
def Context.funcType (C : Context) (x : Nat) : Option FuncType := C.funcs[x]?.bind DefType.expand

/-- `Expand: C.TAGS[x] ~~ FUNC t* → ε`'s function type. -/
def Context.tagType (C : Context) (x : Nat) : Option FuncType := C.tags[x]?.bind DefType.expand

/-- `C ⊢ blocktype : [t₁*] → [t₂*]` (`Blocktype_ok`): no result, one valid value type (closed),
or a defined type's expansion. -/
def Context.blockType (C : Context) : BlockType → Option FuncType
  | .empty => some ⟨[], []⟩
  | .val t => if t.Src C.types.length then some ⟨[], [C.close t]⟩ else none
  | .idx x => C.typeAt x

/-- A memory argument within the format's bounds, aligned to at most `bytes` (`Memarg_ok`). -/
def _root_.FVA.Wasm.MemArg.WF (m : MemArg) (bytes : Nat) : Prop :=
  2 ^ m.align ≤ bytes ∧ m.offset < 2 ^ 32

/-- `C ⊢ t₁* ≤ t₂*` (`Resulttype_sub`). -/
def ResultSub (ts ts' : List ValType) : Prop := List.Forall₂ ValType.Sub ts ts'

/-- `(ref exn)`. -/
abbrev exnNonNull : ValType := .ref ⟨false, .abs .exn⟩

/-- `C ⊢ catch : OK` (`Catch_ok`), under the context enclosing `try_table`: the clause's values
(the tag's parameters, then the caught exception for `*_ref`) match the target label's types. -/
def CatchOK (C : Context) : Catch → Prop
  | .tag x l => ∃ ts lts, C.tagType x = some ⟨ts, []⟩ ∧ C.labels[l]? = some lts ∧ ResultSub ts lts
  | .tagRef x l => ∃ ts lts, C.tagType x = some ⟨ts, []⟩ ∧ C.labels[l]? = some lts ∧
      ResultSub (ts ++ [exnNonNull]) lts
  | .all l => C.labels[l]? = some []
  | .allRef l => ∃ lts, C.labels[l]? = some lts ∧ ResultSub [exnNonNull] lts

/-- The locals an instruction initializes for the rest of its sequence (3.0 `->_(x*)` of
`Instr_ok`): `local.set x` and `local.tee x` set `x`; nothing else, block bodies included. -/
def _root_.FVA.Wasm.Instr.sets : Instr → List Nat
  | .localSet x | .localTee x => [x]
  | _ => []

mutual

/-- `C ⊢ instr : [t₁*] → [t₂*]` (`Instr_ok`). -/
inductive InstrT : Context → Instr → StackType → Prop where
  -- numeric
  | iconst {C} {w : Width} {n : Nat} (h : n < 2 ^ w.bits) :
      InstrT C (.iconst w n) ⟨[], [int w]⟩
  | fconst {C} {w : Width} {n : Nat} (h : n < 2 ^ w.bits) :
      InstrT C (.fconst w n) ⟨[], [flt w]⟩
  | iunop {C} {w : Width} {op : IUnOp} (h : IUnOp.Legal w op) :
      InstrT C (.iunop w op) ⟨[int w], [int w]⟩
  | ibinop {C} {w : Width} {op : IBinOp} : InstrT C (.ibinop w op) ⟨[int w, int w], [int w]⟩
  | itestEqz {C} {w : Width} : InstrT C (.itestEqz w) ⟨[int w], [i32]⟩
  | irelop {C} {w : Width} {op : IRelOp} : InstrT C (.irelop w op) ⟨[int w, int w], [i32]⟩
  | funop {C} {w : Width} {op : FUnOp} : InstrT C (.funop w op) ⟨[flt w], [flt w]⟩
  | fbinop {C} {w : Width} {op : FBinOp} : InstrT C (.fbinop w op) ⟨[flt w, flt w], [flt w]⟩
  | frelop {C} {w : Width} {op : FRelOp} : InstrT C (.frelop w op) ⟨[flt w, flt w], [i32]⟩
  | cvtop {C} {op : CvtOp} :
      InstrT C (.cvtop op) ⟨[.val (.num op.types.1)], [.val (.num op.types.2)]⟩
  -- reference
  | refNull {C : Context} {ht : HeapType} (h : ht.Src C.types.length) :
      InstrT C (.refNull ht) ⟨[], [.val (.ref ⟨true, closeHeap C.types ht⟩)]⟩
  | refIsNull {C} {t : RefType} : InstrT C .refIsNull ⟨[.val (.ref t)], [i32]⟩
  | refFunc {C : Context} {x : Nat} {dt : DefType} (hf : C.funcs[x]? = some dt)
      (hr : x ∈ C.refs) : InstrT C (.refFunc x) ⟨[], [.val (.ref ⟨false, .def_ dt⟩)]⟩
  | refAsNonNull {C} {h : Option HeapType} :
      InstrT C .refAsNonNull ⟨[refOp true h], [refOp false h]⟩
  -- parametric
  | drop {C} {t : OpType} : InstrT C .drop ⟨[t], []⟩
  | select {C} {t : OpType} (h : t = .bot ∨ ∃ n, t = .val (.num n)) :
      InstrT C (.select none) ⟨[t, t, i32], [t]⟩
  | selectT {C : Context} {t : ValType} (h : t.Src C.types.length) :
      InstrT C (.select (some [t])) ⟨[.val (C.close t), .val (C.close t), i32], [.val (C.close t)]⟩
  -- variable
  | localGet {C : Context} {x : Nat} {lt : LocalType} (h : localAt C.locals x = some lt)
      (hs : lt.set = true ∨ x ∈ C.sets ∨ C.dead = true) :
      InstrT C (.localGet x) ⟨[], [.val lt.type]⟩
  | localSet {C : Context} {x : Nat} {lt : LocalType} (h : localAt C.locals x = some lt) :
      InstrT C (.localSet x) ⟨[.val lt.type], []⟩
  | localTee {C : Context} {x : Nat} {lt : LocalType} (h : localAt C.locals x = some lt) :
      InstrT C (.localTee x) ⟨[.val lt.type], [.val lt.type]⟩
  | globalGet {C : Context} {x : Nat} {gt : GlobalType} (h : C.globals[x]? = some gt) :
      InstrT C (.globalGet x) ⟨[], [.val gt.val]⟩
  | globalSet {C : Context} {x : Nat} {t : ValType} (h : C.globals[x]? = some ⟨.var, t⟩) :
      InstrT C (.globalSet x) ⟨[.val t], []⟩
  -- table
  | tableGet {C : Context} {x : Nat} {tt : TableType} (h : C.tables[x]? = some tt) :
      InstrT C (.tableGet x) ⟨[i32], [.val (.ref tt.elem)]⟩
  | tableSet {C : Context} {x : Nat} {tt : TableType} (h : C.tables[x]? = some tt) :
      InstrT C (.tableSet x) ⟨[i32, .val (.ref tt.elem)], []⟩
  | tableSize {C : Context} {x : Nat} {tt : TableType} (h : C.tables[x]? = some tt) :
      InstrT C (.tableSize x) ⟨[], [i32]⟩
  | tableGrow {C : Context} {x : Nat} {tt : TableType} (h : C.tables[x]? = some tt) :
      InstrT C (.tableGrow x) ⟨[.val (.ref tt.elem), i32], [i32]⟩
  | tableFill {C : Context} {x : Nat} {tt : TableType} (h : C.tables[x]? = some tt) :
      InstrT C (.tableFill x) ⟨[i32, .val (.ref tt.elem), i32], []⟩
  | tableCopy {C : Context} {x y : Nat} {tx ty : TableType} (hx : C.tables[x]? = some tx)
      (hy : C.tables[y]? = some ty) (h : ValType.Sub (.ref ty.elem) (.ref tx.elem)) :
      InstrT C (.tableCopy x y) ⟨[i32, i32, i32], []⟩
  | tableInit {C : Context} {x y : Nat} {tt : TableType} {rt : RefType}
      (hx : C.tables[x]? = some tt) (hy : C.elems[y]? = some rt)
      (h : ValType.Sub (.ref rt) (.ref tt.elem)) :
      InstrT C (.tableInit x y) ⟨[i32, i32, i32], []⟩
  | elemDrop {C : Context} {x : Nat} {rt : RefType} (h : C.elems[x]? = some rt) :
      InstrT C (.elemDrop x) ⟨[], []⟩
  -- memory
  | load {C : Context} {t : NumType} {m : MemArg} {lim : Limits} (hm : C.mems[0]? = some lim)
      (ha : m.WF t.bytes) : InstrT C (.load t m) ⟨[i32], [.val (.num t)]⟩
  | loadPacked {C : Context} {w : Width} {p : PackSize} {sx : Sx} {m : MemArg} {lim : Limits}
      (hm : C.mems[0]? = some lim) (hl : PackSize.Legal w p) (ha : m.WF (p.bits / 8)) :
      InstrT C (.loadPacked w p sx m) ⟨[i32], [int w]⟩
  | store {C : Context} {t : NumType} {m : MemArg} {lim : Limits} (hm : C.mems[0]? = some lim)
      (ha : m.WF t.bytes) : InstrT C (.store t m) ⟨[i32, .val (.num t)], []⟩
  | storePacked {C : Context} {w : Width} {p : PackSize} {m : MemArg} {lim : Limits}
      (hm : C.mems[0]? = some lim) (hl : PackSize.Legal w p) (ha : m.WF (p.bits / 8)) :
      InstrT C (.storePacked w p m) ⟨[i32, int w], []⟩
  | memorySize {C : Context} {lim : Limits} (hm : C.mems[0]? = some lim) :
      InstrT C .memorySize ⟨[], [i32]⟩
  | memoryGrow {C : Context} {lim : Limits} (hm : C.mems[0]? = some lim) :
      InstrT C .memoryGrow ⟨[i32], [i32]⟩
  | memoryFill {C : Context} {lim : Limits} (hm : C.mems[0]? = some lim) :
      InstrT C .memoryFill ⟨[i32, i32, i32], []⟩
  | memoryCopy {C : Context} {lim : Limits} (hm : C.mems[0]? = some lim) :
      InstrT C .memoryCopy ⟨[i32, i32, i32], []⟩
  | memoryInit {C : Context} {x : Nat} {lim : Limits} (hm : C.mems[0]? = some lim)
      (hd : x < C.datas) : InstrT C (.memoryInit x) ⟨[i32, i32, i32], []⟩
  | dataDrop {C : Context} {x : Nat} (hd : x < C.datas) : InstrT C (.dataDrop x) ⟨[], []⟩
  -- control
  | nop {C} : InstrT C .nop ⟨[], []⟩
  | unreachable {C} {t₁ t₂ : List OpType} : InstrT C .unreachable ⟨t₁, t₂⟩
  | block {C : Context} {bt : BlockType} {body : List Instr} {ft : FuncType}
      (hb : C.blockType bt = some ft)
      (hs : SeqT (C.withLabel ft.results) body ⟨ops ft.params, ops ft.results⟩) :
      InstrT C (.block bt body) ⟨ops ft.params, ops ft.results⟩
  | loop {C : Context} {bt : BlockType} {body : List Instr} {ft : FuncType}
      (hb : C.blockType bt = some ft)
      (hs : SeqT (C.withLabel ft.params) body ⟨ops ft.params, ops ft.results⟩) :
      InstrT C (.loop bt body) ⟨ops ft.params, ops ft.results⟩
  | if_ {C : Context} {bt : BlockType} {thn els : List Instr} {ft : FuncType}
      (hb : C.blockType bt = some ft)
      (h₁ : SeqT (C.withLabel ft.results) thn ⟨ops ft.params, ops ft.results⟩)
      (h₂ : SeqT (C.withLabel ft.results) els ⟨ops ft.params, ops ft.results⟩) :
      InstrT C (.if_ bt thn els) ⟨ops ft.params ++ [i32], ops ft.results⟩
  | br {C : Context} {l : Nat} {ts : List ValType} {t₁ t₂ : List OpType}
      (h : C.labels[l]? = some ts) : InstrT C (.br l) ⟨t₁ ++ ops ts, t₂⟩
  | brIf {C : Context} {l : Nat} {ts : List ValType} (h : C.labels[l]? = some ts) :
      InstrT C (.brIf l) ⟨ops ts ++ [i32], ops ts⟩
  | brTable {C : Context} {ls : List Nat} {l : Nat} {ts t₁ t₂ : List OpType}
      (h : ∀ k ∈ l :: ls, ∃ ts', C.labels[k]? = some ts' ∧ Matches ts (ops ts')) :
      InstrT C (.brTable ls l) ⟨t₁ ++ ts ++ [i32], t₂⟩
  | brOnNull {C : Context} {l : Nat} {ts : List ValType} {h : Option HeapType}
      (hl : C.labels[l]? = some ts) :
      InstrT C (.brOnNull l) ⟨ops ts ++ [refOp true h], ops ts ++ [refOp false h]⟩
  | brOnNonNull {C : Context} {l : Nat} {ts : List ValType} {n : Bool} {h : HeapType}
      (hl : C.labels[l]? = some (ts ++ [.ref ⟨n, h⟩])) :
      InstrT C (.brOnNonNull l) ⟨ops ts ++ [.val (.ref ⟨true, h⟩)], ops ts⟩
  | return_ {C : Context} {ts : List ValType} {t₁ t₂ : List OpType} (h : C.return_ = some ts) :
      InstrT C .return_ ⟨t₁ ++ ops ts, t₂⟩
  | call {C : Context} {x : Nat} {ft : FuncType} (h : C.funcType x = some ft) :
      InstrT C (.call x) ⟨ops ft.params, ops ft.results⟩
  | callIndirect {C : Context} {x y : Nat} {tt : TableType} {ft : FuncType}
      (ht : C.tables[x]? = some tt) (he : ValType.Sub (.ref tt.elem) (.ref .funcref))
      (hy : C.typeAt y = some ft) :
      InstrT C (.callIndirect x y) ⟨ops ft.params ++ [i32], ops ft.results⟩
  | callRef {C : Context} {y : Nat} {dt : DefType} {ft : FuncType} (hy : C.types[y]? = some dt)
      (he : dt.expand = some ft) :
      InstrT C (.callRef y) ⟨ops ft.params ++ [.val (.ref ⟨true, .def_ dt⟩)], ops ft.results⟩
  | returnCall {C : Context} {x : Nat} {ft : FuncType} {rs : List ValType} {t₃ t₄ : List OpType}
      (h : C.funcType x = some ft) (hr : C.return_ = some rs) (hs : ResultSub ft.results rs) :
      InstrT C (.returnCall x) ⟨t₃ ++ ops ft.params, t₄⟩
  | returnCallIndirect {C : Context} {x y : Nat} {tt : TableType} {ft : FuncType}
      {rs : List ValType} {t₃ t₄ : List OpType} (ht : C.tables[x]? = some tt)
      (he : ValType.Sub (.ref tt.elem) (.ref .funcref)) (hy : C.typeAt y = some ft)
      (hr : C.return_ = some rs) (hs : ResultSub ft.results rs) :
      InstrT C (.returnCallIndirect x y) ⟨t₃ ++ ops ft.params ++ [i32], t₄⟩
  | returnCallRef {C : Context} {y : Nat} {dt : DefType} {ft : FuncType} {rs : List ValType}
      {t₃ t₄ : List OpType} (hy : C.types[y]? = some dt) (he : dt.expand = some ft)
      (hr : C.return_ = some rs) (hs : ResultSub ft.results rs) :
      InstrT C (.returnCallRef y) ⟨t₃ ++ ops ft.params ++ [.val (.ref ⟨true, .def_ dt⟩)], t₄⟩
  | throw {C : Context} {x : Nat} {ts : List ValType} {t₁ t₂ : List OpType}
      (h : C.tagType x = some ⟨ts, []⟩) : InstrT C (.throw x) ⟨t₁ ++ ops ts, t₂⟩
  | throwRef {C} {t₁ t₂ : List OpType} : InstrT C .throwRef ⟨t₁ ++ [.val (.ref .exnref)], t₂⟩
  | tryTable {C : Context} {bt : BlockType} {cs : List Catch} {body : List Instr} {ft : FuncType}
      (hb : C.blockType bt = some ft)
      (hs : SeqT (C.withLabel ft.results) body ⟨ops ft.params, ops ft.results⟩)
      (hc : ∀ c ∈ cs, CatchOK C c) :
      InstrT C (.tryTable bt cs body) ⟨ops ft.params, ops ft.results⟩

/-- `C ⊢ instr* : [t₁*] → [t₂*]` (`Instrs_ok`): the empty sequence keeps any stack; `instr*
instr_N` composes when the top of `instr*`'s result matches `instr_N`'s operands, `instr_N` typed
with the locals `instr*` initialized (`/seq`); a result may be read at any type it matches
(`/sub` on results; inputs widen through `snoc`'s matching). A `⊥` result only arises after an
instruction that never falls through, so it never meets a value at run time. -/
inductive SeqT : Context → List Instr → StackType → Prop where
  | nil {C} {ts : List OpType} : SeqT C [] ⟨ts, ts⟩
  | snoc {C : Context} {is : List Instr} {i : Instr} {t₁ t₀ t' t t₃ : List OpType}
      (hs : SeqT C is ⟨t₁, t₀ ++ t'⟩) (hm : Matches t' t)
      (hi : InstrT (C.addSets (is.flatMap Instr.sets)) i ⟨t, t₃⟩) :
      SeqT C (is ++ [i]) ⟨t₁, t₀ ++ t₃⟩
  | sub {C} {is : List Instr} {t₁ t₂ t₂' : List OpType} (hs : SeqT C is ⟨t₁, t₂⟩)
      (hm : Matches t₂ t₂') : SeqT C is ⟨t₁, t₂'⟩

end

/-- `C ⊢ expr : [t*]` (`Expr_ok`): the body leaves operands matching `t*`. -/
def ExprT (C : Context) (e : Expr) (ts : List ValType) : Prop :=
  ∃ t', SeqT C e ⟨[], t'⟩ ∧ Matches t' (ops ts)

/-- `C ⊢ instr const` (`Instr_const`, P′): a number constant, `ref.null`, `ref.func`, or
`global.get` of an immutable global of the context. -/
def ConstInstr (C : Context) : Instr → Prop
  | .iconst _ _ | .fconst _ _ | .refNull _ | .refFunc _ => True
  | .globalGet x => ∃ t, C.globals[x]? = some ⟨.const, t⟩
  | _ => False

/-- `C ⊢ expr const`. -/
def ConstExpr (C : Context) (e : Expr) : Prop := ∀ i ∈ e, ConstInstr C i

end FVA.Wasm.Valid
