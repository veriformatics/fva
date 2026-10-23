import FVA.Spec.Exec.Step

/-!
# Instruction typing (reviewed spec; contract U6 T1)

Transcribes WebAssembly 2.0 §3.1–§3.3 (validation of instructions) for FVA's profile, SIMD
excluded, rule by rule. Stack types range over operand types: a value type or `⊥` (bottom,
unconstrained in unreachable code); a stack matches another pointwise (§3.3 "Instructions",
`⊢ t ≤ t'`). Stacks list their operands bottom first, the top last. The raw syntax carries
unbounded `Nat`s, so typing also asks what the binary format guarantees: constants below 2^N,
memory offsets below 2^32, and only the width/operator combinations the format has.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

/-- Operand types (§3.3): a value type, or bottom (`⊥`: unconstrained). -/
inductive OpType where
  | val (t : ValType)
  | bot
  deriving DecidableEq

/-- `⊢ t ≤ t'` (§3.3): an operand type matches itself; bottom matches every operand type. -/
def OpType.Matches : OpType → OpType → Prop
  | .bot, _ => True
  | .val t, .val t' => t = t'
  | .val _, .bot => False

/-- `⊢ [t*] ≤ [t'*]`: pointwise matching. -/
def Matches (ts ts' : List OpType) : Prop := List.Forall₂ OpType.Matches ts ts'

/-- Value types as operand types. -/
def ops (ts : List ValType) : List OpType := ts.map .val

/-- Stack types `[t₁*] → [t₂*]` (§3.3), operands bottom first. -/
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

/-- The operand and result types of a conversion (§3.3.1 `t₂.cvtop_t₁_sx`). -/
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

/-- Validation contexts (§3.1.1). Locals are kept as `(count, type)` runs, as functions declare
them. -/
structure Context where
  /-- Function types. -/
  types : List FuncType := []
  /-- Function types of the functions (imports first). -/
  funcs : List FuncType := []
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
  locals : List (Nat × ValType) := []
  /-- Label result types, innermost first. -/
  labels : List (List ValType) := []
  /-- The return type, if a `return` is allowed. -/
  return_ : Option (List ValType) := none
  /-- Function indices `ref.func` may name. -/
  refs : List Nat := []

/-- The type of local `x` among the runs: `C.locals[x]`. -/
def localAt : List (Nat × ValType) → Nat → Option ValType
  | [], _ => none
  | (n, t) :: rest, x => if x < n then some t else localAt rest (x - n)

/-- `C, labels [ts]`: a new innermost label. -/
def Context.withLabel (C : Context) (ts : List ValType) : Context :=
  { C with labels := ts :: C.labels }

/-- `C ⊢ blocktype : [t₁*] → [t₂*]` (§3.2.2). -/
def Context.blockType (C : Context) : BlockType → Option FuncType
  | .empty => some ⟨[], []⟩
  | .val t => some ⟨[], [t]⟩
  | .idx x => C.types[x]?

/-- A memory argument within the format's bounds, aligned to at most `bytes` (§3.3.7). -/
def _root_.FVA.Wasm.MemArg.WF (m : MemArg) (bytes : Nat) : Prop :=
  2 ^ m.align ≤ bytes ∧ m.offset < 2 ^ 32

mutual

/-- `C ⊢ instr : [t₁*] → [t₂*]` (§3.3). -/
inductive InstrT : Context → Instr → StackType → Prop where
  -- numeric (§3.3.1)
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
  -- reference (§3.3.2)
  | refNull {C} {t : RefType} : InstrT C (.refNull t) ⟨[], [.val (.ref t)]⟩
  | refIsNull {C} {t : RefType} : InstrT C .refIsNull ⟨[.val (.ref t)], [i32]⟩
  | refFunc {C : Context} {x : Nat} {ft : FuncType} (hf : C.funcs[x]? = some ft)
      (hr : x ∈ C.refs) : InstrT C (.refFunc x) ⟨[], [.val (.ref .funcref)]⟩
  -- parametric (§3.3.4)
  | drop {C} {t : OpType} : InstrT C .drop ⟨[t], []⟩
  | select {C} {t : OpType} (h : t = .bot ∨ ∃ n, t = .val (.num n)) :
      InstrT C (.select none) ⟨[t, t, i32], [t]⟩
  | selectT {C} {t : ValType} :
      InstrT C (.select (some [t])) ⟨[.val t, .val t, i32], [.val t]⟩
  -- variable (§3.3.5)
  | localGet {C : Context} {x : Nat} {t : ValType} (h : localAt C.locals x = some t) :
      InstrT C (.localGet x) ⟨[], [.val t]⟩
  | localSet {C : Context} {x : Nat} {t : ValType} (h : localAt C.locals x = some t) :
      InstrT C (.localSet x) ⟨[.val t], []⟩
  | localTee {C : Context} {x : Nat} {t : ValType} (h : localAt C.locals x = some t) :
      InstrT C (.localTee x) ⟨[.val t], [.val t]⟩
  | globalGet {C : Context} {x : Nat} {gt : GlobalType} (h : C.globals[x]? = some gt) :
      InstrT C (.globalGet x) ⟨[], [.val gt.val]⟩
  | globalSet {C : Context} {x : Nat} {t : ValType} (h : C.globals[x]? = some ⟨.var, t⟩) :
      InstrT C (.globalSet x) ⟨[.val t], []⟩
  -- table (§3.3.6)
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
      (hy : C.tables[y]? = some ty) (h : tx.elem = ty.elem) :
      InstrT C (.tableCopy x y) ⟨[i32, i32, i32], []⟩
  | tableInit {C : Context} {x y : Nat} {tt : TableType} {rt : RefType}
      (hx : C.tables[x]? = some tt) (hy : C.elems[y]? = some rt) (h : tt.elem = rt) :
      InstrT C (.tableInit x y) ⟨[i32, i32, i32], []⟩
  | elemDrop {C : Context} {x : Nat} {rt : RefType} (h : C.elems[x]? = some rt) :
      InstrT C (.elemDrop x) ⟨[], []⟩
  -- memory (§3.3.7)
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
  -- control (§3.3.8)
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
  | return_ {C : Context} {ts : List ValType} {t₁ t₂ : List OpType} (h : C.return_ = some ts) :
      InstrT C .return_ ⟨t₁ ++ ops ts, t₂⟩
  | call {C : Context} {x : Nat} {ft : FuncType} (h : C.funcs[x]? = some ft) :
      InstrT C (.call x) ⟨ops ft.params, ops ft.results⟩
  | callIndirect {C : Context} {x y : Nat} {tt : TableType} {ft : FuncType}
      (ht : C.tables[x]? = some tt) (he : tt.elem = .funcref) (hy : C.types[y]? = some ft) :
      InstrT C (.callIndirect x y) ⟨ops ft.params ++ [i32], ops ft.results⟩

/-- `C ⊢ instr* : [t₁*] → [t₂*]` (§3.3.9): the empty sequence keeps any stack; `instr* instr_N`
composes when the top of `instr*`'s result matches `instr_N`'s operands; a result may be read
at any type it matches (`sub`). The wg-2.0 text composes by matching but requires exact results
at block and function boundaries, so `unreachable select` (result `⊥`) types as a function body
yet not as the body of a `block (result funcref)`, while the appendix algorithm and engines
accept both; `sub` restores the algorithm's reading. A `⊥` result only arises after an
instruction that never falls through, so it never meets a value at run time. -/
inductive SeqT : Context → List Instr → StackType → Prop where
  | nil {C} {ts : List OpType} : SeqT C [] ⟨ts, ts⟩
  | snoc {C} {is : List Instr} {i : Instr} {t₁ t₀ t' t t₃ : List OpType}
      (hs : SeqT C is ⟨t₁, t₀ ++ t'⟩) (hm : Matches t' t) (hi : InstrT C i ⟨t, t₃⟩) :
      SeqT C (is ++ [i]) ⟨t₁, t₀ ++ t₃⟩
  | sub {C} {is : List Instr} {t₁ t₂ t₂' : List OpType} (hs : SeqT C is ⟨t₁, t₂⟩)
      (hm : Matches t₂ t₂') : SeqT C is ⟨t₁, t₂'⟩

end

/-- `C ⊢ expr : [t*]` (§3.3.10): the body leaves operands matching `t*`. -/
def ExprT (C : Context) (e : Expr) (ts : List ValType) : Prop :=
  ∃ t', SeqT C e ⟨[], t'⟩ ∧ Matches t' (ops ts)

/-- `C ⊢ instr const` (§3.3.10): a constant, `ref.null`, `ref.func`, or `global.get` of an
immutable global. -/
def ConstInstr (C : Context) : Instr → Prop
  | .iconst _ _ | .fconst _ _ | .refNull _ | .refFunc _ => True
  | .globalGet x => ∃ t, C.globals[x]? = some ⟨.const, t⟩
  | _ => False

/-- `C ⊢ expr const`. -/
def ConstExpr (C : Context) (e : Expr) : Prop := ∀ i ∈ e, ConstInstr C i

end FVA.Wasm.Valid
