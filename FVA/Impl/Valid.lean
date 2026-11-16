import FVA.Spec.Valid.Module
import FVA.Impl.TypeEq

/-!
# WebAssembly validator

The appendix operand/control-stack algorithm over the nested AST, for profile P′. Each recursive
body owns its operand stack; the enclosing context supplies its labels and its view of the
initialized locals. An unreachable empty stack pops bottom, and a reference popped as bottom
becomes the bottom reference (`pop_ref`); explicit operands still undergo every type check.
Typed calls pop the reference first, then the parameters (SpecTec `2.3`; the appendix sketch
reverses them). Local declarations stay as runs; `local.set`/`local.tee` cons their local onto
the context's initialized set (`Context.addSets`), and `local.get` consults it only for a local
its declaration leaves unset.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

deriving instance DecidableEq for OpType

namespace Check

/-- Top-first operands above the current control frame's base. -/
structure Stack where
  /-- Explicit operands, top first; surrounding frames own separate stacks. -/
  types : List OpType := []
  /-- Empty-base pops may synthesize bottom after an unconditional transfer. -/
  unreachable : Bool := false
  deriving DecidableEq

/-- A source heap type naming one of the first `k` defined types (`HeapType.Src`). -/
def heapSrc (k : Nat) : HeapType → Bool
  | .abs _ => true
  | .idx y => Nat.blt y k
  | _ => false

/-- A source value type naming one of the first `k` defined types (`ValType.Src`). -/
def valSrc (k : Nat) : ValType → Bool
  | .num _ => true
  | .ref t => heapSrc k t.heap

/-- Sequentially valid recursive groups (`TypesSeq`). -/
def typesSeq : List RecType → Nat → Bool
  | [], _ => true
  | g :: gs, x => g.all (fun f => f.params.all (valSrc (x + g.length)) &&
      f.results.all (valSrc (x + g.length))) && typesSeq gs (x + g.length)

/-- A defined heap type below `func` (`Heaptype_sub/func`). -/
def defFunc : HeapType → HeapType → Bool
  | .def_ _, .abs .func => true
  | _, _ => false

/-- Boolean `ValType.Sub`. -/
def subType : ValType → ValType → Bool
  | .num a, .num b => a == b
  | .ref ⟨n₁, h₁⟩, .ref ⟨n₂, h₂⟩ => (!n₁ || n₂) && (HeapType.beq h₁ h₂ || defFunc h₁ h₂)
  | _, _ => false

/-- Boolean `ResultSub`: equal lengths, pointwise subtyping. -/
def subTypes : List ValType → List ValType → Bool
  | [], [] => true
  | t :: ts, u :: us => subType t u && subTypes ts us
  | _, _ => false

/-- Boolean operand matching; a bottom operand matches every expected type, the bottom reference
every reference type. -/
def matchType : OpType → OpType → Bool
  | .bot, _ => true
  | .refBot, .refBot => true
  | .refBot, .val (.ref _) => true
  | .val t, .val u => subType t u
  | _, _ => false

/-- Pointwise operand matching; lengths must agree. -/
def matchTypeList : List OpType → List OpType → Bool
  | [], [] => true
  | t :: ts, u :: us => matchType t u && matchTypeList ts us
  | _, _ => false

/-- Pop one operand, synthesizing bottom only at an unreachable frame's base. -/
def pop : Stack → Option (OpType × Stack)
  | ⟨[], false⟩ => none
  | ⟨[], true⟩ => some (.bot, ⟨[], true⟩)
  | ⟨t :: ts, u⟩ => some (t, ⟨ts, u⟩)

/-- Pop top-first expected types, retaining actual types for `br_table`. -/
def pops : List OpType → Stack → Option (List OpType × Stack)
  | [], s => some ([], s)
  | t :: ts, s => match pop s with
    | none => none
    | some (a, rest) => bif matchType a t then
        match pops ts rest with
        | none => none
        | some (as, rest') => some (a :: as, rest')
      else none

/-- Push bottom-first result types. -/
def push (ts : List OpType) (s : Stack) : Stack :=
  { s with types := ts.reverse ++ s.types }

/-- Apply a monomorphic stack signature, framed by the untouched operands. -/
def apply (st : StackType) (s : Stack) : Option Stack :=
  match pops st.ins.reverse s with
  | none => none
  | some (_, rest) => some (push st.outs rest)

/-- Check a control frame's end: result operands match, and no extra operand remains. -/
def finish (ts : List ValType) (s : Stack) : Bool :=
  match pops (ops ts).reverse s with
  | none => false
  | some (_, rest) => rest.types.isEmpty

/-- Kernel-cheap lookup through compressed local runs. -/
def lookupLocal : List (Nat × LocalType) → Nat → Option LocalType
  | [], _ => none
  | (n, t) :: rest, x => bif Nat.blt x n then some t else lookupLocal rest (Nat.sub x n)

/-- The heap type of a reference operand (`pop_ref`): `none` = bottom. -/
def refHeap : OpType → Option (Option HeapType)
  | .bot | .refBot => some none
  | .val (.ref ⟨_, h⟩) => some (some h)
  | _ => none

/-- Representable integer unary operators. -/
def unary : Width → IUnOp → Bool
  | .w32, .extend32s => false
  | _, _ => true

/-- Representable packed accesses. -/
def packed : Width → PackSize → Bool
  | .w32, .p32 => false
  | _, _ => true

/-- The early exponent bound avoids constructing a huge power on a raw invalid AST. -/
def memArg (m : MemArg) (bytes : Nat) : Bool :=
  Nat.ble m.align 3 && Nat.ble (Nat.pow 2 m.align) bytes && Nat.blt m.offset (Nat.pow 2 32)

/-- Block types, closing a valid value type. -/
def blockType (C : Context) : BlockType → Option FuncType
  | .empty => some ⟨[], []⟩
  | .val t => bif valSrc C.types.length t then some ⟨[], [C.close t]⟩ else none
  | .idx x => C.typeAt x

/-- A catch clause's values against its label (`Catch_ok`). -/
def catchOk (C : Context) : Catch → Bool
  | .tag x l => match C.tagType x, C.labels[l]? with
    | some ⟨ts, []⟩, some lts => subTypes ts lts
    | _, _ => false
  | .tagRef x l => match C.tagType x, C.labels[l]? with
    | some ⟨ts, []⟩, some lts => subTypes (ts ++ [exnNonNull]) lts
    | _, _ => false
  | .all l => match C.labels[l]? with
    | some [] => true
    | _ => false
  | .allRef l => match C.labels[l]? with
    | some lts => subTypes [exnNonNull] lts
    | none => false

/-- Fixed-signature instructions, with all context and representation checks. -/
def fixed (C : Context) : Instr → Option StackType
  | .iconst w n => bif Nat.blt n (Nat.pow 2 w.bits) then some ⟨[], [int w]⟩ else none
  | .fconst w n => bif Nat.blt n (Nat.pow 2 w.bits) then some ⟨[], [flt w]⟩ else none
  | .iunop w op => bif unary w op then some ⟨[int w], [int w]⟩ else none
  | .ibinop w _ => some ⟨[int w, int w], [int w]⟩
  | .itestEqz w => some ⟨[int w], [i32]⟩
  | .irelop w _ => some ⟨[int w, int w], [i32]⟩
  | .funop w _ => some ⟨[flt w], [flt w]⟩
  | .fbinop w _ => some ⟨[flt w, flt w], [flt w]⟩
  | .frelop w _ => some ⟨[flt w, flt w], [i32]⟩
  | .cvtop op => some ⟨[.val (.num op.types.1)], [.val (.num op.types.2)]⟩
  | .refNull ht => bif heapSrc C.types.length ht then
      some ⟨[], [.val (.ref ⟨true, closeHeap C.types ht⟩)]⟩ else none
  | .refFunc x => match C.funcs[x]? with
    | none => none
    | some dt => bif C.refs.any (Nat.beq x) then some ⟨[], [.val (.ref ⟨false, .def_ dt⟩)]⟩
      else none
  | .select ts => match ts with
    | some [t] => bif valSrc C.types.length t then
        some ⟨[.val (C.close t), .val (C.close t), i32], [.val (C.close t)]⟩ else none
    | _ => none
  | .localGet x => match lookupLocal C.locals x with
    | none => none
    | some lt => bif lt.set || C.dead || C.sets.any (Nat.beq x) then some ⟨[], [.val lt.type]⟩
      else none
  | .localSet x => (lookupLocal C.locals x).map fun lt => ⟨[.val lt.type], []⟩
  | .localTee x => (lookupLocal C.locals x).map fun lt => ⟨[.val lt.type], [.val lt.type]⟩
  | .globalGet x => (C.globals[x]?).map fun gt => ⟨[], [.val gt.val]⟩
  | .globalSet x => match C.globals[x]? with
    | some ⟨.var, t⟩ => some ⟨[.val t], []⟩
    | _ => none
  | .tableGet x => (C.tables[x]?).map fun tt => ⟨[i32], [.val (.ref tt.elem)]⟩
  | .tableSet x => (C.tables[x]?).map fun tt => ⟨[i32, .val (.ref tt.elem)], []⟩
  | .tableSize x => (C.tables[x]?).map fun _ => ⟨[], [i32]⟩
  | .tableGrow x => (C.tables[x]?).map fun tt => ⟨[.val (.ref tt.elem), i32], [i32]⟩
  | .tableFill x => (C.tables[x]?).map fun tt => ⟨[i32, .val (.ref tt.elem), i32], []⟩
  | .tableCopy x y => match C.tables[x]?, C.tables[y]? with
    | some tx, some ty => bif subType (.ref ty.elem) (.ref tx.elem) then
        some ⟨[i32, i32, i32], []⟩ else none
    | _, _ => none
  | .tableInit x y => match C.tables[x]?, C.elems[y]? with
    | some tt, some rt => bif subType (.ref rt) (.ref tt.elem) then
        some ⟨[i32, i32, i32], []⟩ else none
    | _, _ => none
  | .elemDrop x => (C.elems[x]?).map fun _ => ⟨[], []⟩
  | .load t m => match C.mems[0]? with
    | none => none
    | some _ => bif memArg m t.bytes then some ⟨[i32], [.val (.num t)]⟩ else none
  | .loadPacked w p _ m => match C.mems[0]? with
    | none => none
    | some _ => bif packed w p && memArg m (p.bits / 8) then
        some ⟨[i32], [int w]⟩ else none
  | .store t m => match C.mems[0]? with
    | none => none
    | some _ => bif memArg m t.bytes then some ⟨[i32, .val (.num t)], []⟩ else none
  | .storePacked w p m => match C.mems[0]? with
    | none => none
    | some _ => bif packed w p && memArg m (p.bits / 8) then
        some ⟨[i32, int w], []⟩ else none
  | .memorySize => (C.mems[0]?).map fun _ => ⟨[], [i32]⟩
  | .memoryGrow => (C.mems[0]?).map fun _ => ⟨[i32], [i32]⟩
  | .memoryFill | .memoryCopy => (C.mems[0]?).map fun _ => ⟨[i32, i32, i32], []⟩
  | .memoryInit x => match C.mems[0]? with
    | none => none
    | some _ => bif Nat.blt x C.datas then some ⟨[i32, i32, i32], []⟩ else none
  | .dataDrop x => bif Nat.blt x C.datas then some ⟨[], []⟩ else none
  | .nop => some ⟨[], []⟩
  | .brIf l => (C.labels[l]?).map fun ts => ⟨ops ts ++ [i32], ops ts⟩
  | .brOnNonNull l => match C.labels[l]? with
    | some lts => match lts.getLast? with
      | some (.ref ⟨_, h⟩) => some ⟨ops lts.dropLast ++ [.val (.ref ⟨true, h⟩)], ops lts.dropLast⟩
      | _ => none
    | none => none
  | .call x => (C.funcType x).map fun ft => ⟨ops ft.params, ops ft.results⟩
  | .callIndirect x y => match C.tables[x]?, C.typeAt y with
    | some tt, some ft => bif subType (.ref tt.elem) (.ref .funcref) then
        some ⟨ops ft.params ++ [i32], ops ft.results⟩ else none
    | _, _ => none
  | .callRef y => match C.types[y]? with
    | none => none
    | some dt => dt.expand.map fun ft =>
        ⟨ops ft.params ++ [.val (.ref ⟨true, .def_ dt⟩)], ops ft.results⟩
  | _ => none

/-- Untyped select merges numeric or bottom operands; references require typed select. -/
def selectType : OpType → OpType → Option OpType
  | .bot, .bot => some .bot
  | .bot, .val (.num n) | .val (.num n), .bot => some (.val (.num n))
  | .val (.num n), .val (.num m) =>
    bif decide (n = m) then some (.val (.num n)) else none
  | _, _ => none

/-- An unconditional transfer checks its operands and resets the current frame. -/
def branch (ts : List ValType) (s : Stack) : Option Stack :=
  match pops (ops ts).reverse s with
  | none => none
  | some _ => some ⟨[], true⟩

/-- All table destinations accept the same actual operands, including bottom operands. -/
def targets (C : Context) (as : List OpType) (ls : List Nat) : Bool :=
  ls.all fun k => match C.labels[k]? with
    | none => false
    | some ts => matchTypeList as (ops ts).reverse

/-- A tail call: the callee's results below the caller's, then its operands as a transfer. -/
def tailCall (C : Context) (ft : FuncType) (operands : List ValType) (s : Stack) :
    Option Stack :=
  match C.return_ with
  | none => none
  | some rs => bif subTypes ft.results rs then branch operands s else none

mutual

/-- One instruction; nested bodies start their own operand stack and control frame. -/
def instr (C : Context) (i : Instr) (s : Stack) : Option Stack :=
  match i with
  | .unreachable => some ⟨[], true⟩
  | .drop => (pop s).map fun (_, rest) => rest
  | .refIsNull => match pop s with
    | some (.bot, rest) | some (.refBot, rest) | some (.val (.ref _), rest) =>
      some (push [i32] rest)
    | _ => none
  | .refAsNonNull => match pop s with
    | some (a, _) => match refHeap a with
      | some h => apply ⟨[refOp true h], [refOp false h]⟩ s
      | none => none
    | none => none
  | .select none => match pops [i32] s with
    | none => none
    | some (_, rest) => match pop rest with
      | none => none
      | some (t, rest') => match pop rest' with
        | none => none
        | some (u, rest'') => (selectType t u).map fun v => push [v] rest''
  | .block bt body => match blockType C bt with
    | none => none
    | some ft => match seq (C.withLabel ft.results) body ⟨(ops ft.params).reverse, false⟩ with
      | none => none
      | some out => bif finish ft.results out then apply ⟨ops ft.params, ops ft.results⟩ s
        else none
  | .loop bt body => match blockType C bt with
    | none => none
    | some ft => match seq (C.withLabel ft.params) body ⟨(ops ft.params).reverse, false⟩ with
      | none => none
      | some out => bif finish ft.results out then apply ⟨ops ft.params, ops ft.results⟩ s
        else none
  | .if_ bt thn els => match blockType C bt with
    | none => none
    | some ft =>
      match seq (C.withLabel ft.results) thn ⟨(ops ft.params).reverse, false⟩,
          seq (C.withLabel ft.results) els ⟨(ops ft.params).reverse, false⟩ with
      | some out₁, some out₂ => bif finish ft.results out₁ && finish ft.results out₂ then
          apply ⟨ops ft.params ++ [i32], ops ft.results⟩ s else none
      | _, _ => none
  | .tryTable bt cs body => match blockType C bt with
    | none => none
    | some ft => match seq (C.withLabel ft.results) body ⟨(ops ft.params).reverse, false⟩ with
      | none => none
      | some out => bif finish ft.results out && cs.all (catchOk C) then
          apply ⟨ops ft.params, ops ft.results⟩ s else none
  | .br l => match C.labels[l]? with | none => none | some ts => branch ts s
  | .return_ => match C.return_ with | none => none | some ts => branch ts s
  | .brTable ls l => match C.labels[l]?, pops [i32] s with
    | some ts, some (_, rest) => match pops (ops ts).reverse rest with
      | some (as, _) => bif targets C as ls then some ⟨[], true⟩ else none
      | none => none
    | _, _ => none
  | .brOnNull l => match C.labels[l]?, pop s with
    | some ts, some (a, _) => match refHeap a with
      | some h => apply ⟨ops ts ++ [refOp true h], ops ts ++ [refOp false h]⟩ s
      | none => none
    | _, _ => none
  | .returnCall x => match C.funcType x with
    | none => none
    | some ft => tailCall C ft ft.params s
  | .returnCallIndirect x y => match C.tables[x]?, C.typeAt y with
    | some tt, some ft => bif subType (.ref tt.elem) (.ref .funcref) then
        tailCall C ft (ft.params ++ [.num .i32]) s else none
    | _, _ => none
  | .returnCallRef y => match C.types[y]? with
    | none => none
    | some dt => match dt.expand with
      | none => none
      | some ft => tailCall C ft (ft.params ++ [.ref ⟨true, .def_ dt⟩]) s
  | .throw x => match C.tagType x with
    | some ⟨ts, []⟩ => branch ts s
    | _ => none
  | .throwRef => branch [.ref .exnref] s
  | _ => match fixed C i with | none => none | some st => apply st s

/-- Sequential structural recursion, without flattening nested bodies; each instruction sees
the locals its predecessors initialized. -/
def seq (C : Context) : List Instr → Stack → Option Stack
  | [], s => some s
  | i :: is, s => match instr C i s with | none => none | some s' => seq (C.addSets i.sets) is s'

end

/-- A complete expression starts without operands. -/
def expr (C : Context) (e : Expr) (ts : List ValType) : Bool :=
  match seq C e {} with | none => false | some s => finish ts s

/-- Constant expressions read the context's immutable globals alone. -/
def constant (C : Context) : Instr → Bool
  | .iconst _ _ | .fconst _ _ | .refNull _ | .refFunc _ => true
  | .globalGet x => match C.globals[x]? with | some ⟨.const, _⟩ => true | _ => false
  | _ => false

/-- A typed constant expression. -/
def constExpr (C : Context) (e : Expr) (ts : List ValType) : Bool :=
  e.all (constant C) && expr C e ts

/-- Limits respect the profile's bound and the optional maximum. -/
def limits (k : Nat) (l : Limits) : Bool :=
  Nat.ble l.min k && match l.max with
    | none => true
    | some mx => Nat.ble l.min mx && Nat.ble mx k

/-- A tag's type: a function type without results. -/
def tagType (C : Context) (x : Nat) : Bool :=
  match C.typeAt x with
  | some ⟨_, []⟩ => true
  | _ => false

/-- Import description checks, under the defined types. -/
def importDesc (C : Context) : ImportDesc → Bool
  | .func x => (C.typeAt x).isSome
  | .table tt => limits (2 ^ 32 - 1) tt.limits && heapSrc C.types.length tt.elem.heap
  | .mem lim => limits (2 ^ 16) lim
  | .global gt => valSrc C.types.length gt.val
  | .tag x => tagType C x

/-- Defined globals in order, each under the globals before it (`C` holds the imported ones). -/
def globals (C : Context) (dts : List DefType) : List Global → Bool
  | [] => true
  | g :: gs => valSrc dts.length g.type.val &&
      constExpr C g.init [(g.type.close dts).val] &&
      globals { C with globals := C.globals ++ [g.type.close dts] } dts gs

/-- Function body validation; local declarations stay in compressed runs. -/
def func (C : Context) (f : Func) : Bool :=
  match C.typeAt f.type with
  | none => false
  | some ft => f.locals.all (fun l => valSrc C.types.length l.2) && expr { C with
      locals := ft.params.map (1, ⟨true, ·⟩) ++
        f.locals.map fun l => (l.1, ⟨l.2.defaultable, C.close l.2⟩)
      labels := [ft.results]
      return_ := some ft.results } f.body ft.results

/-- An element segment's mode. -/
def elemMode (C : Context) (t : RefType) : ElemMode → Bool
  | .passive | .declarative => true
  | .active x off => match C.tables[x]? with
    | none => false
    | some tt => subType (.ref t) (.ref tt.elem) && constExpr C off [.num .i32]

/-- A data segment's mode. -/
def dataMode (C : Context) : DataMode → Bool
  | .passive => true
  | .active x off => match C.mems[x]? with
    | none => false
    | some _ => constExpr C off [.num .i32]

/-- Export references are checked in the combined index spaces. -/
def exportDesc (C : Context) : ExportDesc → Bool
  | .func x => Nat.blt x C.funcs.length
  | .table x => Nat.blt x C.tables.length
  | .mem x => Nat.blt x C.mems.length
  | .global x => Nat.blt x C.globals.length
  | .tag x => Nat.blt x C.tags.length

/-- Distinct names, without a hash-table trusted implementation. -/
def distinct : List String → Bool
  | [] => true
  | name :: names => !names.contains name && distinct names

end Check

/-- Validate an arbitrary module AST; decoding is not a premise. -/
def validate (m : Module) : Bool :=
  let dts := m.defTypes
  let C := moduleContext m
  let C' := { C with globals := importGlobals dts m.imports }
  Check.typesSeq m.types 0 && Nat.ble C.mems.length 1 &&
  m.imports.all (fun im => Check.importDesc C im.desc) &&
  m.tags.all (fun t => Check.tagType C t.type) &&
  Check.globals C' dts m.globals &&
  m.mems.all (Check.limits (2 ^ 16)) &&
  m.tables.all (fun t => Check.limits (2 ^ 32 - 1) t.type.limits &&
    Check.heapSrc dts.length t.type.elem.heap &&
    Check.constExpr C' t.init [.ref (t.type.elem.close dts)]) &&
  m.funcs.all (Check.func C) &&
  m.elems.all (fun e => Check.heapSrc dts.length e.type.heap &&
    e.init.all (fun ex => Check.constExpr C ex [.ref (e.type.close dts)]) &&
    Check.elemMode C (e.type.close dts) e.mode) &&
  m.datas.all (fun d => Check.dataMode C d.mode) &&
  m.elems.all (fun e => Nat.blt e.init.length (2 ^ 32)) &&
  m.datas.all (fun d => Nat.blt d.init.length (2 ^ 32)) &&
  (match m.start with
    | none => true
    | some x => match C.funcType x with
      | some ⟨[], []⟩ => true
      | _ => false) &&
  m.exports.all (fun ex => Check.exportDesc C ex.desc) &&
  Check.distinct (m.exports.map (·.name))

end FVA.Wasm.Valid
