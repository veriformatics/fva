import FVA.Spec.Valid.Module

/-!
# WebAssembly validator

The appendix operand/control-stack algorithm over the nested AST. Each recursive body owns
its operand stack; the enclosing context supplies its labels. An unreachable empty stack pops
bottom, but explicit operands still undergo every type check. Local declarations stay as runs.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

namespace Check

/-- Top-first operands above the current control frame's base. -/
structure Stack where
  /-- Explicit operands, top first; surrounding frames own separate stacks. -/
  types : List OpType := []
  /-- Empty-base pops may synthesize bottom after an unconditional transfer. -/
  unreachable : Bool := false
  deriving DecidableEq

/-- Boolean operand matching; a bottom operand matches every expected type. -/
def matchType : OpType → OpType → Bool
  | .bot, _ => true
  | .val t, .val u => decide (t = u)
  | .val _, .bot => false

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
def lookupLocal : List (Nat × ValType) → Nat → Option ValType
  | [], _ => none
  | (n, t) :: rest, x => bif Nat.blt x n then some t else lookupLocal rest (Nat.sub x n)

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
  | .refNull rt => some ⟨[], [.val (.ref rt)]⟩
  | .refFunc x => match C.funcs[x]? with
    | none => none
    | some _ => bif C.refs.any (Nat.beq x) then some ⟨[], [.val (.ref .funcref)]⟩ else none
  | .select ts => match ts with
    | some [t] => some ⟨[.val t, .val t, i32], [.val t]⟩
    | _ => none
  | .localGet x => (lookupLocal C.locals x).map fun t => ⟨[], [.val t]⟩
  | .localSet x => (lookupLocal C.locals x).map fun t => ⟨[.val t], []⟩
  | .localTee x => (lookupLocal C.locals x).map fun t => ⟨[.val t], [.val t]⟩
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
    | some tx, some ty => bif decide (tx.elem = ty.elem) then
        some ⟨[i32, i32, i32], []⟩ else none
    | _, _ => none
  | .tableInit x y => match C.tables[x]?, C.elems[y]? with
    | some tt, some rt => bif decide (tt.elem = rt) then some ⟨[i32, i32, i32], []⟩ else none
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
  | .call x => (C.funcs[x]?).map fun ft => ⟨ops ft.params, ops ft.results⟩
  | .callIndirect x y => match C.tables[x]?, C.types[y]? with
    | some ⟨_, .funcref⟩, some ft => some ⟨ops ft.params ++ [i32], ops ft.results⟩
    | _, _ => none
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

mutual

/-- One instruction; nested bodies start their own operand stack and control frame. -/
def instr (C : Context) (i : Instr) (s : Stack) : Option Stack :=
  match i with
  | .unreachable => some ⟨[], true⟩
  | .drop => (pop s).map fun (_, rest) => rest
  | .refIsNull => match pop s with
    | some (.bot, rest) | some (.val (.ref _), rest) => some (push [i32] rest)
    | _ => none
  | .select none => match pops [i32] s with
    | none => none
    | some (_, rest) => match pop rest with
      | none => none
      | some (t, rest') => match pop rest' with
        | none => none
        | some (u, rest'') => (selectType t u).map fun v => push [v] rest''
  | .block bt body => match C.blockType bt with
    | none => none
    | some ft => match seq (C.withLabel ft.results) body ⟨(ops ft.params).reverse, false⟩ with
      | none => none
      | some out => bif finish ft.results out then apply ⟨ops ft.params, ops ft.results⟩ s
        else none
  | .loop bt body => match C.blockType bt with
    | none => none
    | some ft => match seq (C.withLabel ft.params) body ⟨(ops ft.params).reverse, false⟩ with
      | none => none
      | some out => bif finish ft.results out then apply ⟨ops ft.params, ops ft.results⟩ s
        else none
  | .if_ bt thn els => match C.blockType bt with
    | none => none
    | some ft =>
      match seq (C.withLabel ft.results) thn ⟨(ops ft.params).reverse, false⟩,
          seq (C.withLabel ft.results) els ⟨(ops ft.params).reverse, false⟩ with
      | some out₁, some out₂ => bif finish ft.results out₁ && finish ft.results out₂ then
          apply ⟨ops ft.params ++ [i32], ops ft.results⟩ s else none
      | _, _ => none
  | .br l => match C.labels[l]? with | none => none | some ts => branch ts s
  | .return_ => match C.return_ with | none => none | some ts => branch ts s
  | .brTable ls l => match C.labels[l]?, pops [i32] s with
    | some ts, some (_, rest) => match pops (ops ts).reverse rest with
      | some (as, _) => bif targets C as ls then some ⟨[], true⟩ else none
      | none => none
    | _, _ => none
  | _ => match fixed C i with | none => none | some st => apply st s

/-- Sequential structural recursion, without flattening nested bodies. -/
def seq (C : Context) : List Instr → Stack → Option Stack
  | [], s => some s
  | i :: is, s => match instr C i s with | none => none | some s' => seq C is s'

end

/-- A complete expression starts without operands. -/
def expr (C : Context) (e : Expr) (ts : List ValType) : Bool :=
  match seq C e {} with | none => false | some s => finish ts s

/-- Constant expressions use only the restricted initializer context. -/
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

/-- Import description checks, before index spaces are used. -/
def importDesc (C : Context) : ImportDesc → Bool
  | .func x => Nat.blt x C.types.length
  | .table tt => limits (2 ^ 32 - 1) tt.limits
  | .mem lim => limits (2 ^ 16) lim
  | .global _ => true

/-- Function body validation; counting locals never expands their runs. -/
def func (C : Context) (f : Func) : Bool :=
  match C.types[f.type]? with
  | none => false
  | some ft =>
    Nat.blt (f.locals.foldl (fun n r => n + r.1) ft.params.length) (2 ^ 32) &&
    expr { C with
      locals := ft.params.map (1, ·) ++ f.locals
      labels := [ft.results]
      return_ := some ft.results } f.body ft.results

/-- An element segment's mode. -/
def elemMode (C : Context) (t : RefType) : ElemMode → Bool
  | .passive | .declarative => true
  | .active x off => match C.tables[x]? with
    | none => false
    | some tt => decide (tt.elem = t) && constExpr C off [.num .i32]

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

/-- Distinct names, without a hash-table trusted implementation. -/
def distinct : List String → Bool
  | [] => true
  | name :: names => !names.contains name && distinct names

end Check

/-- Validate an arbitrary module AST; decoding is not a premise. -/
def validate (m : Module) : Bool :=
  let C := moduleContext m
  let C' := { C with globals := importGlobals m.imports }
  Nat.ble C.mems.length 1 &&
  m.funcs.all (fun f => Nat.blt f.type m.types.length) &&
  m.imports.all (fun im => Check.importDesc C im.desc) &&
  m.funcs.all (Check.func C) &&
  m.tables.all (fun tt => Check.limits (2 ^ 32 - 1) tt.limits) &&
  m.mems.all (Check.limits (2 ^ 16)) &&
  m.globals.all (fun g => Check.constExpr C' g.init [g.type.val]) &&
  m.elems.all (fun e => e.init.all (fun ex => Check.constExpr C' ex [.ref e.type]) &&
    Check.elemMode C' e.type e.mode) &&
  m.datas.all (fun d => Check.dataMode C' d.mode) &&
  m.elems.all (fun e => Nat.blt e.init.length (2 ^ 32)) &&
  m.datas.all (fun d => Nat.blt d.init.length (2 ^ 32)) &&
  (match m.start with
    | none => true
    | some x => match C.funcs[x]? with
      | some ⟨[], []⟩ => true
      | _ => false) &&
  m.exports.all (fun ex => Check.exportDesc C ex.desc) &&
  Check.distinct (m.exports.map (·.name))

end FVA.Wasm.Valid
