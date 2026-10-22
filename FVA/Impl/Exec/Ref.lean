import FVA.Spec.Exec.Step
import FVA.Spec.Exec.Instantiate
import FVA.Impl.Numerics.Float

/-!
# Reference stepper (verified implementation)

A deterministic, executable reading of `Step` on spec configurations: `seq` finds the first
non-value of an instruction sequence (descending into labels and frames) and applies the rule
the spec gives there. Where the spec allows a choice, the stepper picks one allowed result:
the verified float operators (`FVA.Impl.Numerics`), growth when it fits, and no host call (a host
call is `stuck`). Signals `br`/`ret` carry a pending branch or return up to the label or frame
that resolves it. Structural recursion keeps it kernel-evaluable. `FVA.Proof.Exec` proves every
`step` it returns is a `Step`.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Num

/-- `Val.instr⁻¹`: the value a canonical constant denotes. -/
def toVal : AInstr → Option Val
  | .plain (.iconst .w32 n) => bif Nat.blt n (2 ^ 32) then some (.i32 (BitVec.ofNat 32 n)) else none
  | .plain (.iconst .w64 n) => bif Nat.blt n (2 ^ 64) then some (.i64 (BitVec.ofNat 64 n)) else none
  | .plain (.fconst .w32 n) => bif Nat.blt n (2 ^ 32) then some (.f32 (BitVec.ofNat 32 n)) else none
  | .plain (.fconst .w64 n) => bif Nat.blt n (2 ^ 64) then some (.f64 (BitVec.ofNat 64 n)) else none
  | .plain (.refNull t) => some (.ref (.null t))
  | .refFuncAddr a => some (.ref (.func a))
  | .refExternAddr a => some (.ref (.extern a))
  | _ => none

/-- The impl's float unary operator. -/
def implUn (F : FloatFormat) : FUnOp → FVal → FVal
  | .abs, z => fabs z
  | .neg, z => fneg z
  | .sqrt, z => Impl.fsqrt F z
  | .ceil, z => Impl.fceil F z
  | .floor, z => Impl.ffloor F z
  | .trunc, z => Impl.ftrunc F z
  | .nearest, z => Impl.fnearest F z

/-- The impl's float binary operator. -/
def implBin (F : FloatFormat) : FBinOp → FVal → FVal → FVal
  | .add, a, b => Impl.fadd F a b
  | .sub, a, b => Impl.fsub F a b
  | .mul, a, b => Impl.fmul F a b
  | .div, a, b => Impl.fdiv F a b
  | .min, a, b => Impl.fmin F a b
  | .max, a, b => Impl.fmax F a b
  | .copysign, a, b => fcopysign a b

/-- The impl's float comparison. -/
def implRel (F : FloatFormat) : FRelOp → FVal → FVal → BitVec 32
  | .eq, a, b => Impl.feq a b
  | .ne, a, b => Impl.fne a b
  | .lt, a, b => Impl.flt F a b
  | .gt, a, b => Impl.fgt F a b
  | .le, a, b => Impl.fle F a b
  | .ge, a, b => Impl.fge F a b

/-- `trunc_sx` by the impl. -/
def implTrunc (F : FloatFormat) (N : Nat) : Sx → FVal → Option Val
  | .u, z => (Impl.ftruncU F N z).bind (intVal N)
  | .s, z => (Impl.ftruncS F N z).bind (intVal N)

/-- `trunc_sat_sx` by the impl. -/
def implTruncSat (F : FloatFormat) (N : Nat) : Sx → FVal → Option Val
  | .u, z => intVal N (Impl.ftruncSatU F N z)
  | .s, z => intVal N (Impl.ftruncSatS F N z)

/-- `convert_sx` by the impl. -/
def implConvert (F : FloatFormat) {M : Nat} : Sx → BitVec M → FVal
  | .u, i => Impl.fconvertU F i
  | .s, i => Impl.fconvertS F i

/-- The numeric result the stepper picks (an element of `numResults`); `none` when the instruction
does not apply to the operands (bottom of the stack first). -/
def numStep : Instr → List Val → Option (Option Val)
  | .iunop .w32 op, [.i32 a] => some (some (.i32 (iunop op a)))
  | .iunop .w64 op, [.i64 a] => some (some (.i64 (iunop op a)))
  | .ibinop .w32 op, [.i32 a, .i32 b] => some ((ibinop op a b).map .i32)
  | .ibinop .w64 op, [.i64 a, .i64 b] => some ((ibinop op a b).map .i64)
  | .itestEqz .w32, [.i32 a] => some (some (.i32 (ieqz a)))
  | .itestEqz .w64, [.i64 a] => some (some (.i32 (ieqz a)))
  | .irelop .w32 op, [.i32 a, .i32 b] => some (some (.i32 (irelop op a b)))
  | .irelop .w64 op, [.i64 a, .i64 b] => some (some (.i32 (irelop op a b)))
  | .funop .w32 op, [.f32 a] => some (r32 (implUn f32fmt op (ofBits f32fmt a)))
  | .funop .w64 op, [.f64 a] => some (r64 (implUn f64fmt op (ofBits f64fmt a)))
  | .fbinop .w32 op, [.f32 a, .f32 b] =>
    some (r32 (implBin f32fmt op (ofBits f32fmt a) (ofBits f32fmt b)))
  | .fbinop .w64 op, [.f64 a, .f64 b] =>
    some (r64 (implBin f64fmt op (ofBits f64fmt a) (ofBits f64fmt b)))
  | .frelop .w32 op, [.f32 a, .f32 b] =>
    some (some (.i32 (implRel f32fmt op (ofBits f32fmt a) (ofBits f32fmt b))))
  | .frelop .w64 op, [.f64 a, .f64 b] =>
    some (some (.i32 (implRel f64fmt op (ofBits f64fmt a) (ofBits f64fmt b))))
  | .cvtop .wrap, [.i64 a] => some (some (.i32 (wrap a)))
  | .cvtop (.extend .u), [.i32 a] => some (some (.i64 (extendU a)))
  | .cvtop (.extend .s), [.i32 a] => some (some (.i64 (extendS a)))
  | .cvtop (.trunc .w32 .w32 sx), [.f32 a] => some (implTrunc f32fmt 32 sx (ofBits f32fmt a))
  | .cvtop (.trunc .w32 .w64 sx), [.f64 a] => some (implTrunc f64fmt 32 sx (ofBits f64fmt a))
  | .cvtop (.trunc .w64 .w32 sx), [.f32 a] => some (implTrunc f32fmt 64 sx (ofBits f32fmt a))
  | .cvtop (.trunc .w64 .w64 sx), [.f64 a] => some (implTrunc f64fmt 64 sx (ofBits f64fmt a))
  | .cvtop (.truncSat .w32 .w32 sx), [.f32 a] =>
    some (implTruncSat f32fmt 32 sx (ofBits f32fmt a))
  | .cvtop (.truncSat .w32 .w64 sx), [.f64 a] =>
    some (implTruncSat f64fmt 32 sx (ofBits f64fmt a))
  | .cvtop (.truncSat .w64 .w32 sx), [.f32 a] =>
    some (implTruncSat f32fmt 64 sx (ofBits f32fmt a))
  | .cvtop (.truncSat .w64 .w64 sx), [.f64 a] =>
    some (implTruncSat f64fmt 64 sx (ofBits f64fmt a))
  | .cvtop (.convert .w32 .w32 sx), [.i32 a] => some (r32 (implConvert f32fmt sx a))
  | .cvtop (.convert .w32 .w64 sx), [.i64 a] => some (r32 (implConvert f32fmt sx a))
  | .cvtop (.convert .w64 .w32 sx), [.i32 a] => some (r64 (implConvert f64fmt sx a))
  | .cvtop (.convert .w64 .w64 sx), [.i64 a] => some (r64 (implConvert f64fmt sx a))
  | .cvtop .demote, [.f64 a] => some (r32 (Impl.fdemote (ofBits f64fmt a)))
  | .cvtop .promote, [.f32 a] => some (r64 (Impl.fpromote (ofBits f32fmt a)))
  | .cvtop (.reinterpret .w32 true), [.f32 a] => some (some (.i32 a))
  | .cvtop (.reinterpret .w64 true), [.f64 a] => some (some (.i64 a))
  | .cvtop (.reinterpret .w32 false), [.i32 a] => some (some (.f32 a))
  | .cvtop (.reinterpret .w64 false), [.i64 a] => some (some (.f64 a))
  | _, _ => none

/-- The memory of the frame's instance. -/
def mem0 (s : Store) (f : Frame) : Option (Nat × MemInst) :=
  match f.inst.mems[0]? with
  | some a => (s.mems[a]?).map (a, ·)
  | none => none

/-- The table `x` of the frame's instance. -/
def tableAt (s : Store) (f : Frame) (x : Nat) : Option (Nat × TableInst) :=
  match f.inst.tables[x]? with
  | some a => (s.tables[a]?).map (a, ·)
  | none => none

/-- `call_indirect x y` on index `i`: the callee address, if the spec's checks pass. -/
def callTarget (s : Store) (f : Frame) (x y : Nat) (i : BitVec 32) : Option Nat :=
  match tableAt s f x, f.inst.types[y]? with
  | some (_, t), some ft => match t.elem[i.toNat]? with
    | some (.func a) => match s.funcs[a]? with
      | some fi => bif decide (fi.type = ft) then some a else none
      | none => none
    | _ => none
  | _, _ => none

/-- One step of a plain instruction other than `br`/`return`, the operand stack `stk` top
first: the store, frame, remaining stack and produced instructions; `none` = no rule. -/
def instrStep (s : Store) (f : Frame) (i : Instr) (stk : List Val) :
    Option (Store × Frame × List Val × List AInstr) :=
  match i, stk with
  -- numeric
  | .iunop .., a :: stk | .itestEqz _, a :: stk | .funop .., a :: stk | .cvtop _, a :: stk =>
    (numStep i [a]).map fun r => (s, f, stk, numOut r)
  | .ibinop .., b :: a :: stk | .irelop .., b :: a :: stk | .fbinop .., b :: a :: stk
  | .frelop .., b :: a :: stk =>
    (numStep i [a, b]).map fun r => (s, f, stk, numOut r)
  -- reference
  | .refIsNull, .ref r :: stk => some (s, f, stk, [vi32 (bif r.isNull then 1 else 0)])
  | .refFunc x, stk => (f.inst.funcs[x]?).map fun a => (s, f, stk, [.refFuncAddr a])
  -- parametric
  | .drop, _ :: stk => some (s, f, stk, [])
  | .select _, .i32 c :: v₂ :: v₁ :: stk =>
    some (s, f, stk, [(bif c == 0 then v₂ else v₁).instr])
  -- variable
  | .localGet x, stk => (f.locals[x]?).map fun v => (s, f, stk, [v.instr])
  | .localSet x, v :: stk =>
    bif Nat.blt x f.locals.length then some (s, { f with locals := f.locals.set x v }, stk, [])
    else none
  | .localTee x, v :: stk => some (s, f, stk, [v.instr, v.instr, .plain (.localSet x)])
  | .globalGet x, stk => match f.inst.globals[x]? with
    | some a => (s.globals[a]?).map fun g => (s, f, stk, [g.value.instr])
    | none => none
  | .globalSet x, v :: stk => match f.inst.globals[x]? with
    | some a => (s.globals[a]?).map fun g =>
      ({ s with globals := s.globals.set a { g with value := v } }, f, stk, [])
    | none => none
  -- table
  | .tableGet x, .i32 i :: stk => (tableAt s f x).map fun (_, t) =>
    match t.elem[i.toNat]? with
    | some r => (s, f, stk, [(Val.ref r).instr])
    | none => (s, f, stk, [.trap])
  | .tableSet x, .ref r :: .i32 i :: stk => (tableAt s f x).map fun (ta, t) =>
    bif Nat.blt i.toNat t.elem.length then
      (s.setTable ta { t with elem := t.elem.set i.toNat r }, f, stk, [])
    else (s, f, stk, [.trap])
  | .tableSize x, stk => (tableAt s f x).map fun (_, t) => (s, f, stk, [vi32 t.elem.length])
  | .tableGrow x, .i32 n :: .ref r :: stk => (tableAt s f x).map fun (ta, t) =>
    match t.grow n.toNat r with
    | some t' => (s.setTable ta t', f, stk, [vi32 t.elem.length])
    | none => (s, f, stk, [(Val.i32 (BitVec.ofInt 32 (-1))).instr])
  | .tableFill x, .i32 n :: .ref r :: .i32 i :: stk => (tableAt s f x).map fun (_, t) =>
    bif Nat.blt t.elem.length (i.toNat + n.toNat) then (s, f, stk, [.trap])
    else bif Nat.beq n.toNat 0 then (s, f, stk, [])
    else (s, f, stk, [(Val.i32 i).instr, (Val.ref r).instr, .plain (.tableSet x),
      vi32 (i.toNat + 1), (Val.ref r).instr, vi32 (n.toNat - 1), .plain (.tableFill x)])
  | .tableCopy x y, .i32 n :: .i32 s' :: .i32 d :: stk =>
    match tableAt s f x, tableAt s f y with
    | some (_, tx), some (_, ty) =>
      bif Nat.blt ty.elem.length (s'.toNat + n.toNat) || Nat.blt tx.elem.length (d.toNat + n.toNat)
      then some (s, f, stk, [.trap])
      else bif Nat.beq n.toNat 0 then some (s, f, stk, [])
      else bif Nat.ble d.toNat s'.toNat then
        some (s, f, stk, [(Val.i32 d).instr, (Val.i32 s').instr, .plain (.tableGet y),
          .plain (.tableSet x), vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1),
          .plain (.tableCopy x y)])
      else some (s, f, stk, [vi32 (d.toNat + n.toNat - 1), vi32 (s'.toNat + n.toNat - 1),
          .plain (.tableGet y), .plain (.tableSet x), (Val.i32 d).instr, (Val.i32 s').instr,
          vi32 (n.toNat - 1), .plain (.tableCopy x y)])
    | _, _ => none
  | .tableInit x y, .i32 n :: .i32 s' :: .i32 d :: stk =>
    match tableAt s f x, f.inst.elems[y]? with
    | some (_, t), some ea => (s.elems[ea]?).map fun e =>
      bif Nat.blt e.elem.length (s'.toNat + n.toNat) || Nat.blt t.elem.length (d.toNat + n.toNat)
      then (s, f, stk, [.trap])
      else bif Nat.beq n.toNat 0 then (s, f, stk, [])
      else match e.elem[s'.toNat]? with
        | some r => (s, f, stk, [(Val.i32 d).instr, (Val.ref r).instr, .plain (.tableSet x),
            vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1), .plain (.tableInit x y)])
        | none => (s, f, stk, [.trap])
    | _, _ => none
  | .elemDrop x, stk => match f.inst.elems[x]? with
    | some a => (s.elems[a]?).map fun e =>
      ({ s with elems := s.elems.set a { e with elem := [] } }, f, stk, [])
    | none => none
  -- memory
  | .load t m, .i32 i :: stk => (mem0 s f).map fun (_, mem) =>
    let ea := i.toNat + m.offset
    bif Nat.blt mem.size (ea + t.bytes) then (s, f, stk, [.trap])
    else (s, f, stk, [(t.val (mem.read ea t.bytes)).instr])
  | .loadPacked w p sx m, .i32 i :: stk => (mem0 s f).map fun (_, mem) =>
    let ea := i.toNat + m.offset
    bif Nat.blt mem.size (ea + p.bits / 8) then (s, f, stk, [.trap])
    else (s, f, stk, [(packedVal w p.bits sx (mem.read ea (p.bits / 8))).instr])
  | .store t m, v :: .i32 i :: stk => match mem0 s f, v.numBits t with
    | some (a, mem), some c =>
      let ea := i.toNat + m.offset
      bif Nat.blt mem.size (ea + t.bytes) then some (s, f, stk, [.trap])
      else some (s.setMem a (mem.write ea t.bytes c), f, stk, [])
    | _, _ => none
  | .storePacked w p m, v :: .i32 i :: stk => match mem0 s f, v.intBits w with
    | some (a, mem), some c =>
      let ea := i.toNat + m.offset
      bif Nat.blt mem.size (ea + p.bits / 8) then some (s, f, stk, [.trap])
      else some (s.setMem a (mem.write ea (p.bits / 8) c), f, stk, [])
    | _, _ => none
  | .memorySize, stk => (mem0 s f).map fun (_, mem) => (s, f, stk, [vi32 mem.pages])
  | .memoryGrow, .i32 n :: stk => (mem0 s f).map fun (a, mem) =>
    match mem.grow n.toNat with
    | some mem' => (s.setMem a mem', f, stk, [vi32 mem.pages])
    | none => (s, f, stk, [(Val.i32 (BitVec.ofInt 32 (-1))).instr])
  | .memoryFill, .i32 n :: v :: .i32 d :: stk => (mem0 s f).map fun (_, mem) =>
    bif Nat.blt mem.size (d.toNat + n.toNat) then (s, f, stk, [.trap])
    else bif Nat.beq n.toNat 0 then (s, f, stk, [])
    else (s, f, stk, [(Val.i32 d).instr, v.instr, .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
      vi32 (d.toNat + 1), v.instr, vi32 (n.toNat - 1), .plain .memoryFill])
  | .memoryCopy, .i32 n :: .i32 s' :: .i32 d :: stk => (mem0 s f).map fun (_, mem) =>
    bif Nat.blt mem.size (s'.toNat + n.toNat) || Nat.blt mem.size (d.toNat + n.toNat) then
      (s, f, stk, [.trap])
    else bif Nat.beq n.toNat 0 then (s, f, stk, [])
    else bif Nat.ble d.toNat s'.toNat then
      (s, f, stk, [(Val.i32 d).instr, (Val.i32 s').instr,
        .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
        vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1), .plain .memoryCopy])
    else (s, f, stk, [vi32 (d.toNat + n.toNat - 1), vi32 (s'.toNat + n.toNat - 1),
        .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
        (Val.i32 d).instr, (Val.i32 s').instr, vi32 (n.toNat - 1), .plain .memoryCopy])
  | .memoryInit x, .i32 n :: .i32 s' :: .i32 d :: stk =>
    match mem0 s f, f.inst.datas[x]? with
    | some (_, mem), some da => (s.datas[da]?).map fun di =>
      bif Nat.blt di.data.length (s'.toNat + n.toNat) || Nat.blt mem.size (d.toNat + n.toNat)
      then (s, f, stk, [.trap])
      else bif Nat.beq n.toNat 0 then (s, f, stk, [])
      else match di.data[s'.toNat]? with
        | some b => (s, f, stk, [(Val.i32 d).instr, vi32 b.toNat,
            .plain (.storePacked .w32 .p8 ⟨0, 0⟩), vi32 (d.toNat + 1), vi32 (s'.toNat + 1),
            vi32 (n.toNat - 1), .plain (.memoryInit x)])
        | none => (s, f, stk, [.trap])
    | _, _ => none
  | .dataDrop x, stk => match f.inst.datas[x]? with
    | some a => (s.datas[a]?).map fun _ =>
      ({ s with datas := s.datas.set a { data := [] } }, f, stk, [])
    | none => none
  -- control
  | .nop, stk => some (s, f, stk, [])
  | .unreachable, stk => some (s, f, stk, [.trap])
  | .block bt body, stk => (bt.expand f).bind fun ft =>
    let m := ft.params.length
    bif Nat.blt stk.length m then none
    else some (s, f, stk.drop m,
      [.label ft.results.length [] (vals (stk.take m).reverse ++ body.map .plain)])
  | .loop bt body, stk => (bt.expand f).bind fun ft =>
    let m := ft.params.length
    bif Nat.blt stk.length m then none
    else some (s, f, stk.drop m,
      [.label m [.loop bt body] (vals (stk.take m).reverse ++ body.map .plain)])
  | .if_ bt thn els, .i32 c :: stk =>
    some (s, f, stk, [.plain (.block bt (bif c == 0 then els else thn))])
  | .brIf l, .i32 c :: stk => some (s, f, stk, bif c == 0 then [] else [.plain (.br l)])
  | .brTable ls l, .i32 i :: stk => some (s, f, stk, [.plain (.br (ls[i.toNat]?.getD l))])
  | .call x, stk => (f.inst.funcs[x]?).map fun a => (s, f, stk, [.invoke a])
  | .callIndirect x y, .i32 i :: stk => some (s, f, stk, match callTarget s f x y i with
    | some a => [.invoke a]
    | none => [.trap])
  | _, _ => none

/-- What one attempted step yields. -/
inductive Out where
  /-- A step to this store, frame and sequence. -/
  | step (s : Store) (f : Frame) (es : List AInstr)
  /-- `br k` is next after the values `vs` (top first): resolved by the `k`-th enclosing label. -/
  | br (k : Nat) (vs : List Val)
  /-- `return` is next after the values `vs` (top first): resolved by the enclosing frame. -/
  | ret (vs : List Val)
  /-- Only values remain, or only `trap`. -/
  | final
  /-- No rule applies (invalid code, a host call). -/
  | stuck

/-- `[trap]`. -/
def isTrapOnly : List AInstr → Bool
  | [.trap] => true
  | _ => false

mutual
/-- Step the first non-value of `es`; `vs` = the values before it (top first). -/
def seq (s : Store) (f : Frame) (vs : List Val) : List AInstr → Out
  | [] => .final
  | e :: rest => match toVal e with
    | some v => seq s f (v :: vs) rest
    | none => atInstr s f vs e rest

/-- Step at the non-value `e`, with values `vs` (top first) before it and `rest` after. -/
def atInstr (s : Store) (f : Frame) (vs : List Val) (e : AInstr) (rest : List AInstr) : Out :=
  match e with
  | .trap => bif vs.isEmpty && rest.isEmpty then .final else .step s f [.trap]
  | .label n cont body =>
    match seq s f [] body with
    | .final =>
      .step s f (vals vs.reverse ++ (bif isTrapOnly body then [.trap] else body) ++ rest)
    | .step s' f' body' => .step s' f' (vals vs.reverse ++ [.label n cont body'] ++ rest)
    | .br 0 bvs => bif Nat.blt bvs.length n then .stuck
      else .step s f (vals vs.reverse ++ vals (bvs.take n).reverse ++ cont.map .plain ++ rest)
    | .br (k + 1) bvs => .br k bvs
    | .ret bvs => .ret bvs
    | .stuck => .stuck
  | .frame n fi body =>
    match seq s fi [] body with
    | .final => bif isTrapOnly body then .step s f (vals vs.reverse ++ [.trap] ++ rest)
      else bif Nat.beq body.length n then .step s f (vals vs.reverse ++ body ++ rest)
      else .stuck
    | .step s' fi' body' => .step s' f (vals vs.reverse ++ [.frame n fi' body'] ++ rest)
    | .ret bvs => bif Nat.blt bvs.length n then .stuck
      else .step s f (vals vs.reverse ++ vals (bvs.take n).reverse ++ rest)
    | .br _ _ => .stuck
    | .stuck => .stuck
  | .invoke a =>
    match s.funcs[a]? with
    | some (.wasm ft inst code) =>
      let m := ft.params.length
      bif Nat.blt vs.length m then .stuck
      else .step s f (vals (vs.drop m).reverse ++
        [.frame ft.results.length ⟨(vs.take m).reverse ++ code.localDefaults, inst⟩
          [.label ft.results.length [] (code.body.map .plain)]] ++ rest)
    | _ => .stuck
  | .plain (.br k) => .br k vs
  | .plain .return_ => .ret vs
  | .plain i => match instrStep s f i vs with
    | some (s', f', stk, out) => .step s' f' (vals stk.reverse ++ out ++ rest)
    | none => .stuck
  | _ => .stuck
end

/-- One step of a configuration (`none` when it is final or stuck). -/
def step (c : Config) : Option Config :=
  match seq c.store c.frame [] c.instrs with
  | .step s f es => some ⟨s, f, es⟩
  | _ => none

/-- Run up to `fuel` steps; `some c'` when a final configuration `c'` is reached. -/
def run : Nat → Config → Option Config
  | 0, _ => none
  | n + 1, c => match seq c.store c.frame [] c.instrs with
    | .step s f es => run n ⟨s, f, es⟩
    | .final => some c
    | _ => none

end FVA.Wasm.Exec.Ref

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm

/-- The reference a value is, if any. -/
def asRef : Val → Option Ref
  | .ref r => some r
  | _ => none

/-- Evaluate a constant expression (a global or element initializer) in store `s` with instance
`inst`, within `fuel` steps. -/
def evalConst (fuel : Nat) (s : Store) (inst : ModuleInst) (e : Expr) : Option Val :=
  match run fuel ⟨s, ⟨[], inst⟩, e.map .plain⟩ with
  | some c => match c.instrs with
    | [v] => toVal v
    | _ => none
  | none => none

/-- Instantiate `m` in `s` with `imports` (§4.5.4) by running the initializers and the
initialization code within `fuel` steps each: allocate with placeholder initial values, evaluate
the initializers in that store, then allocate with their values (a valid module's initializers
read only imported globals and function addresses, which both allocations share). `none` on a
failing initializer, a trap or exhausted fuel; import matching is checked separately. -/
def instantiate (fuel : Nat) (s : Store) (m : Module) (imports : List ExternVal) :
    Option (Store × ModuleInst) := do
  let (s₀, inst₀) := allocModule s m imports (m.globals.map fun g => g.type.val.default)
    (m.elems.map fun _ => [])
  let gvals ← m.globals.mapM fun g => evalConst fuel s₀ inst₀ g.init
  let erefs ← m.elems.mapM fun e => e.init.mapM fun ex => evalConst fuel s₀ inst₀ ex >>= asRef
  let (s₁, inst) := allocModule s m imports gvals erefs
  let c ← run fuel ⟨s₁, ⟨[], inst⟩, (initCode m).map .plain⟩
  match c.instrs with
  | [] => some (c.store, inst)
  | _ => none

end FVA.Wasm.Exec.Ref
