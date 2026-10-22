import FVA
import FVA.Spec.Numerics.Int
import FVA.Tool.Pack
import FVA.Tool.Lift
import Lean.Data.Json

/-!
# Numeric test runner (U3 evidence E1)

Runs the official numeric test scripts (`wasm-tools json-from-wast` output) against the reviewed
numeric operations, without an interpreter: each invoked export must be straight-line code over
its parameters (`local.get`, constants, numeric instructions). Other assertions are counted as
skipped; the pinned counts in `scripts/test-numerics` make a shrinking run fail.
-/

namespace FVA.Test.Numeric

open FVA.Wasm FVA.Wasm.Num Lean

/-- Runtime values of the numeric types. -/
inductive Value where
  | i32 (v : BitVec 32)
  | i64 (v : BitVec 64)
  | f32 (bits : BitVec 32)
  | f64 (bits : BitVec 64)
  deriving BEq, Repr

/-- Outcome of evaluating one instruction: values pushed, a trap, or not covered yet. -/
inductive Out where
  | push (vs : List Value)
  | trap (msg : String)
  | unsupported (what : String)

/-- Lift a partial integer op. -/
def partial32 (r : Option (BitVec 32)) : Out := match r with
  | some v => .push [.i32 v] | none => .trap "trap"
/-- Lift a partial integer op. -/
def partial64 (r : Option (BitVec 64)) : Out := match r with
  | some v => .push [.i64 v] | none => .trap "trap"

/-- Integer binary ops by width. -/
def ibin32 : IBinOp → BitVec 32 → BitVec 32 → Out
  | .add, a, b => .push [.i32 (iadd a b)] | .sub, a, b => .push [.i32 (isub a b)]
  | .mul, a, b => .push [.i32 (imul a b)]
  | .div .u, a, b => partial32 (idiv_u a b) | .div .s, a, b => partial32 (idiv_s a b)
  | .rem .u, a, b => partial32 (irem_u a b) | .rem .s, a, b => partial32 (irem_s a b)
  | .and, a, b => .push [.i32 (iand a b)] | .or, a, b => .push [.i32 (ior a b)]
  | .xor, a, b => .push [.i32 (ixor a b)] | .shl, a, b => .push [.i32 (ishl a b)]
  | .shr .u, a, b => .push [.i32 (ishr_u a b)] | .shr .s, a, b => .push [.i32 (ishr_s a b)]
  | .rotl, a, b => .push [.i32 (irotl a b)] | .rotr, a, b => .push [.i32 (irotr a b)]

/-- Integer binary ops by width. -/
def ibin64 : IBinOp → BitVec 64 → BitVec 64 → Out
  | .add, a, b => .push [.i64 (iadd a b)] | .sub, a, b => .push [.i64 (isub a b)]
  | .mul, a, b => .push [.i64 (imul a b)]
  | .div .u, a, b => partial64 (idiv_u a b) | .div .s, a, b => partial64 (idiv_s a b)
  | .rem .u, a, b => partial64 (irem_u a b) | .rem .s, a, b => partial64 (irem_s a b)
  | .and, a, b => .push [.i64 (iand a b)] | .or, a, b => .push [.i64 (ior a b)]
  | .xor, a, b => .push [.i64 (ixor a b)] | .shl, a, b => .push [.i64 (ishl a b)]
  | .shr .u, a, b => .push [.i64 (ishr_u a b)] | .shr .s, a, b => .push [.i64 (ishr_s a b)]
  | .rotl, a, b => .push [.i64 (irotl a b)] | .rotr, a, b => .push [.i64 (irotr a b)]

/-- Integer comparisons. -/
def irel {N : Nat} : IRelOp → BitVec N → BitVec N → BitVec 32
  | .eq, a, b => ieq a b | .ne, a, b => ine a b
  | .lt .u, a, b => ilt_u a b | .lt .s, a, b => ilt_s a b
  | .gt .u, a, b => igt_u a b | .gt .s, a, b => igt_s a b
  | .le .u, a, b => ile_u a b | .le .s, a, b => ile_s a b
  | .ge .u, a, b => ige_u a b | .ge .s, a, b => ige_s a b

/-- Integer unary ops. -/
def iun {N : Nat} : IUnOp → BitVec N → BitVec N
  | .clz, a => iclz a | .ctz, a => ictz a | .popcnt, a => ipopcnt a
  | .extend8s, a => iextend_s 8 a | .extend16s, a => iextend_s 16 a
  | .extend32s, a => iextend_s 32 a

/-- One numeric instruction on the operand stack (top first). -/
def step (i : Instr) (stk : List Value) : Out × List Value :=
  match i, stk with
  | .iconst .w32 n, s => (.push [.i32 (BitVec.ofNat 32 n)], s)
  | .iconst .w64 n, s => (.push [.i64 (BitVec.ofNat 64 n)], s)
  | .fconst .w32 n, s => (.push [.f32 (BitVec.ofNat 32 n)], s)
  | .fconst .w64 n, s => (.push [.f64 (BitVec.ofNat 64 n)], s)
  | .ibinop .w32 op, .i32 b :: .i32 a :: s => (ibin32 op a b, s)
  | .ibinop .w64 op, .i64 b :: .i64 a :: s => (ibin64 op a b, s)
  | .irelop .w32 op, .i32 b :: .i32 a :: s => (.push [.i32 (irel op a b)], s)
  | .irelop .w64 op, .i64 b :: .i64 a :: s => (.push [.i32 (irel op a b)], s)
  | .itestEqz .w32, .i32 a :: s => (.push [.i32 (ieqz a)], s)
  | .itestEqz .w64, .i64 a :: s => (.push [.i32 (ieqz a)], s)
  | .iunop .w32 op, .i32 a :: s => (.push [.i32 (iun op a)], s)
  | .iunop .w64 op, .i64 a :: s => (.push [.i64 (iun op a)], s)
  | .cvtop .wrap, .i64 a :: s => (.push [.i32 (wrap a)], s)
  | .cvtop (.extend .u), .i32 a :: s => (.push [.i64 (extend_u a)], s)
  | .cvtop (.extend .s), .i32 a :: s => (.push [.i64 (extend_s a)], s)
  | .cvtop (.reinterpret .w32 true), .f32 a :: s => (.push [.i32 a], s)
  | .cvtop (.reinterpret .w64 true), .f64 a :: s => (.push [.i64 a], s)
  | .cvtop (.reinterpret .w32 false), .i32 a :: s => (.push [.f32 a], s)
  | .cvtop (.reinterpret .w64 false), .i64 a :: s => (.push [.f64 a], s)
  | i, s => (.unsupported (FVA.Tool.Lift.instr i), s)

/-- Evaluate straight-line code over the parameters. -/
def run (params : List Value) : List Instr → List Value → Out
  | [], stk => .push stk.reverse
  | .localGet x :: is, stk => match params[x]? with
    | some v => run params is (v :: stk)
    | none => .unsupported "local.get beyond parameters"
  | i :: is, stk =>
    match step i stk with
    | (.push vs, s) => run params is (vs.reverse ++ s)
    | (.trap m, _) => .trap m
    | (.unsupported w, _) => .unsupported w

/-- A JSON argument or expected value; `none` for NaN patterns and other types. -/
def parseValue (j : Json) : Except String (Option Value) := do
  let ty ← j.getObjValAs? String "type"
  let v ← j.getObjValAs? String "value"
  -- `json-from-wast` writes integers as written in the script, so negatives appear signed
  match v.toInt? with
  | none => return none
  | some n => match ty with
    | "i32" => return some (.i32 (BitVec.ofInt 32 n))
    | "i64" => return some (.i64 (BitVec.ofInt 64 n))
    | "f32" => return some (.f32 (BitVec.ofInt 32 n))
    | "f64" => return some (.f64 (BitVec.ofInt 64 n))
    | _ => return none

/-- Tally of one script. -/
structure Tally where
  /-- Assertions evaluated and matching. -/
  pass : Nat := 0
  /-- Assertions evaluated and not matching. -/
  fail : Nat := 0
  /-- Assertions outside the runner's reach (not straight-line, NaN patterns, …). -/
  skip : Nat := 0
  /-- Failure descriptions. -/
  failures : Array String := #[]

/-- Run one `json-from-wast` script; module files are resolved relative to `dir`. -/
def runScript (dir : System.FilePath) (json : Json) : IO Tally := do
  let cmds ← IO.ofExcept (json.getObjValAs? (Array Json) "commands")
  let mut mod : Option FVA.Wasm.Module := none
  let mut t : Tally := {}
  for c in cmds do
    let ty ← IO.ofExcept (c.getObjValAs? String "type")
    if ty == "module" then
      let file ← IO.ofExcept (c.getObjValAs? String "filename")
      let bs ← IO.FS.readBinFile (dir / file)
      mod := match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
        | .ok m => some m | .error _ => none
    else if ty == "assert_return" || ty == "assert_trap" then
      let line := (c.getObjValAs? Nat "line").toOption.getD 0
      let some m := mod | t := { t with skip := t.skip + 1 }; continue
      let act ← IO.ofExcept (c.getObjVal? "action")
      let field ← IO.ofExcept (act.getObjValAs? String "field")
      let args ← IO.ofExcept (act.getObjValAs? (Array Json) "args")
      let argVals ← IO.ofExcept (args.toList.mapM parseValue)
      let some params := argVals.mapM id | t := { t with skip := t.skip + 1 }; continue
      let some fidx := m.exports.findSome? fun e =>
          match e.desc with | .func x => if e.name == field then some x else none | _ => none
        | t := { t with skip := t.skip + 1 }; continue
      let nimp := (m.imports.filter fun im =>
        match im.desc with | .func _ => true | _ => false).length
      let some f := m.funcs[fidx - nimp]? | t := { t with skip := t.skip + 1 }; continue
      match run params f.body [], ty with
      | .unsupported _, _ => t := { t with skip := t.skip + 1 }
      | .trap _, "assert_trap" => t := { t with pass := t.pass + 1 }
      | .push vs, "assert_return" =>
        let exps ← IO.ofExcept (c.getObjValAs? (Array Json) "expected")
        let expVals ← IO.ofExcept (exps.toList.mapM parseValue)
        match expVals.mapM id with
        | none => t := { t with skip := t.skip + 1 }
        | some es =>
          if vs == es then t := { t with pass := t.pass + 1 }
          else
            let msg := s!"line {line}: {field} {repr params} = {repr vs}, expected {repr es}"
            t := { t with fail := t.fail + 1, failures := t.failures.push msg }
      | _, _ =>
        let msg := s!"line {line}: {field}: trap/return mismatch"
        t := { t with fail := t.fail + 1, failures := t.failures.push msg }
  return t

end FVA.Test.Numeric
