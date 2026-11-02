import Lean
import FVA.Spec.CAbi

/-!
# `fva explain` helpers (tooling, outside the trusted base)

Run inside the project (`lake env lean` on a generated file that imports the spec module):
`shapes` reads each claim's docstring, elaborated statement and shape
`∀ (x : BitVec n)…, Returns m "f" args res`; `declared` lists the review modules' names;
`run` computes `res` on concrete inputs.

Values come from `whnf` (definitional: compiled code, which an `implemented_by` override can
change, never runs) and each is confirmed by the kernel (`res = value` by `rfl`, D16), both within
a heartbeat budget per case (D17). Results go to a file, one JSON line per case, flushed: `#eval`
buffers stdout until the command ends.
-/

namespace FVA.Explain

open Lean Meta FVA.Wasm FVA.Wasm.Exec

/-- The count of a statement's leading `BitVec` binders: a `Returns … →` premise is a binder too,
so `forallTelescope` alone would take it as a variable. -/
def leadingBitVecs : Lean.Expr → Nat
  | .forallE _ t b _ => if t.isAppOfArity ``BitVec 1 then leadingBitVecs b + 1 else 0
  | _ => 0

/-- A claim's example shape, or `null` (D18 adds the last two):
* `returns`: `∀ (x : BitVec n)…, Returns m "f" [.t x…] res` — rows: inputs → `res` by Lean,
  checked against the binary;
* `implies`: `∀ (x : BitVec n)… (r : BitVec k)…, Returns m "f" [.t x…] [.t r…] → φ` with `φ`
  decidable — rows: inputs → the binary's results as `r…` → `φ` decided;
* `decide`: `∀ (x : BitVec n)…, φ` with `φ` decidable — rows: inputs → `φ` decided.
`{"kind", "fn"?, "params": [{"name", "bits"}] (the inputs), "outputs": [{"name", "bits"}]}`; the
inputs are the leading binders, in the order the call passes them. -/
def shape (c : Name) : MetaM Json := do
  let some (.defnInfo d) := (← getEnv).find? c | return .null
  forallBoundedTelescope d.value (some (leadingBitVecs d.value)) fun xs body => do
    let mut bs := #[]
    for x in xs do
      let t ← whnfR (← inferType x)
      unless t.isAppOfArity ``BitVec 1 do return .null
      let some n ← evalNat (t.getArg! 0) | return .null
      bs := bs.push <| Json.mkObj [("name", toJson (← x.fvarId!.getUserName).eraseMacroScopes),
        ("bits", toJson n)]
    -- `[.t x₀, .t x₁, …]` over exactly the binders `ys`, in order
    let callOn (l : Lean.Expr) (ys : Array Lean.Expr) : MetaM Bool := do
      let some es ← Meta.getListLit? l | return false
      return es.size == ys.size && (es.zip ys).all fun (e, y) => e.isApp && e.appArg! == y
    let ret (r : Lean.Expr) : Option String :=
      if !r.isAppOfArity ``Returns 4 then none else match r.getArg! 1 with
        | .lit (.strVal fn) => some fn
        | _ => none
    if let some fn := ret body then
      unless ← callOn (body.getArg! 2) xs do return .null
      return Json.mkObj [("kind", "returns"), ("fn", toJson fn), ("params", Json.arr bs),
        ("outputs", Json.arr #[])]
    if let .forallE _ dom φ _ := body then
      if let some fn := ret dom then
        if φ.hasLooseBVars then return .null
        let some outs ← Meta.getListLit? (dom.getArg! 3) | return .null
        let k := xs.size - outs.size
        unless ← callOn (dom.getArg! 2) (xs.extract 0 k) <&&> callOn (dom.getArg! 3) (xs.extract k)
          do return .null
        unless (← synthInstance? (mkApp (mkConst ``Decidable) φ)).isSome do return .null
        return Json.mkObj [("kind", "implies"), ("fn", toJson fn),
          ("params", Json.arr (bs.extract 0 k)), ("outputs", Json.arr (bs.extract k))]
    unless (← synthInstance? (mkApp (mkConst ``Decidable) body)).isSome do return .null
    return Json.mkObj [("kind", "decide"), ("params", Json.arr bs), ("outputs", Json.arr #[])]

/-- Append `{"claim", "doc", "statement", "shape"}` per claim to `out`; `statement` = the
elaborated claim, after every macro and notation the spec imports has run. -/
def shapes (cs : List Name) (out : System.FilePath) : MetaM Unit := do
  let h ← IO.FS.Handle.mk out .append
  for c in cs do
    let some (.defnInfo d) := (← getEnv).find? c | continue
    let doc ← findDocString? (← getEnv) c
    let st ← withOptions (pp.mvars.set · false) <| ppExpr d.value
    h.putStrLn (Json.compress <| Json.mkObj [("claim", toJson c), ("doc", toJson doc),
      ("statement", toJson (toString st)), ("shape", ← shape c)])
  h.flush

/-- Append `{"declared"}` per constant the modules `ms` (the review modules) declare: the names
`fva explain` hides from the model (D5). -/
def declared (ms : List Name) (out : System.FilePath) : MetaM Unit := do
  let env ← getEnv
  let h ← IO.FS.Handle.mk out .append
  for m in ms do
    let some i := env.header.moduleNames.idxOf? m | continue
    for c in env.header.moduleData[i]!.constNames do
      unless c.isInternal do h.putStrLn (Json.compress <| Json.mkObj [("declared", toJson c)])
  h.flush

/-- The literal a closed `Nat` term reduces to by `whnf`, else `none`. -/
partial def natOf (e : Lean.Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  if let some n := e.rawNatLit? <|> e.nat? then return some n
  if e.isAppOfArity ``Nat.succ 1 then return (← natOf e.appArg!).map (· + 1)
  return none

/-- A `List Val` term's values as `(type, bits)` by `whnf` (definitional: the kernel's reading,
which an `implemented_by` override cannot change), else `none`. -/
partial def values (e : Lean.Expr) : MetaM (Option (List (String × Nat))) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return some []
  unless e.isAppOfArity ``List.cons 3 do return none
  let v ← whnf (e.getArg! 1)
  let some (ty, bits) := (match v.getAppFn.constName? with
      | some ``Val.i32 => some ("i32", 32) | some ``Val.i64 => some ("i64", 64)
      | some ``Val.f32 => some ("f32", 32) | some ``Val.f64 => some ("f64", 64)
      | _ => none : Option (String × Nat)) | return none
  let some n ← natOf (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit bits) v.appArg!) | return none
  return (← values (e.getArg! 2)).map ((ty, n) :: ·)

/-- The `List Val` literal of `vs`. -/
def valsExpr (vs : List (String × Nat)) : Lean.Expr :=
  let valT := mkConst ``Val
  vs.foldr (init := mkApp (mkConst ``List.nil [0]) valT) fun (t, n) acc =>
    let (ctor, bits) := match t with
      | "i64" => (``Val.i64, 64) | "f32" => (``Val.f32, 32) | "f64" => (``Val.f64, 64)
      | _ => (``Val.i32, 32)
    mkApp3 (mkConst ``List.cons [0]) valT
      (mkApp (mkConst ctor) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit bits) (mkNatLit n))) acc

/-- Heartbeats (thousands) one example case may spend, in its reduction and again in its kernel
check (D17): deterministic, so a case is too costly on every machine or on none; at 10000,
`sum_to(3000)` fits and `sum_to(4294967295)` stops within about 1.3 s. -/
def caseHeartbeats : Nat := 10000

/-- The kernel's verdict on `res = v` by `rfl` within `caseHeartbeats`: `some true` accepted,
`some false` refused, `none` = out of budget or of its own resources. -/
def kernelAccepts (res v : Lean.Expr) : MetaM (Option Bool) := do
  let decl := Declaration.thmDecl
    { name := `_fva_explain_case, levelParams := [], type := ← mkEq res v, value := ← mkEqRefl v }
  let opts := maxHeartbeats.set (← getOptions) caseHeartbeats
  return match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts decl with
    | .ok _ => some true
    | .error .interrupted | .error .deterministicTimeout | .error .deepRecursion
    | .error .excessiveMemory => none
    | .error _ => some false

/-- One case's values + status: `confirmed` (the kernel accepts `result = values`), `refused`
(it does not: the values are shown as such), `cost` (past `caseHeartbeats` in the reduction or
the kernel), `stuck` (no literal values). The budget is enforced inside Lean (D17), never by
killing the process. -/
def evalCase (res : Lean.Expr) : MetaM (List (String × Nat) × String) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      ({ · with maxHeartbeats := caseHeartbeats * 1000, maxRecDepth := 100000 }) do
      let some vals ← values res | return ([], "stuck")
      return (vals, match ← kernelAccepts res (valsExpr vals) with
        | some true => "confirmed" | some false => "refused" | none => "cost"))
    fun _ => return ([], "cost")

/-- Append `{"claim", "case", "res", "status"}` per case of `cases` (arguments as naturals) to
`out`: `res` = the claim's `Returns` result reduced by `whnf`, `status` as `evalCase`. -/
def run (c : Name) (cases : List (List Nat)) (out : System.FilePath) : MetaM Unit := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c}: not a definition"
  let h ← IO.FS.Handle.mk out .append
  for (args, i) in cases.zipIdx do
    let vs ← forallTelescope d.value fun xs _ => do
      let mut vs := #[]
      for (x, a) in xs.zip args.toArray do
        let t ← whnfR (← inferType x)
        vs := vs.push (mkApp2 (mkConst ``BitVec.ofNat) (t.getArg! 0) (mkNatLit a))
      return vs
    let (vals, status) ← evalCase ((← instantiateForall d.value vs).getArg! 3)
    h.putStrLn (Json.compress <| Json.mkObj [("claim", toJson c), ("case", toJson i),
      ("res", Json.arr (vals.toArray.map fun (t, n) =>
        Json.mkObj [("type", toJson t), ("value", toJson n)])), ("status", toJson status)])
    h.flush

/-- `decide φ` reduced by `whnf` and confirmed by the kernel within `caseHeartbeats` (D18):
`(some b, "confirmed")`, `(some b, "refused")`, `(none, "cost")`, `(none, "stuck")`. -/
def evalDecide (φ : Lean.Expr) : MetaM (Option Bool × String) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      ({ · with maxHeartbeats := caseHeartbeats * 1000, maxRecDepth := 100000 }) do
      let some inst ← synthInstance? (mkApp (mkConst ``Decidable) φ) | return (none, "stuck")
      let e := mkApp2 (mkConst ``Decidable.decide) φ inst
      let v ← whnf e
      let some b := (if v.isConstOf ``Bool.true then some true
        else if v.isConstOf ``Bool.false then some false else none) | return (none, "stuck")
      return (some b, match ← kernelAccepts e (toExpr b) with
        | some true => "confirmed" | some false => "refused" | none => "cost"))
    fun _ => return (none, "cost")

/-- Append `{"claim", "case", "holds", "status"}` per case of `cases` (every binder's value, in
order) to `out`: the condition (`φ` of an `implies` claim, the whole body of a `decide` claim)
decided by `evalDecide` (D18). -/
def decideCases (c : Name) (cases : List (List Nat)) (out : System.FilePath) : MetaM Unit := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c}: not a definition"
  let h ← IO.FS.Handle.mk out .append
  for (vals, i) in cases.zipIdx do
    let vs ← forallTelescope d.value fun xs _ => (xs.zip vals.toArray).mapM fun (x, a) => do
      let t ← whnfR (← inferType x)
      return mkApp2 (mkConst ``BitVec.ofNat) (t.getArg! 0) (mkNatLit a)
    let body ← instantiateForall d.value vs
    let φ := match body with
      | .forallE _ dom φ _ => if dom.isAppOfArity ``Returns 4 then φ else body
      | _ => body
    let (b, status) ← evalDecide φ
    h.putStrLn (Json.compress <| Json.mkObj [("claim", toJson c), ("case", toJson i),
      ("holds", toJson b), ("status", toJson status)])
    h.flush

end FVA.Explain
