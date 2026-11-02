import Lean
import FVA.Spec.CAbi

/-!
# `fva explain` helpers (tooling, outside the trusted base)

Run inside the project (`lake env lean` on a generated file that imports the spec module):
`shapes` reads each claim's docstring, elaborated statement and shape
`∀ (x : BitVec n)…, Returns m "f" args res`; `declared` lists the review modules' names;
`run` computes `res` on concrete inputs.

Values come from `whnf` (definitional: compiled code, which an `implemented_by` override can
change, never runs) and each is confirmed by the kernel (`res = value` by `rfl`, D16). Results go
to a file, one JSON line per case, flushed: `#eval` buffers stdout until the command ends, and a
too-costly case can end the process mid-command.
-/

namespace FVA.Explain

open Lean Meta FVA.Wasm FVA.Wasm.Exec

/-- `{"fn": f, "params": [{"name", "bits"}]}`, or `null` when the claim has another shape. -/
def shape (c : Name) : MetaM Json := do
  let some (.defnInfo d) := (← getEnv).find? c | return .null
  forallTelescope d.value fun xs body => do
    unless body.isAppOfArity ``Returns 4 do return .null
    let .lit (.strVal fn) := body.getArg! 1 | return .null
    let mut ps := #[]
    for x in xs do
      let t ← whnfR (← inferType x)
      unless t.isAppOfArity ``BitVec 1 do return .null
      let some n ← evalNat (t.getArg! 0) | return .null
      ps := ps.push <| Json.mkObj [("name", toJson (← x.fvarId!.getUserName).eraseMacroScopes),
        ("bits", toJson n)]
    return Json.mkObj [("fn", toJson fn), ("params", Json.arr ps)]

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

/-- The kernel's verdict on `res = v` by `rfl`: `some true` accepted, `some false` refused,
`none` = cancelled at its deadline (`tk`) or out of its own resources. -/
def kernelAccepts (res v : Lean.Expr) (tk : IO.CancelToken) : MetaM (Option Bool) := do
  let decl := Declaration.thmDecl
    { name := `_fva_explain_case, levelParams := [], type := ← mkEq res v, value := ← mkEqRefl v }
  return match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl tk with
    | .ok _ => some true
    | .error .interrupted | .error .deterministicTimeout | .error .deepRecursion
    | .error .excessiveMemory => none
    | .error _ => some false

/-- Append `{"claim", "case", "res", "status"}` per case of `cases` (arguments as naturals) to
`out`: `res` = the claim's `Returns` result reduced by `whnf`, `status` = `confirmed` (the kernel
accepts `result = res`), `refused` (it does not: `res` is shown as such), `cost` (past the
reduction or kernel budget), `stuck` (no literal values). -/
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
    let res := (← instantiateForall d.value vs).getArg! 3
    let tk ← IO.CancelToken.new
    let (vals, status) ← tryCatchRuntimeEx (do
        let some vals ← values res | return ([], "stuck")
        return (vals, match ← kernelAccepts res (valsExpr vals) tk with
          | some true => "confirmed" | some false => "refused" | none => "cost"))
      fun _ => return ([], "cost")
    h.putStrLn (Json.compress <| Json.mkObj [("claim", toJson c), ("case", toJson i),
      ("res", Json.arr (vals.toArray.map fun (t, n) =>
        Json.mkObj [("type", toJson t), ("value", toJson n)])), ("status", toJson status)])
    h.flush

end FVA.Explain
