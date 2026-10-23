import Lean
import FVA.Spec.CAbi

/-!
# `fva explain` helpers (tooling, outside the trusted base)

Run inside the project (`lake env lean` on a generated file that imports the spec module):
`shapes` reads each claim's docstring, elaborated statement and shape
`∀ (x : BitVec n)…, Returns m "f" args res`; `run` computes `res` on concrete inputs.

Values come from Lean's compiled evaluator, so an `implemented_by` override in the spec closure
could show a value the kernel never sees; `fva trust` rejects every such override. Results go to
a file, one JSON line per case, flushed: `#eval` buffers stdout until the command ends, and a
too-costly case (deep recursion, long loop) kills the process mid-command.
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

/-- A result value as JSON: its type and its bits as a natural number. -/
def valJson : Val → Json
  | .i32 v => Json.mkObj [("type", "i32"), ("value", toJson v.toNat)]
  | .i64 v => Json.mkObj [("type", "i64"), ("value", toJson v.toNat)]
  | .f32 v => Json.mkObj [("type", "f32"), ("value", toJson v.toNat)]
  | .f64 v => Json.mkObj [("type", "f64"), ("value", toJson v.toNat)]
  | .ref _ => Json.mkObj [("type", "ref")]

/-- Append `{"claim", "case", "res"}` per case of `cases` (arguments as naturals) to `out`. -/
def run (c : Name) (cases : List (List Nat)) (out : System.FilePath) : MetaM Unit := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c}: not a definition"
  let h ← IO.FS.Handle.mk out .append
  let listVal := mkApp (mkConst ``List [Level.zero]) (mkConst ``Val)
  for (args, i) in cases.zipIdx do
    let vs ← forallTelescope d.value fun xs _ => do
      let mut vs := #[]
      for (x, a) in xs.zip args.toArray do
        let t ← whnfR (← inferType x)
        vs := vs.push (mkApp2 (mkConst ``BitVec.ofNat) (t.getArg! 0) (mkNatLit a))
      return vs
    let e ← instantiateForall d.value vs
    let res ← unsafe evalExpr (List Val) listVal (e.getArg! 3)
    h.putStrLn (Json.compress <| Json.mkObj [("claim", toJson c), ("case", toJson i),
      ("res", Json.arr (res.map valJson).toArray)])
    h.flush

end FVA.Explain
