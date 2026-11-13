import FVATest.Spec
import FVATest.Profile
import FVA.Profile

/-!
# P′ contract harness (U28b E3, FVATest only)

Oracle-assisted execution of P′ scripts on the reference stepper (`Ref.seq`), for the blind P′
suite and the official P′ scripts until U28c (validation over P′), U28d (the machine) and U28e (the
public runner) take over. A positive payload must pass `wasm-tools validate` with the support
manifest's features, FVA's syntax classifier (`p-prime`) and the ≤ 1-memory static profile; a
2.0-profile payload (`Module.inP2`) that FVA's validator rejects is skipped (3.0 admits more).
Production validation and claims keep the 2.0 boundary. Commands and outcomes as `fvatest spec`;
`assert_exception` passes on an uncaught exception (`[ref.exn a, throw_ref]` final), its category
alone.
-/

namespace FVA.Test.P2

open FVA.Wasm FVA.Wasm.Exec Lean
open FVA.Test.Spec (Resolution resolveIn Tally tally meets parseValue showValue outcome
  checkMalformed exported spectest spectestStore ModuleIssue)

/-- Script state over the reference store (`Spec.State` holds the machine's). -/
structure State where
  store : Store := spectestStore
  current : Option ModuleInst := none
  named : List (String × Option ModuleInst) := []
  registered : List (String × Option ModuleInst) := [("spectest", some spectest)]

/-- Resolve a script module name, or the latest module when no name is given. -/
def State.moduleAt (s : State) (j : Json) : Option ModuleInst :=
  match (j.getObjValAs? String "module").toOption with
  | some name => (s.named.lookup name).join
  | none => s.current

/-- An action's or initialization's outcome. -/
inductive Result where
  | returned (vs : List Val)
  | trapped
  /-- An uncaught exception: the sequence is `[ref.exn a, throw_ref]`. -/
  | thrown (a : Nat)
  | exhausted
  | stuck
  | skipped (why : String)

/-- How a final sequence ended: values, `trap`, an uncaught exception, else stuck. -/
def ending : List AInstr → Result
  | [.trap] => .trapped
  | [.refExnAddr a, .plain .throwRef] => .thrown a
  | es => match es.mapM Ref.toVal with
    | some vs => .returned vs
    | none => .stuck

/-- Reference-stepper steps; the reached configuration survives every outcome. -/
def runRef : Nat → Config → Config × Result
  | 0, c => (c, .exhausted)
  | n + 1, c => match Ref.seq c.store c.frame [] c.instrs with
    | .step s f es => runRef n ⟨s, f, es⟩
    | .final => (c, ending c.instrs)
    | _ => (c, match ending c.instrs with
      | .thrown a => .thrown a
      | _ => .stuck)

/-- A diagnostic outcome, separate from the expected result. -/
def Result.describe : Result → String
  | .returned vs => "returned [" ++ String.intercalate ", " (vs.map showValue) ++ "]"
  | .trapped => "trap" | .thrown a => s!"exception exn:@{a}" | .exhausted => "fuel exhausted"
  | .stuck => "stuck" | .skipped why => s!"skipped ({why})"

/-- Allocate, evaluate the initializers in the placeholder allocation and run the
initialization code; the store survives a trap (§4.5.4). `none` = an initializer failed. -/
def runInit (fuel : Nat) (s : Store) (m : FVA.Wasm.Module) (imports : List ExternVal) :
    Option (Config × Result) := do
  let (s₀, inst₀) := allocModule s m imports (m.globals.map fun _ => .i32 0)
    (m.tables.map fun _ => .null) (m.elems.map fun _ => [])
  let gvals ← m.globals.mapM fun g => Ref.evalConst fuel s₀ inst₀ g.init
  let trefs ← m.tables.mapM fun t => Ref.evalConst fuel s₀ inst₀ t.init >>= Ref.asRef
  let erefs ← m.elems.mapM fun e =>
    e.init.mapM fun ex => Ref.evalConst fuel s₀ inst₀ ex >>= Ref.asRef
  let (s₁, inst) := allocModule s m imports gvals trefs erefs
  some (runRef fuel ⟨s₁, ⟨[], inst⟩, (initCode m).map .plain⟩)

/-- Execute an invocation or read an exported global. -/
def action (fuel : Nat) (s : State) (j : Json) : Except String (State × Result) := do
  let some inst := s.moduleAt j | return (s, .skipped "missing/rejected module")
  let ty ← j.getObjValAs? String "type"
  let field ← j.getObjValAs? String "field"
  let some ev := exported inst field | throw s!"missing export {field}"
  match ty, ev with
  | "get", .global a =>
    let some g := s.store.globals[a]? | throw s!"missing global address {a}"
    return (s, .returned [g.value])
  | "invoke", .func a =>
    let args ← j.getObjValAs? (Array Json) "args"
    let argVals ← args.toList.mapM (parseValue inst)
    let some vs := argVals.mapM id | return (s, .skipped "unsupported action argument")
    let (c, result) := runRef fuel (invokeConfig s.store a vs)
    return ({ s with store := c.store }, result)
  | _, _ => throw s!"unsupported action/export {ty} {field}"

/-- Run one assertion or standalone action, keeping the resulting store across commands. -/
def checkAction (fuel : Nat) (s : State) (ty : String) (c : Json) :
    State × Except String (Option String) := Id.run do
  let .ok j := c.getObjVal? "action" | return (s, .error "missing action")
  let .ok (s', r) := action fuel s j | return (s, .error "action lookup/parse failed")
  if let .skipped why := r then return (s', .ok (some why))
  let expected := (c.getObjVal? "expected").toOption.getD .null
  let label := s!"{j.compress}: expected {ty} {expected.compress}, actual {r.describe}"
  match ty, r with
  | "assert_trap", .trapped | "assert_exhaustion", .exhausted | "assert_exception", .thrown _
  | "action", .returned _ => return (s', .ok none)
  | "assert_return", .returned vs =>
    let .ok es := c.getObjValAs? (Array Json) "expected" | return (s', .error label)
    let some inst := s.moduleAt j | return (s', .error label)
    let checks := (vs.zip es.toList).mapM fun (v, e) => meets inst v e
    match checks with
    | .ok bs => return (s', if vs.length == es.size && bs.all id then .ok none else .error label)
    | .error why => return (s', .ok (some why))
  | _, _ => return (s', .error label)

/-- The P′ in-profile test: oracle validation with the support manifest's features, the syntax
classifier and at most one memory; `some why` = outside P′. -/
def outsideP2 (path : System.FilePath) : IO (Option String) := do
  let oracle ← IO.Process.output {
    cmd := "wasm-tools"
    args := #["validate", s!"--features={FVA.Profile.wasmToolsFeatures}", path.toString] }
  if oracle.exitCode == 1 then return some s!"oracle rejects: {oracle.stderr.trimAscii}"
  if oracle.exitCode != 0 then
    throw (IO.userError s!"profile oracle exited {oracle.exitCode}: {oracle.stderr.trimAscii}")
  let out ← IO.FS.withTempFile fun _ tmp => do
    let strip ← IO.Process.output
      { cmd := "wasm-tools", args := #["strip", "--all", path.toString, "-o", tmp.toString] }
    if strip.exitCode != 0 then return strip
    IO.Process.output { cmd := "wasm-tools", args := #["print", tmp.toString] }
  if out.exitCode != 0 then return some "wasm-tools print failed"
  let top := FVA.Test.Profile.parse (FVA.Test.Profile.tokens out.stdout)
  match FVA.Test.Profile.classify top with
  | [] => return if FVA.Test.Profile.memoryCount top ≤ 1 then none else some "more than one memory"
  | cs => return some s!"excluded: {",".intercalate (cs.map FVA.Profile.Excluded.id)}"

/-- Decode a payload; a positive one must be in profile first. -/
def readModule (dir : System.FilePath) (c : Json) (negative : Bool) :
    IO (Except ModuleIssue FVA.Wasm.Module) := do
  let file ← IO.ofExcept (c.getObjValAs? String "filename")
  let mut path := dir / file
  if (c.getObjValAs? String "module_type").toOption == some "text" then
    let binary := path.addExtension "wasm"
    let parsed ← IO.Process.output {
      cmd := "wasm-tools"
      args := #["parse", path.toString, "-o", binary.toString] }
    if parsed.exitCode == 1 then
      return .error (.malformed s!"text parser: {parsed.stderr.trimAscii}")
    if parsed.exitCode != 0 then
      throw (IO.userError s!"text parser exited {parsed.exitCode}: {parsed.stderr.trimAscii}")
    path := binary
  if !negative then
    if let some why ← outsideP2 path then return .error (.outside s!"outside P′: {why}")
  let bs ← IO.FS.readBinFile path
  return match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .error (.unsupported pos why) => .error (.outside s!"decoder offset {pos}: {why}")
    | .error (.malformed pos why) => .error (.malformed s!"decoder offset {pos}: {why}")
    | .ok m => .ok m

/-- Positive payloads: in profile (oracle-validated) and, on the 2.0 profile, accepted by FVA's
validator (else a skip). Negative payloads: FVA's validator must reject a 2.0-profile one; P′
typing = U28c. -/
def validatePayload (dir : System.FilePath) (c : Json) (kind : String) (line : Nat) (t : Tally) :
    IO (Tally × Option FVA.Wasm.Module) := do
  match ← readModule dir c (kind == "assert_invalid") with
  | .error (.outside why) => return (tally t line (.ok (some why)), none)
  | .error (.malformed why) =>
    let result := if kind == "assert_invalid" then .ok (some why)
      else .error s!"{kind}: positive module is undecodable: {why}"
    return (tally t line result, none)
  | .ok m =>
    if kind == "assert_invalid" then
      if !m.inP2 then return (tally t line (.ok (some "P′ validation = U28c")), none)
      return (tally t line (if FVA.Wasm.Valid.validate m then
        .error "assert_invalid: validator accepted" else .ok none), none)
    -- the 2.0 validator rejects some 3.0-valid 2.0-syntax modules (3.0 constant expressions read
    -- earlier globals): P′ validation = U28c, the 2.0 runner keeps the check
    if m.inP2 && !FVA.Wasm.Valid.validate m then
      return (tally t line (.ok (some "2.0 validator rejects: P′ validation = U28c")), none)
    return (t, some m)

/-- Interpret one script (`fvatest spec`'s commands, on the reference stepper). -/
def runScript (dir : System.FilePath) (json : Json) (fuel : Nat := 2000000) : IO Tally := do
  let cmds ← IO.ofExcept (json.getObjValAs? (Array Json) "commands")
  let outcomes ← IO.getEnv "FVA_SPEC_OUTCOMES"
  let mut log : Array String := #[]
  let mut s : State := {}
  let mut t : Tally := {}
  for c in cmds do
    let ty ← IO.ofExcept (c.getObjValAs? String "type")
    let line := (c.getObjValAs? Nat "line").toOption.getD 0
    let before := t
    if ty == "module" || ty == "assert_uninstantiable" then
      let mut inst : Option ModuleInst := none
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if let some m := module then
        match resolveIn s.registered m with
        | .unavailable => t := tally t line (.ok (some "unavailable import"))
        | .unknown why => t := tally t line (.error s!"{ty}: {why}")
        | .linked imports =>
          if !Ref.importsMatch s.store m imports then
            t := tally t line (.error s!"{ty}: imports do not match")
          else match runInit fuel s.store m imports, ty with
          | some (c', .returned []), "module" =>
            s := { s with store := c'.store }
            inst := some c'.frame.inst
            t := tally t line (.ok none)
          | some (c', .trapped), "assert_uninstantiable" =>
            s := { s with store := c'.store }
            t := tally t line (.ok none)
          | some (c', r), _ =>
            s := { s with store := c'.store }
            t := tally t line (.error s!"{ty}: initialization {r.describe}")
          | none, _ => t := tally t line (.error s!"{ty}: an initializer failed")
      if ty == "module" then
        s := { s with current := inst }
        if let some name := (c.getObjValAs? String "name").toOption then
          s := { s with named := (name, inst) :: s.named }
    else if ty == "assert_invalid" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if module.isSome then t := tally t line (.ok none)
    else if ty == "assert_unlinkable" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if let some m := module then
        t := tally t line <| match resolveIn s.registered m with
          | .unavailable => .ok (some "unavailable import")
          | .unknown _ => .ok none
          | .linked imports =>
            if Ref.importsMatch s.store m imports then .error "assert_unlinkable: module links"
            else .ok none
    else if ty == "assert_malformed" then
      t := tally t line (← checkMalformed dir c)
    else if ty == "register" then
      let name ← IO.ofExcept (c.getObjValAs? String "as")
      let inst := match (c.getObjValAs? String "name").toOption with
        | some n => (s.named.lookup n).join | none => s.current
      s := { s with registered := (name, inst) :: s.registered }
      t := tally t line (.ok (if inst.isSome then none else some "register rejected module"))
    else if ["action", "assert_return", "assert_trap", "assert_exhaustion",
        "assert_exception"].contains ty then
      let (s', r) := checkAction (if ty == "assert_exhaustion" then 1000 else fuel) s ty c
      s := s'
      t := tally t line r
    else t := tally t line (.ok (some ty))
    if outcomes.isSome then log := log.push s!"{line}\t{ty}\t{outcome before t}"
  if let some path := outcomes then
    let h ← IO.FS.Handle.mk path .append
    for row in log do h.putStrLn row
  return t

end FVA.Test.P2
