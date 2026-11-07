import FVA.Impl.Exec.Ref
import FVA.Impl.Exec.Imports
import FVA.Impl.Exec.Machine
import FVA.Spec.Claims
import FVATest.Numeric
import FVATest.Valid

/-!
# Official execution-script runner

`wasm-tools json-from-wast` commands run against `Valid.validate` and the optimized machine
(`FVA.Wasm.Exec.Machine`: chunk-trie memories, every step proven to be reference-stepper steps,
the store kept in machine form across commands); one tally entry per command. Modules, unlinkable
modules and uninstantiable modules must validate before execution or import resolution; every
decodable invalid module must be rejected. Unsupported payloads, malformed assertions and invalid
modules rejected by the decoder have separate counts. Imports resolve by registered name and must
match (`Ref.importsMatch`, proven to decide `ImportsMatch`); a link-error assertion passes only on
an unknown import or a mismatch. A binary malformed payload must fail FVA's decoder; text
payloads exercise wasm-tools' parser, not FVA, and are skipped. Execution failures remain
failures, including a stuck configuration. Fuel exhaustion passes only `assert_exhaustion`; it is
not evidence of divergence. Numeric expectations include canonical/arithmetic NaN payload classes.
-/

namespace FVA.Test.Spec

open FVA.Wasm FVA.Wasm.Exec Lean

/-- Ordinary Wasm functions stand in for the observable no-result `spectest.print*` hooks. -/
def printTypes : List (String × List ValType) :=
  [("print", []), ("print_i32", [.num .i32]), ("print_i64", [.num .i64]),
   ("print_f32", [.num .f32]), ("print_f64", [.num .f64]),
   ("print_i32_f32", [.num .i32, .num .f32]), ("print_f64_f64", [.num .f64, .num .f64])]

/-- The reference interpreter's `spectest` store (float constants are IEEE bit patterns). -/
def spectestStore : Store :=
  { funcs := printTypes.map fun (_, ps) => .wasm ⟨ps, []⟩ {} ⟨0, [], []⟩,
    globals := [⟨⟨.const, .num .i32⟩, .i32 666⟩, ⟨⟨.const, .num .i64⟩, .i64 666⟩,
      ⟨⟨.const, .num .f32⟩, .f32 0x4426a666⟩, ⟨⟨.const, .num .f64⟩, .f64 0x4084d4cccccccccd⟩],
    tables := [⟨⟨⟨10, some 20⟩, .funcref⟩, List.replicate 10 (.null .funcref)⟩],
    mems := [⟨1, some 2, fun _ => 0⟩] }

/-- Exports of the fixture module; its store addresses are independent of tested modules. -/
def spectest : ModuleInst :=
  { exports := (printTypes.zipIdx.map fun ((name, _), i) => ⟨name, .func i⟩) ++
      [⟨"global_i32", .global 0⟩, ⟨"global_i64", .global 1⟩, ⟨"global_f32", .global 2⟩,
       ⟨"global_f64", .global 3⟩, ⟨"table", .table 0⟩, ⟨"memory", .mem 0⟩] }

/-- Script state: names and registrations retain rejected-module entries as `none`. -/
structure State where
  /-- Store retained across module initialization and actions, including trapped writes. -/
  store : Machine.MStore := Machine.MStore.ofStore spectestStore
  /-- Latest module; rejection clears it rather than reusing the previous instance. -/
  current : Option ModuleInst := none
  /-- Script identifiers retain rejected modules as `none`. -/
  named : List (String × Option ModuleInst) := []
  /-- Import registrations, seeded with the `spectest` fixture. -/
  registered : List (String × Option ModuleInst) := [("spectest", some spectest)]

/-- Resolve a script module name, or the latest module when no name is given. -/
def State.moduleAt (s : State) (j : Json) : Option ModuleInst :=
  match (j.getObjValAs? String "module").toOption with
  | some name => (s.named.lookup name).join
  | none => s.current

/-- Find an exported external value. -/
def exported (inst : ModuleInst) (field : String) : Option ExternVal :=
  (inst.exports.find? (·.name == field)).map (·.value)

/-- Import resolution: every import found, a link error, or a dependency FVA rejected. -/
inductive Resolution where
  /-- Every import found, in order (shared store addresses). -/
  | linked (imports : List ExternVal)
  /-- A module name never registered or a missing export: a link error. -/
  | unknown (why : String)
  /-- An import names a module FVA rejected: its exports are unknown here. -/
  | unavailable

/-- Resolve imports against the registered instances; one rejected dependency makes the result
`unavailable` (the link outcome depends on a module FVA never instantiated). -/
def resolveImports (s : State) (m : FVA.Wasm.Module) : Resolution :=
  let found := m.imports.map fun im => match s.registered.lookup im.module with
    | none => Except.error (some s!"unknown module {im.module}")
    | some none => .error none
    | some (some inst) => match exported inst im.name with
      | some ev => .ok ev
      | none => .error (some s!"unknown import {im.module}.{im.name}")
  if found.any (· matches .error none) then .unavailable
  else match found.mapM id with
    | .ok evs => .linked evs
    | .error why => .unknown (why.getD "unknown import")

/-- Translate a numeric runner value to an execution value. -/
def fromNumeric : Numeric.Value → Val
  | .i32 v => .i32 v | .i64 v => .i64 v | .f32 v => .f32 v | .f64 v => .f64 v

/-- Translate an execution number to the numeric runner's comparison representation. -/
def toNumeric : Val → Option Numeric.Value
  | .i32 v => some (.i32 v) | .i64 v => some (.i64 v)
  | .f32 v => some (.f32 v) | .f64 v => some (.f64 v) | _ => none

/-- Parse an action operand; function references in scripts name the current module's index. -/
def parseValue (inst : ModuleInst) (j : Json) : Except String (Option Val) := do
  let ty ← j.getObjValAs? String "type"
  let v ← j.getObjValAs? String "value"
  match ty, v with
  | "funcref", "null" => return some (.ref (.null .funcref))
  | "externref", "null" => return some (.ref (.null .externref))
  | "funcref", n => return (n.toNat? >>= fun i => inst.funcs[i]?).map (.ref ∘ .func)
  | "externref", n => return n.toNat?.map (.ref ∘ .extern)
  | _, _ => return (← Numeric.parseValue j).map fromNumeric

/-- The JSON value type, including reference types. -/
def valueType : Val → String
  | .i32 _ => "i32" | .i64 _ => "i64" | .f32 _ => "f32" | .f64 _ => "f64"
  | .ref (.null .funcref) | .ref (.func _) => "funcref"
  | .ref (.null .externref) | .ref (.extern _) => "externref"

/-- Equality of exact expected values, including reference identity. -/
def sameValue : Val → Val → Bool
  | .i32 a, .i32 b => a == b | .i64 a, .i64 b => a == b
  | .f32 a, .f32 b => a == b | .f64 a, .f64 b => a == b
  | .ref (.null a), .ref (.null b) => decide (a = b)
  | .ref (.func a), .ref (.func b) | .ref (.extern a), .ref (.extern b) => a == b
  | _, _ => false

/-- Match a JSON expectation: exact identity, typed NaN class, or a non-null reference. -/
def meets (inst : ModuleInst) (v : Val) (j : Json) : Except String Bool := do
  let ty ← j.getObjValAs? String "type"
  if ty == "refnull" then return match v with | .ref (.null _) => true | _ => false
  if ty == "nullfuncref" then return sameValue v (.ref (.null .funcref))
  if ty == "nullexternref" then return sameValue v (.ref (.null .externref))
  if ty != valueType v then return false
  if let some n := toNumeric v then
    let some e ← Numeric.parseExpect j | throw s!"unsupported expectation {j.compress}"
    return Numeric.meets n e
  match (j.getObjValAs? String "value").toOption with
  | none => return match v with | .ref (.func _) | .ref (.extern _) => true | _ => false
  | some _ =>
    let some e ← parseValue inst j | throw s!"unsupported expectation {j.compress}"
    return sameValue v e

/-- Compact value diagnostics retain float bits and reference addresses. -/
def showValue : Val → String
  | .i32 b => s!"i32:{b.toNat}" | .i64 b => s!"i64:{b.toNat}"
  | .f32 b => s!"f32:{b.toNat}" | .f64 b => s!"f64:{b.toNat}"
  | .ref (.null .funcref) => "funcref:null" | .ref (.null .externref) => "externref:null"
  | .ref (.func a) => s!"funcref:@{a}" | .ref (.extern a) => s!"externref:{a}"

/-- The action outcome; a missing/rejected module is explicitly outside this runner's reach. -/
inductive Result where
  | returned (vs : List Val)
  | trapped
  | exhausted
  | stuck
  | skipped (why : String)

/-- Machine steps; the reached store survives every outcome. -/
def runMachine (fuel : Nat) (m : Machine.MState) : Machine.MState × Result :=
  match m.run fuel with
  | (m', true) => (m', .exhausted)
  | (m', false) => (m', match m'.ending with
    | .returned vs => .returned vs
    | .trapped => .trapped
    | .stuck => .stuck)

/-- Execute an invocation or read an exported global; traps retain their preceding effects. -/
def action (fuel : Nat) (s : State) (j : Json) : Except String (State × Result) := do
  let some inst := s.moduleAt j | return (s, .skipped "missing/rejected module")
  let ty ← j.getObjValAs? String "type"
  let field ← j.getObjValAs? String "field"
  let some ev := exported inst field | throw s!"missing export {field}"
  match ty, ev with
  | "get", .global a =>
    let some g := s.store.base.globals[a]? | throw s!"missing global address {a}"
    return (s, .returned [g.value])
  | "invoke", .func a =>
    let args ← j.getObjValAs? (Array Json) "args"
    let argVals ← args.toList.mapM (parseValue inst)
    let some vs := argVals.mapM id | return (s, .skipped "unsupported action argument")
    let (m', result) := runMachine fuel (Machine.MState.ofInvoke s.store a vs)
    return ({ s with store := m'.store }, result)
  | _, _ => throw s!"unsupported action/export {ty} {field}"

/-- A diagnostic outcome, separate from the expected result. -/
def Result.describe : Result → String
  | .returned vs => "returned [" ++ String.intercalate ", " (vs.map showValue) ++ "]"
  | .trapped => "trap" | .exhausted => "fuel exhausted" | .stuck => "stuck"
  | .skipped why => s!"skipped ({why})"

/-- Disjoint payload categories: checked modules by command kind, then explicit exclusions. -/
structure ValidationCounts where
  /-- Decodable baseline module commands sent to the validator. -/
  modules : Nat := 0
  /-- Unlinkable baseline payloads checked for validity before import resolution. -/
  unlinkable : Nat := 0
  /-- Baseline payloads checked before their trapping initialization runs. -/
  uninstantiable : Nat := 0
  /-- Decodable invalid payloads checked for rejection. -/
  invalid : Nat := 0
  /-- Assertions assigned to decoder/parser coverage rather than validation. -/
  malformed : Nat := 0
  /-- Payloads excluded by the feature oracle or an unsupported decoder feature. -/
  outside : Nat := 0
  /-- Payloads rejected before validation by binary decoding or text parsing. -/
  undecodable : Nat := 0

/-- Stable column order for the gate's pinned validation denominators. -/
def ValidationCounts.summary (v : ValidationCounts) : String :=
  s!"{v.modules} {v.unlinkable} {v.uninstantiable} {v.invalid} " ++
    s!"{v.malformed} {v.outside} {v.undecodable}"

/-- Count every validation attempt, whether its verdict agrees with the oracle or not. -/
def ValidationCounts.checked (v : ValidationCounts) (kind : String) : ValidationCounts :=
  match kind with
  | "module" => { v with modules := v.modules + 1 }
  | "assert_unlinkable" => { v with unlinkable := v.unlinkable + 1 }
  | "assert_uninstantiable" => { v with uninstantiable := v.uninstantiable + 1 }
  | _ => { v with invalid := v.invalid + 1 }

/-- One entry per script command; skipped setup cannot silently reuse an older module. -/
structure Tally extends Numeric.Tally where
  /-- Skip details, for coverage accounting without treating a skip as a passing assertion. -/
  skips : Array String := #[]
  /-- Payload denominators, separate from the execution command tallies. -/
  validation : ValidationCounts := {}

/-- Add a pass, failure, or explicit coverage exclusion. -/
def tally (t : Tally) (line : Nat) (result : Except String (Option String)) : Tally :=
  match result with
  | .ok none => { t with pass := t.pass + 1 }
  | .ok (some why) => { t with skip := t.skip + 1, skips := t.skips.push s!"line {line}: {why}" }
  | .error why =>
    { t with fail := t.fail + 1, failures := t.failures.push s!"line {line}: {why}" }

/-- Run one assertion or standalone action, keeping the resulting store across commands. -/
def checkAction (fuel : Nat) (s : State) (ty : String) (c : Json) :
    State × Except String (Option String) := Id.run do
  let .ok j := c.getObjVal? "action" | return (s, .error "missing action")
  let .ok (s', r) := action fuel s j | return (s, .error "action lookup/parse failed")
  if let .skipped why := r then return (s', .ok (some why))
  let expected := (c.getObjVal? "expected").toOption.getD .null
  let label := s!"{j.compress}: expected {ty} {expected.compress}, actual {r.describe}"
  match ty, r with
  | "assert_trap", .trapped | "assert_exhaustion", .exhausted
  | "action", .returned _ => return (s', .ok none)
  | "assert_return", .returned vs =>
    let .ok es := c.getObjValAs? (Array Json) "expected" | return (s', .error label)
    let some inst := s.moduleAt j | return (s', .error label)
    let checks := (vs.zip es.toList).mapM fun (v, e) => meets inst v e
    match checks with
    | .ok bs => return (s', if vs.length == es.size && bs.all id then .ok none else .error label)
    | .error why => return (s', .ok (some why))
  | _, _ => return (s', .error label)

/-- Run initialization without discarding the store on a trap: imported writes persist (§4.5.4).
Successful `module` commands use `Machine.instantiate`; this exposes its failed-init outcome. -/
def runInit (fuel : Nat) (s : Machine.MStore) (m : FVA.Wasm.Module) (imports : List ExternVal) :
    Option (Machine.MState × Result) := do
  let (s₀, inst₀) := s.alloc m imports (m.globals.map fun g => g.type.val.default)
    (m.elems.map fun _ => [])
  let gvals ← m.globals.mapM fun g => Ref.evalConst fuel s₀.abs inst₀ g.init
  let erefs ← m.elems.mapM fun e =>
    e.init.mapM fun ex => Ref.evalConst fuel s₀.abs inst₀ ex >>= Ref.asRef
  let (s₁, inst) := s.alloc m imports gvals erefs
  some (runMachine fuel
    { store := s₁, frame := ⟨[], inst⟩, stack := [], code := (initCode m).map .plain, ctl := [] })

/-- Unsupported payloads differ from malformed inputs that never reach validation. -/
inductive ModuleIssue where
  | outside (why : String)
  | malformed (why : String)

/-- The pinned suite mixes newer proposals into positive modules. The independent baseline
oracle classifies those before decoding; a baseline-positive decode failure is an error.
Negative cases check every decodable AST, including invalid globals and combined memories. -/
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
    let oracle ← IO.Process.output {
      cmd := "wasm-tools"
      args := #["validate", "--features=wasm2,-simd", path.toString] }
    if oracle.exitCode == 1 then
      return .error (.outside s!"outside wasm2,-simd: {oracle.stderr.trimAscii}")
    if oracle.exitCode != 0 then
      throw (IO.userError s!"profile oracle exited {oracle.exitCode}: {oracle.stderr.trimAscii}")
  let bs ← IO.FS.readBinFile path
  return match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .error (.unsupported pos why) =>
      if negative then .error (.outside s!"decoder offset {pos}: {why}")
      else .error (.malformed s!"baseline-positive unsupported at {pos}: {why}")
    | .error (.malformed pos why) => .error (.malformed s!"decoder offset {pos}: {why}")
    | .ok m => .ok m

/-- Only accepted positive payloads reach instantiation; validation failures still count. -/
def validatePayload (dir : System.FilePath) (c : Json) (kind : String) (line : Nat) (t : Tally) :
    IO (Tally × Option FVA.Wasm.Module) := do
  match ← readModule dir c (kind == "assert_invalid") with
  | .error (.outside why) =>
    let t := { t with validation.outside := t.validation.outside + 1 }
    return (tally t line (.ok (some why)), none)
  | .error (.malformed why) =>
    let t := { t with validation.undecodable := t.validation.undecodable + 1 }
    let result := if kind == "assert_invalid" then .ok (some why)
      else .error s!"{kind}: positive module is undecodable: {why}"
    return (tally t line result, none)
  | .ok m =>
    let t := { t with validation := t.validation.checked kind }
    let accepted := FVA.Wasm.Valid.validate m
    if kind == "assert_invalid" then
      return (tally t line (if accepted then .error "assert_invalid: validator accepted"
        else .ok none), none)
    if !accepted then return (tally t line (.error s!"{kind}: validator rejected"), none)
    return (t, some m)

/-- A binary malformed payload must fail FVA's decoder. `unsupported` = outside the profile;
decoded but invalid = "rejected only by validation" (Wasm 3.0 calls memarg flags ≥ 0x80
malformed, Wasm 2.0 invalid). Text payloads test wasm-tools' parser and are skipped. -/
def checkMalformed (dir : System.FilePath) (c : Json) : IO (Except String (Option String)) := do
  if ((c.getObjValAs? String "module_type").toOption.getD "binary") != "binary" then
    return .ok (some "text format")
  let file ← IO.ofExcept (c.getObjValAs? String "filename")
  let bs ← IO.FS.readBinFile (dir / file)
  return match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .error (.malformed _ _) => .ok none
    | .error (.unsupported pos why) => .ok (some s!"outside: decoder offset {pos}: {why}")
    | .ok m =>
      if FVA.Wasm.Valid.validate m then .error "assert_malformed: module decodes + validates"
      else .ok (some "rejected only by validation")

/-- The outcome one command added to the tally: `pass`, `fail: why`, `skip: why`. -/
def outcome (before after : Tally) : String :=
  if after.pass > before.pass then "pass"
  else if after.fail > before.fail then s!"fail: {after.failures.back?.getD ""}"
  else if after.skip > before.skip then s!"skip: {after.skips.back?.getD ""}"
  else "none"

/-- Interpret one script with an action budget and a smaller stack-exhaustion probe budget.
`FVA_SPEC_OUTCOMES=<file>` appends one `line<TAB>type<TAB>outcome` row per command. -/
def runScript (dir : System.FilePath) (json : Json) (fuel : Nat := 2000000) : IO Tally := do
  let cmds ← IO.ofExcept (json.getObjValAs? (Array Json) "commands")
  let trace := (← IO.getEnv "FVA_SPEC_TRACE") == some "1"
  let outcomes ← IO.getEnv "FVA_SPEC_OUTCOMES"
  let mut log : Array String := #[]
  let mut s : State := {}
  let mut t : Tally := {}
  for c in cmds do
    let ty ← IO.ofExcept (c.getObjValAs? String "type")
    let line := (c.getObjValAs? Nat "line").toOption.getD 0
    if trace then IO.eprintln s!"spec line {line}: {ty}"
    let before := t
    if ty == "module" then
      let mut inst : Option ModuleInst := none
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      match module with
      | none => pure ()
      | some m =>
        match resolveImports s m with
        | .unavailable => t := tally t line (.ok (some "unavailable import"))
        | .unknown why => t := tally t line (.error s!"module: {why}")
        | .linked imports =>
          if !Ref.importsMatch s.store.abs m imports then
            t := tally t line (.error "module: imports do not match")
          else match Machine.instantiate fuel s.store m imports with
          | some (store, i) =>
            s := { s with store }
            inst := some i
            t := tally t line (.ok none)
          | none => t := tally t line (.error "module: instantiation failed")
      s := { s with current := inst }
      if let some name := (c.getObjValAs? String "name").toOption then
        s := { s with named := (name, inst) :: s.named }
    else if ty == "assert_uninstantiable" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      match module with
      | none => pure ()
      | some m =>
        match resolveImports s m with
        | .unavailable => t := tally t line (.ok (some "unavailable import"))
        | .unknown why => t := tally t line (.error s!"assert_uninstantiable: {why}")
        | .linked imports =>
          if !Ref.importsMatch s.store.abs m imports then
            t := tally t line (.error "assert_uninstantiable: imports do not match")
          else match runInit fuel s.store m imports with
          | some (m', .trapped) =>
            s := { s with store := m'.store }
            t := tally t line (.ok none)
          | some (m', .returned _) =>
            s := { s with store := m'.store }
            t := tally t line
              (.error "assert_uninstantiable: expected trap, initialization returned")
          | _ => t := tally t line (.error "initialization stuck or fuel exhausted")
    else if ty == "assert_invalid" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if module.isSome then t := tally t line (.ok none)
    else if ty == "assert_unlinkable" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if let some m := module then
        t := tally t line <| match resolveImports s m with
          | .unavailable => .ok (some "unavailable import")
          | .unknown _ => .ok none
          | .linked imports =>
            if Ref.importsMatch s.store.abs m imports then .error "assert_unlinkable: module links"
            else .ok none
    else if ty == "assert_malformed" then
      t := { t with validation.malformed := t.validation.malformed + 1 }
      t := tally t line (← checkMalformed dir c)
    else if ty == "register" then
      let name ← IO.ofExcept (c.getObjValAs? String "as")
      let inst := match (c.getObjValAs? String "name").toOption with
        | some n => (s.named.lookup n).join | none => s.current
      s := { s with registered := (name, inst) :: s.registered }
      t := tally t line (.ok (if inst.isSome then none else some "register rejected module"))
    else if ["action", "assert_return", "assert_trap", "assert_exhaustion"].contains ty then
      let (s', r) := checkAction (if ty == "assert_exhaustion" then 1000 else fuel) s ty c
      s := s'
      t := tally t line r
    else t := tally t line (.ok (some ty))
    if outcomes.isSome then log := log.push s!"{line}\t{ty}\t{outcome before t}"
  if let some path := outcomes then
    let h ← IO.FS.Handle.mk path .append
    for row in log do h.putStrLn row
  return t

end FVA.Test.Spec
