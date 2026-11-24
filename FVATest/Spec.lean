import FVA.Impl.Exec.Ref
import FVA.Impl.Exec.Imports
import FVA.Impl.Exec.Machine
import FVA.Spec.Claims
import FVATest.Numeric
import FVATest.Profile
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
  { funcs := printTypes.map fun (_, ps) => .wasm ⟨[⟨ps, []⟩], 0⟩ {} ⟨0, [], []⟩,
    globals := [⟨⟨.const, .num .i32⟩, .i32 666⟩, ⟨⟨.const, .num .i64⟩, .i64 666⟩,
      ⟨⟨.const, .num .f32⟩, .f32 0x4426a666⟩, ⟨⟨.const, .num .f64⟩, .f64 0x4084d4cccccccccd⟩],
    tables := [⟨⟨⟨10, some 20⟩, .funcref⟩, List.replicate 10 .null⟩],
    mems := [⟨1, some 2, fun _ => 0⟩] }

/-- Exports of the fixture module; its store addresses are independent of tested modules. -/
def spectest : ModuleInst :=
  { exports := (printTypes.zipIdx.map fun ((name, _), i) => ⟨name, .func i⟩) ++
      [⟨"global_i32", .global 0⟩, ⟨"global_i64", .global 1⟩, ⟨"global_f32", .global 2⟩,
       ⟨"global_f64", .global 3⟩, ⟨"table", .table 0⟩, ⟨"memory", .mem 0⟩] }

/-- A module entry: its instance (`none` = FVA rejected or skipped it) and the line of the
`module` command that produced it, which a dependent command's skip names (U28e I6). -/
abbrev Entry := Option ModuleInst × Nat

/-- Script state: the latest module, names and registrations keep rejected modules as entries
without an instance, so an absent name stays apart from a rejected module. -/
structure State where
  /-- Store retained across module initialization and actions, including trapped writes. -/
  store : Machine.MStore := Machine.MStore.ofStore spectestStore
  /-- Latest module; rejection clears its instance rather than reusing the previous one. -/
  current : Option Entry := none
  /-- Script identifiers. -/
  named : List (String × Entry) := []
  /-- Import registrations, seeded with the `spectest` fixture. -/
  registered : List (String × Entry) := [("spectest", (some spectest, 0))]

/-- The entry of a script module name, or of the latest module when no name is given. -/
def State.entryAt (s : State) (j : Json) : Option Entry :=
  match (j.getObjValAs? String "module").toOption with
  | some name => s.named.lookup name
  | none => s.current

/-- The instance a command names: `.error (some l)` = the module of line `l` was rejected (a
dependent skip), `.error none` = no such module was ever defined (a failure). -/
def State.moduleAt (s : State) (j : Json) : Except (Option Nat) ModuleInst :=
  match s.entryAt j with
  | some (some inst, _) => .ok inst
  | some (none, l) => .error (some l)
  | none => .error none

/-- Find an exported external value. -/
def exported (inst : ModuleInst) (field : String) : Option ExternVal :=
  (inst.exports.find? (·.name == field)).map (·.value)

/-- Import resolution: every import found, a link error, or a dependency FVA rejected. -/
inductive Resolution where
  /-- Every import found, in order (shared store addresses). -/
  | linked (imports : List ExternVal)
  /-- A module name never registered or a missing export: a link error. -/
  | unknown (why : String)
  /-- An import names a module FVA rejected (its `module` command's line): its exports are
  unknown here. -/
  | unavailable (line : Nat)

/-- Resolve imports against registered instances; one rejected dependency makes the result
`unavailable` (the link outcome depends on a module FVA never instantiated). -/
def resolveIn (registered : List (String × Entry)) (m : FVA.Wasm.Module) : Resolution :=
  let found := m.imports.map fun im => match registered.lookup im.module with
    | none => Except.error (Sum.inl s!"unknown module {im.module}")
    | some (none, l) => .error (.inr l)
    | some (some inst, _) => match exported inst im.name with
      | some ev => .ok ev
      | none => .error (.inl s!"unknown import {im.module}.{im.name}")
  match found.findSome? fun | .error (.inr l) => some l | _ => none with
  | some l => .unavailable l
  | none => match found.mapM id with
    | .ok evs => .linked evs
    | .error (.inl why) => .unknown why
    | .error (.inr l) => .unavailable l

/-- `resolveIn` over the script's registrations. -/
def resolveImports (s : State) (m : FVA.Wasm.Module) : Resolution := resolveIn s.registered m

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
  | "funcref", "null" | "externref", "null" | "exnref", "null" => return some (.ref .null)
  | "funcref", n => return (n.toNat? >>= fun i => inst.funcs[i]?).map (.ref ∘ .func)
  | "externref", n => return n.toNat?.map (.ref ∘ .extern)
  | _, _ => return (← Numeric.parseValue j).map fromNumeric

/-- The JSON value type of a non-null value (a null carries no type: `meets` matches it
first). -/
def valueType : Val → String
  | .i32 _ => "i32" | .i64 _ => "i64" | .f32 _ => "f32" | .f64 _ => "f64"
  | .ref (.func _) => "funcref" | .ref (.extern _) => "externref" | .ref (.exn _) => "exnref"
  | .ref .null => "null"

/-- Equality of exact expected values, including reference identity. -/
def sameValue : Val → Val → Bool
  | .i32 a, .i32 b => a == b | .i64 a, .i64 b => a == b
  | .f32 a, .f32 b => a == b | .f64 a, .f64 b => a == b
  | .ref .null, .ref .null => true
  | .ref (.func a), .ref (.func b) | .ref (.extern a), .ref (.extern b)
  | .ref (.exn a), .ref (.exn b) => a == b
  | _, _ => false

/-- Match a JSON expectation: exact identity, typed NaN class, or a non-null reference. -/
def meets (inst : ModuleInst) (v : Val) (j : Json) : Except String Bool := do
  let ty ← j.getObjValAs? String "type"
  -- 3.0's one null value (`REF.NULL_ADDR`) meets every null expectation, as in the reference
  -- interpreter's script runner (runner.ml:476)
  let nullExpected := ty == "refnull" || ty == "nullfuncref" || ty == "nullexternref" ||
    (j.getObjValAs? String "value").toOption == some "null"
  if let .ref .null := v then return nullExpected
  if nullExpected || ty != valueType v then return false
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
  | .ref .null => "ref:null" | .ref (.func a) => s!"funcref:@{a}"
  | .ref (.extern a) => s!"externref:{a}" | .ref (.exn a) => s!"exnref:@{a}"

/-- The action outcome; a missing/rejected module is explicitly outside this runner's reach. -/
inductive Result where
  | returned (vs : List Val)
  | trapped
  /-- An uncaught exception (`assert_exception` = U28e). -/
  | thrown (a : Nat)
  | exhausted
  | stuck
  | skipped (why : String)

/-- The engine running initialization and actions (U28e I7): the optimized machine (default) or
the reference stepper, kept so a blind suite compares the two command by command (forward
simulation alone misses a machine that stops early, U28d E4). Fuel counts the engine's own
steps: a value movement is a machine step and no reference step. -/
inductive Engine where
  | machine
  | ref
  deriving DecidableEq

/-- The engine's command-line name. -/
def Engine.name : Engine → String
  | .machine => "machine" | .ref => "ref"

/-- `fvatest spec` arguments (U28e I7): `[--engine ref|machine] [--fuel N] SCRIPT…`, options
first and at most once each; `none` = a usage error. Defaults: the machine, 40,000,000 steps
(the official tail-call scripts recurse a million calls deep; 2,000,000 steps exhaust 11). -/
def parseArgs : List String → Option (Engine × Nat × List String) :=
  go none none
where
  /-- The options read so far, then the rest. -/
  go (engine : Option Engine) (fuel : Option Nat) :
      List String → Option (Engine × Nat × List String)
    | "--engine" :: e :: rest => do
      guard engine.isNone
      let e' ← match e with | "machine" => some Engine.machine | "ref" => some .ref | _ => none
      go (some e') fuel rest
    | "--fuel" :: n :: rest => do
      guard fuel.isNone
      let k ← n.toNat?
      guard (k > 0)
      go engine (some k) rest
    | scripts => do
      guard (!scripts.isEmpty && scripts.all fun a => !a.startsWith "--")
      some (engine.getD .machine, fuel.getD 40000000, scripts)

#guard (parseArgs ["a.json"]).map (·.2.1) == some 40000000
#guard (parseArgs ["--engine", "ref", "--fuel", "7", "a.json"]).map (·.1) == some .ref
#guard parseArgs [] == none
#guard parseArgs ["--engine", "gpu", "a.json"] == none
#guard parseArgs ["--engine", "ref", "--engine", "ref", "a.json"] == none
#guard parseArgs ["--fuel", "x", "a.json"] == none
#guard parseArgs ["--fuel", "0", "a.json"] == none
#guard parseArgs ["--bogus", "a.json"] == none
#guard parseArgs ["--engine", "ref"] == none

/-- How a machine state with no step left ended. -/
def endResult (m : Machine.MState) : Result :=
  match m.ending with
  | .returned vs => .returned vs
  | .trapped => .trapped
  | .thrown a => .thrown a
  | .stuck => .stuck

/-- Machine steps; the reached store survives every outcome. -/
def runMachine (fuel : Nat) (m : Machine.MState) : Machine.MState × Result :=
  match m.run fuel with
  | (m', true) => (m', .exhausted)
  | (m', false) => (m', endResult m')

/-- How a reference configuration's final sequence ended: values, `trap`, an uncaught exception
(`[ref.exn a, throw_ref]`), else stuck. -/
def refEnding : List AInstr → Result
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
    | .final => (c, refEnding c.instrs)
    | _ => (c, match refEnding c.instrs with
      | .thrown a => .thrown a
      | _ => .stuck)

/-- Whether a script literal fits parameter type `t` (upstream `runner.ml:411–416`:
`Match.match_valtype` on the literal's type): a number at its own type; an abstract reference
literal at a reference type of that heap type, a null one only where `t` is nullable. The
corpus' action arguments are numbers, `externref` values + nulls and `funcref` nulls. -/
def litFits (j : Json) (t : ValType) : Bool :=
  let ty := (j.getObjValAs? String "type").toOption.getD ""
  let null := (j.getObjValAs? String "value").toOption == some "null"
  match t with
  | .num .i32 => ty == "i32" | .num .i64 => ty == "i64"
  | .num .f32 => ty == "f32" | .num .f64 => ty == "f64"
  | .ref ⟨nullable, .abs a⟩ =>
    (nullable || !null) && match a with
      | .func => ty == "funcref" | .extern => ty == "externref" | .exn => ty == "exnref"
  | .ref _ => false

/-- Execute an invocation or read an exported global on the engine; traps and uncaught
exceptions retain their preceding effects. The arguments must match the export's parameter
types in number and type (upstream: `wrong number of arguments`, `wrong type of argument`). -/
def action (engine : Engine) (fuel : Nat) (s : State) (j : Json) :
    Except String (State × Result) := do
  let inst ← match s.moduleAt j with
    | .ok inst => pure inst
    | .error (some l) => return (s, .skipped s!"rejected module: line {l}")
    | .error none => throw "no such module"
  let ty ← j.getObjValAs? String "type"
  let field ← j.getObjValAs? String "field"
  let some ev := exported inst field | throw s!"missing export {field}"
  match ty, ev with
  | "get", .global a =>
    let some g := s.store.base.globals[a]? | throw s!"missing global address {a}"
    return (s, .returned [g.value])
  | "invoke", .func a =>
    let args ← j.getObjValAs? (Array Json) "args"
    let some ft := s.store.base.funcs[a]?.bind (·.type.expand)
      | throw s!"missing function address {a}"
    if args.size != ft.params.length then throw "wrong number of arguments"
    unless (args.toList.zip ft.params).all fun (j, t) => litFits j t do
      throw "wrong type of argument"
    let argVals ← args.toList.mapM (parseValue inst)
    let some vs := argVals.mapM id | return (s, .skipped "unsupported action argument")
    match engine with
    | .machine =>
      let (m', result) := runMachine fuel (Machine.MState.ofInvoke s.store a vs)
      return ({ s with store := m'.store }, result)
    | .ref =>
      let (c, result) := runRef fuel (invokeConfig s.store.abs a vs)
      return ({ s with store := Machine.MStore.ofStore c.store }, result)
  | _, _ => throw s!"unsupported action/export {ty} {field}"

/-- A diagnostic outcome, separate from the expected result. -/
def Result.describe : Result → String
  | .returned vs => "returned [" ++ String.intercalate ", " (vs.map showValue) ++ "]"
  | .trapped => "trap" | .thrown a => s!"exception exn:@{a}" | .exhausted => "fuel exhausted"
  | .stuck => "stuck"
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
def checkAction (engine : Engine) (fuel : Nat) (s : State) (ty : String) (c : Json) :
    State × Except String (Option String) := Id.run do
  let .ok j := c.getObjVal? "action" | return (s, .error "missing action")
  let (s', r) ← match action engine fuel s j with
    | .ok sr => pure sr
    | .error why => return (s, .error s!"action {j.compress}: {why}")
  if let .skipped why := r then return (s', .ok (some why))
  let expected := (c.getObjVal? "expected").toOption.getD .null
  let label := s!"{j.compress}: expected {ty} {expected.compress}, actual {r.describe}"
  match ty, r with
  | "assert_trap", .trapped | "assert_exhaustion", .exhausted | "assert_exception", .thrown _
  | "action", .returned _ => return (s', .ok none)
  | "assert_return", .returned vs =>
    let .ok es := c.getObjValAs? (Array Json) "expected" | return (s', .error label)
    let .ok inst := s.moduleAt j | return (s', .error label)
    let checks := (vs.zip es.toList).mapM fun (v, e) => meets inst v e
    match checks with
    | .ok bs => return (s', if vs.length == es.size && bs.all id then .ok none else .error label)
    | .error why => return (s', .ok (some why))
  | _, _ => return (s', .error label)

/-- Allocation + initialization on the engine (§4.5.4, U28e I2): U28c's shared candidates
(`Ref.initCandidates` + the final-allocation recheck `Ref.initAgrees`), then the
initialization code; the reached store (it survives a trap or an uncaught exception), the
instance and the ending; `none` = an initializer failed. -/
def initRun (engine : Engine) (fuel : Nat) (s : Machine.MStore) (m : FVA.Wasm.Module)
    (imports : List ExternVal) : Option (Machine.MStore × ModuleInst × Result) := do
  match engine with
  | .machine =>
    let (m', exhausted) ← Machine.initRun fuel s m imports
    pure (m'.store, m'.frame.inst, if exhausted then .exhausted else endResult m')
  | .ref =>
    let (gvals, trefs, erefs) ← Ref.initCandidates fuel s.abs m imports
    guard (Ref.initAgrees fuel s.abs m imports gvals trefs erefs)
    let (s₁, inst) := allocModule s.abs m imports gvals trefs erefs
    let (c, r) := runRef fuel ⟨s₁, ⟨[], inst⟩, (initCode m).map .plain⟩
    pure (Machine.MStore.ofStore c.store, inst, r)

/-- Unsupported payloads differ from malformed inputs that never reach validation. -/
inductive ModuleIssue where
  | outside (why : String)
  | malformed (why : String)

/-- The P′ in-profile test (U28a's boundary): oracle validation under the support manifest's
features, FVA's syntax classifier over `wasm-tools print` (independent of the decoder) and at
most one memory; `some why` = outside P′. A tool failure is a setup error, never an exclusion. -/
def outsideProfile (path : System.FilePath) : IO (Option String) := do
  let oracle ← IO.Process.output {
    cmd := "wasm-tools"
    args := #["validate", s!"--features={FVA.Profile.wasmToolsFeatures}", path.toString] }
  if oracle.exitCode == 1 then return some s!"oracle rejects: {oracle.stderr.trimAscii}"
  if oracle.exitCode != 0 then
    throw (IO.userError s!"profile oracle exited {oracle.exitCode}: {oracle.stderr.trimAscii}")
  let out ← IO.FS.withTempFile fun _ tmp => do
    let strip ← IO.Process.output
      { cmd := "wasm-tools", args := #["strip", "--all", path.toString, "-o", tmp.toString] }
    if strip.exitCode != 0 then
      throw (IO.userError s!"wasm-tools strip exited {strip.exitCode}: {strip.stderr.trimAscii}")
    IO.Process.output { cmd := "wasm-tools", args := #["print", tmp.toString] }
  if out.exitCode != 0 then
    throw (IO.userError s!"wasm-tools print exited {out.exitCode}: {out.stderr.trimAscii}")
  let top := FVA.Test.Profile.parse (FVA.Test.Profile.tokens out.stdout)
  match FVA.Test.Profile.classify top with
  | [] => return if FVA.Test.Profile.memoryCount top ≤ 1 then none else some "more than one memory"
  | cs => return some s!"excluded: {",".intercalate (cs.map FVA.Profile.Excluded.id)}"

/-- Positive payloads pass the P′ in-profile test before decoding; an in-profile payload the
decoder calls unsupported is an error. Negative cases check every decodable AST, including
invalid globals and combined memories; one outside the decoder's profile is excluded. -/
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
    if let some why ← outsideProfile path then return .error (.outside s!"outside P′: {why}")
  let bs ← IO.FS.readBinFile path
  return match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .error (.unsupported pos why) =>
      if negative then .error (.outside s!"outside P′: decoder offset {pos}: {why}")
      else .error (.malformed s!"in-profile payload unsupported at {pos}: {why}")
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

/-- A binary malformed payload must fail FVA's decoder: FVA's grammar is Wasm 3.0's restricted
to P′ (U28a), so a payload that decodes is a decoder fault; `unsupported` = outside the profile.
Text payloads test wasm-tools' parser and are skipped. -/
def checkMalformed (dir : System.FilePath) (c : Json) : IO (Except String (Option String)) := do
  if ((c.getObjValAs? String "module_type").toOption.getD "binary") != "binary" then
    return .ok (some "text format")
  let file ← IO.ofExcept (c.getObjValAs? String "filename")
  let bs ← IO.FS.readBinFile (dir / file)
  return match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .error (.malformed _ _) => .ok none
    | .error (.unsupported pos why) => .ok (some s!"outside: decoder offset {pos}: {why}")
    | .ok _ => .error "assert_malformed: module decodes"

/-- The outcome one command added to the tally: `pass`, `fail: why`, `skip: why`. -/
def outcome (before after : Tally) : String :=
  if after.pass > before.pass then "pass"
  else if after.fail > before.fail then s!"fail: {after.failures.back?.getD ""}"
  else if after.skip > before.skip then s!"skip: {after.skips.back?.getD ""}"
  else "none"

/-- Interpret one script on the engine with an action budget and a smaller stack-exhaustion
probe budget. `FVA_SPEC_OUTCOMES=<file>` appends one `line<TAB>type<TAB>outcome` row per
command. A dependent skip names the line of the `module` command FVA rejected or skipped. -/
def runScript (dir : System.FilePath) (json : Json) (fuel : Nat) (engine : Engine) :
    IO Tally := do
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
    if ty == "module" || ty == "assert_uninstantiable" then
      let mut inst : Option ModuleInst := none
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if let some m := module then
        match resolveImports s m with
        | .unavailable l => t := tally t line (.ok (some s!"unavailable import: line {l}"))
        | .unknown why => t := tally t line (.error s!"{ty}: {why}")
        | .linked imports =>
          if !Ref.importsMatch s.store.abs m imports then
            t := tally t line (.error s!"{ty}: imports do not match")
          else match initRun engine fuel s.store m imports, ty with
            -- upstream `runner.ml:559–566`: an uninstantiable module traps or throws
            | some (store, i, .returned []), "module" =>
              s := { s with store }
              inst := some i
              t := tally t line (.ok none)
            | some (store, _, .trapped), "assert_uninstantiable"
            | some (store, _, .thrown _), "assert_uninstantiable" =>
              s := { s with store }
              t := tally t line (.ok none)
            | some (store, _, r), _ =>
              s := { s with store }
              t := tally t line (.error s!"{ty}: initialization {r.describe}")
            | none, _ => t := tally t line (.error s!"{ty}: an initializer failed")
      if ty == "module" then
        s := { s with current := some (inst, line) }
        if let some name := (c.getObjValAs? String "name").toOption then
          s := { s with named := (name, (inst, line)) :: s.named }
    else if ty == "module_definition" then
      -- a definition validates without instantiating (memory.wast:8 defines a 4 GiB memory)
      let (t', module) ← validatePayload dir c "module" line t
      t := t'
      if module.isSome then t := tally t line (.ok none)
    else if ty == "assert_invalid" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if module.isSome then t := tally t line (.ok none)
    else if ty == "assert_unlinkable" then
      let (t', module) ← validatePayload dir c ty line t
      t := t'
      if let some m := module then
        t := tally t line <| match resolveImports s m with
          | .unavailable l => .ok (some s!"unavailable import: line {l}")
          | .unknown _ => .ok none
          | .linked imports =>
            if Ref.importsMatch s.store.abs m imports then .error "assert_unlinkable: module links"
            else .ok none
    else if ty == "assert_malformed" then
      t := { t with validation.malformed := t.validation.malformed + 1 }
      t := tally t line (← checkMalformed dir c)
    else if ty == "register" then
      let name ← IO.ofExcept (c.getObjValAs? String "as")
      let entry := match (c.getObjValAs? String "name").toOption with
        | some n => s.named.lookup n | none => s.current
      match entry with
      | some (inst, l) =>
        s := { s with registered := (name, (inst, l)) :: s.registered }
        t := tally t line
          (.ok (if inst.isSome then none else some s!"register rejected module: line {l}"))
      | none => t := tally t line (.error "register: no such module")
    else if ["action", "assert_return", "assert_trap", "assert_exhaustion",
        "assert_exception"].contains ty then
      let (s', r) := checkAction engine (if ty == "assert_exhaustion" then 1000 else fuel) s ty c
      s := s'
      t := tally t line r
    else t := tally t line (.error s!"unsupported command {ty}")
    if outcomes.isSome then log := log.push s!"{line}\t{ty}\t{outcome before t}"
  if let some path := outcomes then
    let h ← IO.FS.Handle.mk path .append
    for row in log do h.putStrLn row
  return t

end FVA.Test.Spec
