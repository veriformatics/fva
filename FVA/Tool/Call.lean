import FVA.Tool.Lift
import FVA.Impl.Exec.Det

/-!
# `fva call`: the claim + proof of one concrete call's result (D55)

Runs one call of an export on given arguments with FVA's verified reference stepper (the module
decoded from the bytes the lifted module names, allocated as a fresh instance) and writes two
modules: a spec module with the claim `Returns <module> "<export>" <args> <results>` and a proof
module whose proof runs the same stepper inside the kernel (`must_returned_of_runDet_get`). The
writer is untrusted: `fva trust` checks the proof, and the claim says what the reviewer reads.
Supported modules = those whose fresh instance is the allocated store (`instantiable_alloc`): no
imports, globals, element or data segments, start function; tables start null.
-/

namespace FVA.Tool.Call

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- One argument `<type>:<value>`: `i32`/`i64` decimal or `0x` hex (a leading `-` wraps),
`f32`/`f64` as `0x` bits (exact: no decimal float is rounded). -/
def parseArg (a : String) : Except String Val := do
  let [t, v] := a.splitOn ":" | throw s!"argument {a}: write <type>:<value>, for example i32:5"
  let neg := v.startsWith "-"
  let digits := if neg then (v.drop 1).toString else v
  unless ["i32", "i64", "f32", "f64"].contains t do throw s!"argument {a}: unknown type {t}"
  if (t == "f32" || t == "f64") && (neg || !digits.startsWith "0x") then
    throw s!"argument {a}: give a float as its bits in hex, for example f64:0x3fe0000000000000"
  let n ← match digits.startsWith "0x", (digits.drop 2).toString with
    | true, h =>
      if h.isEmpty then throw s!"argument {a}: no hex digits" else
      h.toList.foldlM (init := 0) fun acc c =>
        if c.isDigit then pure (acc * 16 + (c.toNat - 48))
        else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then pure (acc * 16 + (c.toLower.toNat - 87))
        else throw s!"argument {a}: {c} is no hex digit"
    | false, _ => match digits.toNat? with
      | some n => pure n
      | none => throw s!"argument {a}: {digits} is no number"
  let w := if t == "i32" || t == "f32" then 32 else 64
  if n ≥ 2 ^ w then throw s!"argument {a}: does not fit in {w} bits"
  let n := if neg then (2 ^ w - n) % 2 ^ w else n
  return match t with
    | "i32" => .i32 (BitVec.ofNat 32 n)
    | "i64" => .i64 (BitVec.ofNat 64 n)
    | "f32" => .f32 (BitVec.ofNat 32 n)
    | _ => .f64 (BitVec.ofNat 64 n)

/-- A value as Lean source (`.i32 0x…`, fixed width hex) and its type for the docstring. -/
def valSrc : Val → Option (String × String)
  | .i32 v => some (s!".i32 {hex v.toNat 8}", s!"i32 {v.toNat}")
  | .i64 v => some (s!".i64 {hex v.toNat 16}", s!"i64 {v.toNat}")
  | .f32 v => some (s!".f32 {hex v.toNat 8}", s!"f32 bits {hex v.toNat 8}")
  | .f64 v => some (s!".f64 {hex v.toNat 16}", s!"f64 bits {hex v.toNat 16}")
  | .ref _ => none
where
  hex (n w : Nat) : String :=
    let d := String.ofList (Nat.toDigits 16 n)
    "0x" ++ String.ofList (List.replicate (w - d.length) '0') ++ d

/-- The number type of a value (`fva call` arguments are numbers; a reference has none). -/
def Val.ty : Val → Option ValType
  | .i32 _ => some (.num .i32)
  | .i64 _ => some (.num .i64)
  | .f32 _ => some (.num .f32)
  | .f64 _ => some (.num .f64)
  | .ref _ => none

/-- The first part of `m` that makes its fresh instance more than the allocated store. -/
def unsupported (m : Module) : Option String :=
  if !m.imports.isEmpty then some "imports"
  else if !m.globals.isEmpty then some "globals"
  else if !m.elems.isEmpty then some "element segments"
  else if !m.datas.isEmpty then some "data segments"
  else if m.start.isSome then some "a start function"
  else if !m.nullTables then some "a table initializer other than ref.null"
  else none

/-- Steps until `c` is final (`runDet`'s order: trap, uniqueness, step), at most `cap`: the final
configuration and the step count. -/
def run (c : Config) (cap : Nat) : Except String (Config × Nat) := Id.run do
  let mut c := c
  for k in [0:cap] do
    if seqTraps c.instrs then return .ok (⟨c.store, c.frame, [.trap]⟩, k)
    unless uniqueStep false c do
      return .error "the call reaches a choice point (several successors)"
    match seq c.store c.frame [] c.instrs with
    | .step s f es => c := ⟨s, f, es⟩
    | .final => return .ok (c, k)
    | _ => return .error "the call gets stuck (the module does not validate for this call?)"
  return .error s!"the call takes more than {cap} steps"

/-- `path` (project-relative `.lean`) as a module name. -/
def modName (path : String) : String :=
  ".".intercalate (((path.dropEnd 5).toString.splitOn "/"))

/-- Words of `text` in lines of at most `w` columns after `first`, then after `next`. -/
def wrap (text first next : String) (w : Nat := 100) : String := Id.run do
  let mut lines : Array String := #[]
  let mut cur := first
  for word in text.splitOn " " do
    if cur.length + 1 + word.length > w && cur.length > first.length then
      lines := lines.push cur
      cur := next ++ word
    else cur := if cur == first then cur ++ word else cur ++ " " ++ word
  return "\n".intercalate (lines.push cur).toList

/-- A value list as Lean source: one line when it fits, else one value per line. -/
def listSrc (vs : List String) (indent : String) : String :=
  let one := "[" ++ ", ".intercalate vs ++ "]"
  if indent.length + one.length ≤ 100 then indent ++ one
  else indent ++ "[" ++ (",\n" ++ indent ++ " ").intercalate vs ++ "]"

/-- The spec module: the claim alone. -/
def specFile (ns liftedMod liftedNs name exp src : String) (args res : List (String × String)) :
    String :=
  let read (vs : List (String × String)) := ", ".intercalate (vs.map (·.2))
  s!"import {liftedMod}\nimport FVA.Spec.CAbi\n\n" ++
  wrap s!"Generated by `fva call`: one call of `{exp}` on the artifact `{src}`. -/" "/-! " "" ++
    "\n\n" ++
  s!"namespace {ns}\n\n" ++
  wrap s!"`{exp}` called on ({read args}) in a fresh instance returns ({read res}). -/" "/-- " "" ++
    "\n" ++
  s!"@[fva_claim] def {name} : Prop :=\n" ++
  s!"  FVA.Wasm.Exec.Returns {liftedNs}.module {exp.quote}\n" ++
  listSrc (args.map (·.1)) "    " ++ "\n" ++ listSrc (res.map (·.1)) "    " ++ "\n\n" ++
  s!"end {ns}\n"

/-- The proof module: the kernel runs the reference stepper for `fuel` steps. -/
def proofFile (ns specMod name : String) (addr fuel nargs : Nat) (res : List String) :
    String :=
  let typing := (List.replicate nargs ".cons ⟨⟩ (").foldr (· ++ ·) ".nil" ++
    String.ofList (List.replicate nargs ')')
  s!"import {specMod}\nimport FVA.Proof.Lib.Instance\n\n" ++
  "/-! Generated by `fva call`: the kernel runs FVA's reference stepper on the call. -/\n\n" ++
  s!"namespace {ns}\n\nopen FVA.Wasm FVA.Wasm.Exec\n\n" ++
  s!"set_option maxRecDepth 100000 in\ntheorem {name}_holds : {name} := by\n" ++
  "  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl rfl, ?_⟩\n" ++
  "  rintro H s inst hinst\n" ++
  "  obtain ⟨h1, h2⟩ := Prod.mk.inj (instance_alloc rfl rfl rfl rfl rfl hinst)\n" ++
  "  subst h1; subst h2\n" ++
  s!"  refine ⟨{addr}, by decide +kernel, ⟨_, _, rfl, rfl, {typing}⟩, ?_⟩\n" ++
  s!"  refine (must_returned_of_runDet_get (P := fun _ _ => True) " ++
    s!"(vs := [{", ".intercalate res}])\n" ++
  s!"    (n := {fuel}) (by decide +kernel) (by kernel_rfl) trivial).mono ?_\n" ++
  "  rintro (⟨s', vs⟩ | s' | ⟨s', a⟩) h\n" ++
  "  · exact h.1\n" ++
  "  all_goals exact h\n\n" ++
  s!"end {ns}\n"

/-- A `def <field> … := …` line's right-hand side in a lifted file. -/
def field (text key : String) : Option String :=
  (text.splitOn "\n").findSome? fun l =>
    if l.startsWith s!"def {key} : " then
      match l.splitOn " := " with
      | _ :: rest => some (" := ".intercalate rest)
      | [] => none
    else none

/-- `fva call <Lifted.lean> <export> [<type>:<value>]… --spec F --proof F [--name N] [--ns Ns]
[--max-steps K] [--force]`. -/
def main (argv : List String) : IO UInt32 := do
  let fail (msg : String) : IO UInt32 := do IO.eprintln s!"fva call: {msg}"; return 2
  let rec opts (o : Std.HashMap String String) (pos : Array String) :
      List String → Std.HashMap String String × Array String
    | "--force" :: r => opts (o.insert "force" "") pos r
    | k :: v :: r => if k.startsWith "--" then opts (o.insert (k.drop 2).toString v) pos r
      else opts o (pos.push k) (v :: r)
    | [k] => (o, pos.push k)
    | [] => (o, pos)
  let (o, pos) := opts {} #[] argv
  let some lifted := pos[0]? | fail "give the lifted module, the export and its arguments"
  let some exp := pos[1]? | fail "give the export to call"
  let (some spec, some proof) := (o.get? "spec", o.get? "proof")
    | fail "give --spec <file.lean> and --proof <file.lean>"
  for p in [lifted, spec, proof] do
    let f : System.FilePath := p
    if f.isAbsolute || f.components.contains ".." || !p.endsWith ".lean" then
      return ← fail s!"{p}: give a .lean path relative to the project root, without `..`"
  unless o.contains "force" do
    for p in [spec, proof] do
      if ← System.FilePath.pathExists p then
        return ← fail s!"{p} exists (use --force to replace it)"
  let text ← IO.FS.readFile lifted
  let some liftedNs := (text.splitOn "\n").findSome? fun l =>
      if l.startsWith "namespace " then some (l.drop 10).toString else none
    | fail s!"{lifted}: no namespace (not a module `fva lift` wrote)"
  let some src := (field text "source").bind fun s =>
      if s.startsWith "\"" && s.endsWith "\"" then some ((s.drop 1).dropEnd 1).toString else none
    | fail s!"{lifted}: no `source` (not a module `fva lift` wrote)"
  let bs ← try IO.FS.readBinFile src catch e => return ← fail s!"{src}: {e}"
  let .ok m := FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size
    | fail s!"{src} does not decode"
  -- the claim names the lifted module: it must be exactly what `fva lift` writes for these bytes
  unless text == FVA.Tool.Lift.file liftedNs bs m src do
    return ← fail s!"{lifted} is not `fva lift`'s output for {src} (run fva lift again)"
  if let some what := unsupported m then
    return ← fail (s!"the module has {what}; fva call supports modules without imports, " ++
      "globals, element or data segments, a start function, or a table initializer other " ++
      "than ref.null")
  let args ← match (pos.extract 2).toList.mapM parseArg with
    | .ok a => pure a
    | .error e => return ← fail e
  let (s, inst) := allocModule {} m [] [] (m.tables.map fun _ => .null) []
  let some addr := inst.exportFunc exp | fail s!"no exported function {exp}"
  let some (.wasm dt _ _) := s.funcs[addr]? | fail s!"{exp} is no module function"
  let some ft := dt.expand | fail s!"{exp} has no function type"
  unless ft.params.map some == args.map Val.ty do
    let ty : ValType → String
      | .num .i32 => "i32" | .num .i64 => "i64" | .num .f32 => "f32" | .num .f64 => "f64"
      | .ref _ => "a reference"
    return ← fail s!"{exp} takes ({", ".intercalate (ft.params.map ty)})"
  let cap := ((o.get? "max-steps").bind String.toNat?).getD 1000000
  let (fin, steps) ← match run (invokeConfig s addr args) cap with
    | .ok r => pure r
    | .error e => return (← do IO.eprintln s!"fva call: {e}"; pure 1)
  if seqTraps fin.instrs then
    IO.eprintln s!"fva call: the call traps (fva call states returning calls only)"; return 1
  let some res := fin.instrs.mapM toVal
    | do IO.eprintln "fva call: the final state holds no values"; return 1
  -- the proof's fuel: `runDet` spends one unit per step and one to see the final state
  unless (runDet (steps + 1) (invokeConfig s addr args)).isSome do
    IO.eprintln "fva call: internal error: runDet disagrees with the step count"; return 1
  let some argSrc := args.mapM valSrc | fail "reference arguments are not supported"
  let some resSrc := res.mapM valSrc | fail "the call returns a reference (not supported)"
  let liftedMod := modName lifted
  let parent := ".".intercalate (liftedNs.splitOn ".").dropLast
  let ns := (o.get? "ns").getD (if parent.isEmpty then "Calls" else parent)
  let name := (o.get? "name").getD s!"{exp}_call"
  for p in [spec, proof] do
    if let some d := (System.FilePath.mk p).parent then IO.FS.createDirAll d
  IO.FS.writeFile spec (specFile ns liftedMod liftedNs name exp src argSrc resSrc)
  IO.FS.writeFile proof
    (proofFile ns (modName spec) name addr (steps + 1) args.length (resSrc.map (·.1)))
  IO.println s!"{exp}({", ".intercalate (argSrc.map (·.2))}) returns ({", ".intercalate
    (resSrc.map (·.2))}) after {steps} steps; wrote {spec} (claim {ns}.{name}) and {proof}"
  return 0

end FVA.Tool.Call
