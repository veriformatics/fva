import Lean
import FVA.Tool.Codex
import FVA.Tool.Trust
import FVA.Trust.Collect
import FVA.Tool.Sandbox

/-!
# `fva explain` (advisory review aid; the verdict stays with `fva trust`)

The spec in plain English for a reader who cannot read Lean, by Claimcheck's two-pass round trip
(https://github.com/metareflection/claimcheck), reimplemented: pass 1 explains each claim from
the comment-stripped spec source plus its elaborated statement (it never sees the author's
intent, nor the author's names), pass 2 compares that explanation with the intent (the
requirements file, else the docstring, else the name). Example inputs
come from pass 1 plus fixed `0`, `1` per argument; their outputs never come from the model: the
spec value is the claim's `Returns` result reduced by Lean and confirmed by its kernel, the
binary value is wasmtime's.

The text is saved beside the spec module (`fva-explain.json`) and shown again without a model
call; `--force` regenerates it. Its `inputsSha` covers everything the text derives from, so a
change shows a STALE banner (rc 1). The proof status comes from a fresh `fva trust` every run.
-/

namespace FVA.Tool.Explain

open Lean

/-- File name of the saved explanation, beside the spec module's source. -/
def savedName : String := "fva-explain.json"

/-- Inputs every claim gets per argument, whatever the model proposes. -/
def fixedInputs : List Nat := [0, 1]

/-- Example rows per claim. -/
def maxExamples : Nat := 8

/-- Seconds for one spec-value case: a backstop for a process that dies or hangs, since each case's
budget is enforced inside Lean (`FVA.Explain.caseHeartbeats`, D17). -/
def caseSeconds : Nat := 10

private def obj (fs : List (String × Json)) : Json := Json.mkObj fs
private def str : Json := obj [("type", "string")]
private def strs : Json := obj [("type", "array"), ("items", str)]
private def strict (req : List String) (props : List (String × Json)) : Json :=
  obj [("type", "object"), ("additionalProperties", false),
    ("required", Json.arr (req.map toJson).toArray), ("properties", obj props)]

/-- Pass 1 reply schema. -/
def explainSchema : Json :=
  strict ["claims"] [("claims", obj [("type", "array"), ("items",
    strict ["name", "summary", "details", "caveats", "examples"]
      [("name", str), ("summary", str), ("details", strs), ("caveats", strs),
       ("examples", obj [("type", "array"), ("items",
         obj [("type", "array"), ("items", obj [("type", "integer")])])])])])]

/-- Pass 2 reply schema (reason before verdict: the reply is generated in this order). -/
def compareSchema : Json :=
  strict ["claims"] [("claims", obj [("type", "array"), ("items",
    strict ["name", "reason", "verdict"]
      [("name", str), ("reason", str),
       ("verdict", obj [("enum", Json.arr #["matches", "weaker", "stronger", "different",
         "vacuous"])])])])]

/-- Pass 1 prompt. -/
def explainPrompt (statements spec vocabulary : String) : String :=
  "You explain a formal specification to a reader who cannot read Lean 4. The specification
makes claims about functions exported by a compiled WebAssembly binary. `Returns m \"f\" args res`
means: the module m can be instantiated, and calling its exported function f with args, in a
fresh instance and under every host behavior, terminates without a trap and returns exactly res
(definitions below). `ReturnsAfterWrite m p bytes \"f\" args res` is the same after the caller
wrote bytes at address p of the instance's memory, whenever they fit. Lean core names (BitVec,
Nat.gcd, List.sum, …) have their standard Lean 4 meaning.

For each claim in the list, return:
- summary: one sentence in plain English, no Lean notation, that states what the claim guarantees.
- details: short sentences. Name the inputs the claim covers, bit widths, whether a value is read
  as signed or unsigned, wraparound, and what `Returns` adds (termination, no trap).
- caveats: what a reader could misread, what the claim leaves out, or why it may be weaker than
  it looks (vacuous, too narrow, trivially true). Empty when there is nothing.
  Keep example values out of summary, details and caveats; they go in examples alone.
- examples (required for every claim whose leading variables are integers): 3 to 6 lists of
  values for those variables, inputs only (leave out a variable that names a function's result),
  that show the behavior, boundary cases included. Integers; negative values are allowed where
  the claim reads a value as signed. Keep values small where the result needs a loop or
  recursion over the input.

The elaborated statement of each claim = what Lean checks, after every macro and notation the
specification imports has run. It is the truth: where it differs from the source text, explain
the elaborated statement and name the difference in caveats.

=== Elaborated claims ===
" ++ statements ++ "
=== Specification source (comments removed) ===
" ++ spec ++ "
=== FVA claim vocabulary (trusted definitions the claims use) ===
" ++ vocabulary

/-- Pass 2 prompt. -/
def comparePrompt (items : String) : String :=
  "Check whether formal claims mean what their authors intended. For each claim you get the
author's stated intent, the formal statement as Lean elaborates it, and an independent
plain-English explanation of that statement, written without seeing the intent, plus
input → output examples that Lean computed from the statement. The formal statement decides:
where the explanation misreads it, follow the statement (for example, a premise that can never
hold makes the claim vacuous). Compare the guarantee, not the wording. Every `Returns` claim
includes termination without a trap; that alone never makes a claim stronger than its intent.
Verdict:
- matches: the claim guarantees what the intent says.
- weaker: the claim guarantees part of what the intent says and nothing contrary to it
  (narrower inputs, missing cases, a looser result).
- stronger: the claim guarantees more than the intent says.
- different: for some input the claim guarantees a result the intent rules out, or it
  guarantees something else.
- vacuous: the claim is trivially true or says nothing about the function.
reason: one or two plain-English sentences a non-expert can follow; cite an example if one shows
the gap.

" ++ items

/-- Pass 2 reply schema with a requirements file (D5): one verdict per requirement. -/
def reqSchema : Json :=
  strict ["requirements"] [("requirements", obj [("type", "array"), ("items",
    strict ["id", "claims", "reason", "verdict"]
      [("id", str), ("claims", strs), ("reason", str),
       ("verdict", obj [("enum", Json.arr #["matches", "weaker", "stronger", "different",
         "vacuous", "missing"])])])])]

/-- Pass 2 prompt with a requirements file (D5): the claims under neutral names, so neither the
author's names nor docstrings reach the comparison. -/
def reqPrompt (context reqs items : String) : String :=
  "Check whether formal claims meet the requirements a user wrote for their software. Someone
else wrote the claims. For each claim you get the formal statement as Lean elaborates it, an
independent plain-English explanation of that statement, and input → output examples that Lean
computed from the statement. Names in the claims were replaced by neutral ones (claim_1,
name_1, …). The formal statement decides: where the explanation misreads it, follow the
statement (for example, a premise that can never hold makes the claim vacuous). Every `Returns`
claim includes termination without a trap; that alone never makes a claim stronger than a
requirement.

For each requirement, list the claims that state it (often one), then judge what those claims
guarantee together:
- matches: they guarantee what the requirement says.
- weaker: they guarantee part of what the requirement says and nothing contrary to it
  (narrower inputs, missing cases, a looser result).
- stronger: they guarantee more than the requirement says.
- different: for some input they guarantee a result the requirement rules out, or they
  guarantee something else.
- vacuous: they are trivially true or say nothing about the function.
- missing: no claim states the requirement.
reason: one or two plain-English sentences a non-expert can follow; cite an example if one shows
the gap.

=== Context from the requirements file ===
" ++ context ++ "
=== Requirements ===
" ++ reqs ++ "
=== Claims ===
" ++ items

/-- A requirement of the requirements file (D5). -/
structure Req where
  id : String
  text : String
deriving BEq, Repr

/-- Requirements file: each `## <id>` line starts a requirement, whose text runs to the next
one; the text before the first = context for every requirement. -/
def parseReqs (src : String) : String × List Req := Id.run do
  let mut pre := #[]
  let mut reqs : Array Req := #[]
  for l in src.splitOn "\n" do
    if l.startsWith "## " then
      reqs := reqs.push { id := (l.drop 3).trimAscii.toString, text := "" }
    else if reqs.isEmpty then pre := pre.push l
    else reqs := reqs.modify (reqs.size - 1) fun r => { r with text := r.text ++ l ++ "\n" }
  return (("\n".intercalate pre.toList).trimAscii.toString,
    reqs.toList.map fun r => { r with text := r.text.trimAscii.toString })

/-- Neutral names for the model (D5): names carry their author's intent, so pass 1 (and pass 2
with a requirements file) never sees what the author called a claim or a review-module
definition. -/
structure Renamer where
  /-- Last name component → neutral name (`claim_k` for claims, `name_k` otherwise). -/
  map : Std.HashMap String String := {}
  /-- Each project name's component-aligned suffixes (`c`, `B.c`, `A.B.c`): the identifiers
  that refer to it. -/
  refs : Std.HashSet String := {}

/-- The renamer for `claims` (numbered in this order) and the other `declared` names. -/
def Renamer.of (claims declared : List Name) : Renamer := Id.run do
  let mut r : Renamer := {}
  for (n, claim) in claims.map (·, true) ++ declared.map (·, false) do
    if let .str _ s := n then
      unless r.map.contains s do
        let k := r.map.size + 1
        r := { r with map := r.map.insert s (if claim then s!"claim_{k}" else s!"name_{k}") }
    let cs := n.components.map toString
    for j in List.range cs.length do
      r := { r with refs := r.refs.insert (".".intercalate (cs.drop j)) }
  return r

/-- `src` with every identifier that names a project constant renamed (its last component);
string literals, `«…»` names and projections (`x.f`: after a `.`) stay as written. -/
def Renamer.apply (r : Renamer) (src : String) : String := Id.run do
  let cs := src.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' || c == '«' then
      let close := if c == '"' then '"' else '»'
      out := out.push c; i := i + 1
      while i < cs.size && cs[i]! != close do
        if c == '"' && cs[i]! == '\\' && i + 1 < cs.size then out := out.push cs[i]!; i := i + 1
        out := out.push cs[i]!; i := i + 1
      if i < cs.size then out := out.push cs[i]!; i := i + 1
    else if Lean.isIdFirst c && !(i > 0 && (Lean.isIdRest cs[i - 1]! || cs[i - 1]! == '.')) then
      let mut j := i
      let mut more := true
      while more do
        while j < cs.size && Lean.isIdRest cs[j]! do j := j + 1
        if j + 1 < cs.size && cs[j]! == '.' && Lean.isIdFirst cs[j + 1]! then j := j + 1
        else more := false
      let tok := String.ofList (cs.extract i j).toList
      let parts := tok.splitOn "."
      out := out ++ match r.refs.contains tok, r.map.get? (parts.getLastD tok) with
        | true, some nn => ".".intercalate (parts.dropLast ++ [nn])
        | _, _ => tok
      i := j
    else out := out.push c; i := i + 1
  return out

/-- Model text with the neutral names back to the author's (last components). -/
def Renamer.restore (r : Renamer) (text : String) : String := Id.run do
  let back : Std.HashMap String String := r.map.fold (fun m k v => m.insert v k) {}
  let word (c : Char) := c.isAlphanum || c == '_'
  let cs := text.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if word cs[i]! then
      let mut j := i
      while j < cs.size && word cs[j]! do j := j + 1
      let w := String.ofList (cs.extract i j).toList
      out := out ++ (back.get? w).getD w
      i := j
    else out := out.push cs[i]!; i := i + 1
  return out

/-- Parsed options. -/
structure Opts where
  dir : String := ""
  spec : Option String := none
  root : Option String := none
  /-- Requirements file (D5); default `requirements.md` beside the spec module. -/
  reqs : Option String := none
  model : String := Codex.defaultModel
  effort : String := "medium"
  force : Bool := false
  json : Bool := false

/-- Parse options (`dir` first). -/
def parse (o : Opts) : List String → Except String Opts
  | [] => if o.dir.isEmpty then .error "no project directory given"
    else if o.spec.isNone then .error "--spec-module is required" else .ok o
  | "--spec-module" :: m :: r => parse { o with spec := some m } r
  | "--root-module" :: m :: r => parse { o with root := some m } r
  | "--requirements" :: f :: r => parse { o with reqs := some f } r
  | "--model" :: m :: r => parse { o with model := m } r
  | "--effort" :: e :: r => parse { o with effort := e } r
  | "--force" :: r => parse { o with force := true } r
  | "--json" :: r => parse { o with json := true } r
  | a :: r =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if o.dir.isEmpty then parse { o with dir := a } r
    else .error s!"unexpected argument {a}"

/-- The source path of module `m`, relative to its package root. -/
def modPath (m : String) : System.FilePath :=
  ("/".intercalate (m.splitOn ".") : System.FilePath).addExtension "lean"

/-- The source file of module `m` in the project at `root`. -/
def modFile (root : System.FilePath) (m : String) : System.FilePath :=
  root / modPath m

/-- Run `cmd` (stdout captured) under `timeout`; `none` = killed at the deadline. -/
def runTimed (cmd : String) (args : Array String) (cwd : System.FilePath) (secs : Nat) :
    IO (Option IO.Process.Output) := do
  let o ← IO.Process.output
    { cmd := "timeout", args := #["-s", "KILL", toString secs, cmd] ++ args, cwd }
  return if o.exitCode == 137 then none else some o

/-- `#eval` `cmd` (writing JSON lines to the file it is given) in a file importing the spec
module, under `lake env lean` in the project's sandbox (`FVA.Tool.Sandbox`: the spec's
definitions are project code), the temp dir alone writable; the lines written + whether Lean
finished. -/
def evalLean (root : System.FilePath) (spec : String) (cmd : System.FilePath → String)
    (secs : Nat) : IO (Array Json × Bool) :=
  IO.FS.withTempDir fun tmp => do
    let out := tmp / "out.jsonl"
    IO.FS.writeFile out ""
    let src := tmp / "FvaExplain.lean"
    IO.FS.writeFile src s!"import {spec}\nimport FVA.Explain\n{cmd out}\n"
    let sysroot ← Sandbox.sysrootAt root
    -- the mode `fva trust` would choose (D19: reduced inside an agent sandbox)
    let mode := ((← Sandbox.choose root sysroot).toOption).getD .full
    let a ← Sandbox.spawnArgs root sysroot (sysroot / "bin" / "lake").toString
      #["env", "lean", src.toString] #[tmp] (mode := mode)
    let r ← runTimed a.cmd a.args root secs
    let lines := (← IO.FS.readFile out).splitOn "\n" |>.filter (!·.isEmpty)
    return (lines.toArray.filterMap fun l => (Json.parse l).toOption,
      r.any (·.exitCode == 0))

/-- One claim's shape, statement and docstring (`FVA.Explain.shapes`). -/
structure Shape where
  doc : Option String
  statement : String
  /-- `returns`, `implies` or `decide` (`FVA.Explain.shape`); `none` = no examples. -/
  kind : Option String
  fn : Option String
  params : Array (String × Nat)
  outputs : Array (String × Nat)

/-- Read every claim's `Shape`, and the names the review modules `mods` declare. -/
def shapes (root : System.FilePath) (spec : String) (claims : Array String)
    (mods : List String) : IO (Std.HashMap String Shape × List Name) := do
  let names := ", ".intercalate (claims.toList.map ("`" ++ ·))
  let ms := ", ".intercalate (mods.map ("`" ++ ·))
  let (rows, done) ← evalLean root spec
    (fun out => s!"#eval FVA.Explain.shapes [{names}] {repr out.toString}\n" ++
      s!"#eval FVA.Explain.declared [{ms}] {repr out.toString}") 300
  unless done do throw <| .userError "fva explain: reading the claims' statements failed"
  let declared := rows.toList.filterMap fun r =>
    (r.getObjValAs? String "declared").toOption.map String.toName
  let mut m := {}
  for r in rows do
    let some c := (r.getObjValAs? String "claim").toOption | continue
    let sh := r.getObjValD "shape"
    let binders (k : String) := ((sh.getObjValD k).getArr?.toOption.getD #[]).filterMap fun p =>
      match p.getObjValAs? String "name", p.getObjValAs? Nat "bits" with
      | .ok n, .ok b => some (n, b)
      | _, _ => none
    m := m.insert c { doc := (r.getObjValAs? String "doc").toOption,
                      statement := (r.getObjValAs? String "statement").toOption.getD "",
                      kind := (sh.getObjValAs? String "kind").toOption,
                      fn := (sh.getObjValAs? String "fn").toOption, params := binders "params",
                      outputs := binders "outputs" }
  return (m, declared)

/-- Spec value + kernel status per case (`FVA.Explain.run`: `confirmed`, `refused`, `cost`,
`stuck`; a killed or crashed evaluation = `cost`, no value). -/
partial def specValues (root : System.FilePath) (spec claim : String)
    (cases : List (List Nat)) : IO (List (Option (List (String × Nat)) × String)) := do
  if cases.isEmpty then return []
  let lit := "[" ++ ", ".intercalate (cases.map fun c => toString c) ++ "]"
  let (rows, _) ← evalLean root spec
    (fun out => s!"#eval FVA.Explain.run `{claim} {lit} {repr out.toString}")
    (caseSeconds + 5 * cases.length)
  let vals := rows.toList.map fun r =>
    let status := (r.getObjValAs? String "status").toOption.getD "stuck"
    let vs := ((r.getObjValD "res").getArr?.toOption.getD #[]).toList.filterMap fun v =>
      match v.getObjValAs? String "type", v.getObjValAs? Nat "value" with
      | .ok t, .ok x => some (t, x)
      | _, _ => none
    (if status == "confirmed" || status == "refused" then some vs else none, status)
  let got := vals.take cases.length
  if got.length == cases.length then return got
  -- the case after the last result was too costly: skip it, continue with the rest
  let rest ← specValues root spec claim (cases.drop (got.length + 1))
  return got ++ [(none, "cost")] ++ rest

/-- The condition's truth + kernel status per case (`FVA.Explain.decideCases`: every binder's
value; a killed or crashed evaluation = `cost`). -/
partial def decided (root : System.FilePath) (spec claim : String) (cases : List (List Nat)) :
    IO (List (Option Bool × String)) := do
  if cases.isEmpty then return []
  let lit := "[" ++ ", ".intercalate (cases.map fun c => toString c) ++ "]"
  let (rows, _) ← evalLean root spec
    (fun out => s!"#eval FVA.Explain.decideCases `{claim} {lit} {repr out.toString}")
    (caseSeconds + 5 * cases.length)
  let got := (rows.toList.map fun r => ((r.getObjValAs? Bool "holds").toOption,
    (r.getObjValAs? String "status").toOption.getD "stuck")).take cases.length
  if got.length == cases.length then return got
  let rest ← decided root spec claim (cases.drop (got.length + 1))
  return got ++ [(none, "cost")] ++ rest

/-- Bits of a result type name. -/
def typeBits : String → Nat
  | "i64" | "f64" => 64
  | _ => 32

/-- `x` mod 2^bits as a two's-complement signed integer. -/
def signed (x bits : Nat) : Int :=
  if x ≥ 2 ^ (bits - 1) then (x : Int) - 2 ^ bits else x

/-- The binary's results for `fn` on `args` (wasmtime; arguments in signed form, results read
back mod 2^bits), or `none` on a trap or a failed run. -/
def binaryValue (wasmtime : String) (wasm : System.FilePath) (fn : String)
    (args : List (Nat × Nat)) (resBits : List Nat) : IO (Option (List Nat)) := do
  let some o ← runTimed wasmtime (#["run", "--invoke", fn, wasm.toString] ++
      (args.map fun (a, b) => toString (signed a b)).toArray) "." caseSeconds
    | return none
  if o.exitCode != 0 then return none
  let outs := (o.stdout.splitOn "\n").filter (!·.trimAscii.isEmpty)
  let vals := outs.filterMap (·.trimAscii.toString.toInt?)
  if vals.length != resBits.length then return none
  return some (vals.zip resBits |>.map fun (v, b) => (v % (2 ^ b : Int)).toNat)

/-- The `.wasm` path a `Lifted.lean` names (`def source : String := "…"`). -/
def liftedSource (lifted : System.FilePath) : IO (Option String) := do
  for l in (← IO.FS.readFile lifted).splitOn "\n" do
    if l.startsWith "def source : String := \"" then
      return some (((l.drop "def source : String := \"".length).dropEnd 1).toString)
  return none

/-- One example row. -/
structure Example where
  args : List Nat
  spec : Option (List Nat)
  binary : Option (List Nat)
  /-- The spec value's (or the decided condition's) kernel status (`FVA.Explain`). -/
  status : String := "confirmed"
  /-- An `implies` or `decide` claim's condition on this case (D18). -/
  holds : Option Bool := none

/-- One explained claim. -/
structure Row where
  name : String
  intent : Option String
  statement : String
  summary : String
  details : List String
  caveats : List String
  /-- Example shape: `returns`, `implies` or `decide` (`FVA.Explain.shape`, D18). -/
  kind : String := "returns"
  fn : Option String := none
  params : List (String × Nat) := []
  resultBits : List Nat := []
  examples : List Example := []
  verdict : String := "unknown"
  reason : String := ""
  /-- Requirements this claim states (pass 2 with a requirements file). -/
  serves : List String := []

/-- One requirement's check (D5): the claims stating it + the verdict on them. -/
structure ReqRow where
  id : String
  text : String
  claims : List String
  verdict : String
  reason : String
deriving ToJson, FromJson

instance : ToJson Example where
  toJson e := Json.mkObj [("args", toJson e.args), ("spec", toJson e.spec),
    ("binary", toJson e.binary), ("status", toJson e.status), ("holds", toJson e.holds)]

instance : FromJson Example where
  fromJson? j := do
    let args ← j.getObjValAs? (List Nat) "args"
    let spec ← j.getObjValAs? (Option (List Nat)) "spec"
    let binary ← j.getObjValAs? (Option (List Nat)) "binary"
    return { args, spec, binary,
             status := (j.getObjValAs? String "status").toOption.getD "confirmed",
             holds := (j.getObjValAs? Bool "holds").toOption }

instance : ToJson Row where
  toJson r := Json.mkObj [("name", toJson r.name), ("intent", toJson r.intent),
    ("statement", toJson r.statement), ("summary", toJson r.summary),
    ("details", toJson r.details), ("caveats", toJson r.caveats), ("fn", toJson r.fn),
    ("params", toJson (r.params.map fun (n, b) => Json.mkObj [("name", toJson n),
      ("bits", toJson b)])),
    ("kind", toJson r.kind), ("resultBits", toJson r.resultBits),
    ("examples", toJson r.examples),
    ("verdict", toJson r.verdict), ("reason", toJson r.reason), ("serves", toJson r.serves)]

instance : FromJson Row where
  fromJson? j := do
    let ps ← j.getObjValAs? (List Json) "params"
    let params ← ps.mapM fun p => return ((← p.getObjValAs? String "name"),
      (← p.getObjValAs? Nat "bits"))
    let name ← j.getObjValAs? String "name"
    let statement ← j.getObjValAs? String "statement"
    let summary ← j.getObjValAs? String "summary"
    let details ← j.getObjValAs? (List String) "details"
    let caveats ← j.getObjValAs? (List String) "caveats"
    let resultBits ← j.getObjValAs? (List Nat) "resultBits"
    let examples ← j.getObjValAs? (List Example) "examples"
    let verdict ← j.getObjValAs? String "verdict"
    let reason ← j.getObjValAs? String "reason"
    return { name, intent := (j.getObjValAs? String "intent").toOption, statement, summary,
             details, caveats, fn := (j.getObjValAs? String "fn").toOption, params, resultBits,
             examples, verdict, reason,
             serves := (j.getObjValAs? (List String) "serves").toOption.getD [],
             kind := (j.getObjValAs? String "kind").toOption.getD "returns" }

/-- A claim's proof status from the trust report: issues naming the claim or its proofs, plus
the project-wide ones (no claim named). -/
def proofStatus (issues : List (String × String)) (every own : List String) :
    Bool × List String × List String :=
  let names (d : String) (ns : List String) := ns.any fun n => mentions d n
  let mine := issues.filter (fun (_, d) => names d own) |>.map (·.2)
  let shared := (issues.filter fun (_, d) => !names d every).map (·.1) |>.eraseDups
  (mine.isEmpty && shared.isEmpty, mine, shared)
where
  /-- `n` occurs in `d` as a whole name (not inside a longer dotted name). -/
  mentions (d n : String) : Bool :=
    let isName (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\''
    (d.splitOn n).length > 1 && Id.run do
      let parts := d.splitOn n
      let mut ok := false
      for k in List.range (parts.length - 1) do
        let before := (parts[k]!).back
        let after := (parts[k + 1]!).front
        if !(isName before && !(parts[k]!).isEmpty) && !(isName after && !(parts[k + 1]!).isEmpty)
        then ok := true
      return ok

/-- The saved text no longer describes the inputs: another `inputsSha`, or another claim set. -/
def isStale (savedSha : Option String) (sha : String) (saved current : List String) : Bool :=
  savedSha != some sha || saved.mergeSort (· ≤ ·) != current.mergeSort (· ≤ ·)

/-- A claim of the trust report: name, proof names, subject modules. -/
structure Claim where
  name : String
  proofs : List String
  subjects : List String

/-- The parts of `fva trust --json` explain reads. -/
structure Trust where
  verdict : String
  issues : List (String × String)
  claims : List Claim
  reviewModules : List String

/-- Parse `fva trust --json` output. -/
def Trust.ofJson (j : Json) : Except String Trust := do
  let pass := (j.getObjValD "verdict") == toJson FVA.Trust.Verdict.pass
  let verdict := if pass then "PASS" else "FAIL"
  let issues ← (← j.getObjValAs? (List Json) "issues").mapM fun i =>
    return ((← i.getObjValAs? String "tag"), (← i.getObjValAs? String "detail"))
  let r := j.getObjValD "report"
  let claims ← (← r.getObjValAs? (List Json) "claims").mapM fun c => do
    let proofs ← (← c.getObjValAs? (List Json) "proofs").mapM (·.getObjValAs? String "name")
    return { name := ← c.getObjValAs? String "name", proofs,
             subjects := ← c.getObjValAs? (List String) "subjects" }
  let mods ← (← r.getObjValAs? (List Json) "reviewModules").mapM (·.getObjValAs? String "module")
  return { verdict, issues, claims, reviewModules := mods }

/-- The FVA files (paths inside the FVA package) whose text the prompt carries (claim
vocabulary) or the examples rest on. -/
def fvaFiles : List System.FilePath :=
  ["FVA/Spec/CAbi.lean", "FVA/Spec/Claims.lean", "FVA/Explain.lean"]

/-- sha256 of every input the saved text derives from: model, effort, prompts, schemas, the
requirements file, the review-surface files, the lifted modules (their numerals are the `.wasm`
bytes), FVA's files. Each file enters by its path inside the project or the FVA package, so a
checkout elsewhere (a pool host, CI) finds the same text current. -/
def inputsSha (o : Opts) (root fva : System.FilePath) (t : Trust) (reqs : Option String) :
    IO String :=
  IO.FS.withTempDir fun tmp => do
    let own := (t.reviewModules.map modPath ++
      (t.claims.flatMap (·.subjects)).eraseDups.map modPath).mergeSort
      (·.toString ≤ ·.toString)
    let files := own.map (root, ·) ++ fvaFiles.map (fva, ·)
    let mut payload := toString (toJson [o.model, o.effort, explainPrompt "" "" "",
      comparePrompt "", reqPrompt "" "" "", explainSchema.compress, compareSchema.compress,
      reqSchema.compress, toString fixedInputs, toString maxExamples])
    payload := payload ++ "\x00requirements\x00" ++ reqs.getD "(none)"
    for (dir, f) in files do
      payload := payload ++ "\x00" ++ f.toString ++ "\x00" ++
        (← try IO.FS.readFile (dir / f) catch _ => pure "(missing)")
    IO.FS.writeFile (tmp / "in") payload
    let r ← IO.Process.output { cmd := "sha256sum", args := #[(tmp / "in").toString] }
    return (r.stdout.splitOn " ").headD ""

/-- `Codex.ask`, and with `FVA_EXPLAIN_DUMP=<dir>` set, the exact prompt + schema and the reply
saved there as `<tag>.prompt.txt`, `<tag>.schema.json`, `<tag>.reply.json` (a measurement can
replay the same bytes on another model). -/
def ask (tag prompt : String) (schema : Json) (o : Opts) : IO Json := do
  let dump := (← IO.getEnv "FVA_EXPLAIN_DUMP").map System.FilePath.mk
  if let some d := dump then
    IO.FS.createDirAll d
    IO.FS.writeFile (d / s!"{tag}.prompt.txt") prompt
    IO.FS.writeFile (d / s!"{tag}.schema.json") schema.compress
  let r ← Codex.ask prompt schema o.model o.effort
  if let some d := dump then IO.FS.writeFile (d / s!"{tag}.reply.json") r.compress
  return r

/-- Pass 1, examples, pass 2: against each claim's docstring, or with a requirements file
(`reqs` = its context + requirements) against the requirements. -/
def generate (o : Opts) (root fva : System.FilePath) (t : Trust)
    (reqs : Option (String × List Req)) : IO (List Row × List ReqRow) := do
  let spec := o.spec.getD ""
  let names := t.claims.map (·.name)
  let (sh, declared) ← shapes root spec names.toArray t.reviewModules
  let rn := Renamer.of (names.map String.toName) declared
  let env ← mkEmptyEnvironment
  let specText ← t.reviewModules.foldlM (init := "") fun acc m => do
    let src ← try IO.FS.readFile (modFile root m) catch _ => pure ""
    return acc ++ s!"--- {m}\n{rn.apply (FVA.Trust.stripComments env src)}\n"
  let vocab ← fvaFiles.take 2 |>.foldlM (init := "") fun acc f => do
    return acc ++ s!"--- {f.fileName.getD ""}\n{← IO.FS.readFile (fva / f)}\n"
  let statements := "\n".intercalate (names.filterMap fun n =>
    (sh.get? n).map fun s => s!"{rn.apply n} : Prop := {rn.apply s.statement}")
  let p1 ← ask "pass1" (explainPrompt statements specText vocab) explainSchema o
  let p1rows := (p1.getObjValD "claims").getArr?.toOption.getD #[]
  -- a reply names a claim by its full or its last component (neutral in pass 1)
  let named (x n : String) := x == n || x == (n.splitOn ".").getLastD n
  let find (rows : Array Json) (key : String) (n : String) : Json :=
    (rows.find? fun r => named ((r.getObjValAs? String key).toOption.getD "") n).getD Json.null
  let wasmtime :=
    let p := fva / ".tools/bin/wasmtime"
    p.toString
  -- rows keep pass 1's neutral text until pass 2 has read it
  let mut rows := #[]
  for c in t.claims do
    let e := find p1rows "name" (rn.apply c.name)
    let strsOf (k : String) := (e.getObjValAs? (List String) k).toOption.getD []
    let s := sh.get? c.name
    let mut row : Row :=
      { name := c.name, intent := s.bind (·.doc), statement := (s.map (·.statement)).getD "",
        summary := (e.getObjValAs? String "summary").toOption.getD "",
        details := strsOf "details", caveats := strsOf "caveats" }
    if let some s := s then
      let bits := s.params.toList.map (·.2)
      let proposed := ((e.getObjValAs? (List (List Int)) "examples").toOption.getD []) ++
        fixedInputs.map fun v => List.replicate bits.length (Int.ofNat v)
      let cases := (proposed.filter (·.length == bits.length)).map fun xs =>
        (xs.zip bits).map fun (a, b) => (a % (2 ^ b : Int)).toNat
      let cases := (cases.eraseDups).take maxExamples
      let wasm ← match c.subjects with
        | [subj] => pure ((← liftedSource (modFile root subj)).map (root / ·))
        | _ => pure none
      match s.kind, s.fn, wasm with
      | some "returns", some fn, some wasm =>
        let specV ← specValues root spec c.name cases
        let resBits := ((specV.findSome? (·.1)).getD []).map (typeBits ·.1)
        let mut exs := #[]
        for (a, v, status) in cases.zip specV do
          let b ← binaryValue wasmtime wasm fn (a.zip bits) resBits
          exs := exs.push { args := a, spec := v.map (·.map (·.2)), binary := b, status }
        row := { row with fn := some fn, params := s.params.toList, resultBits := resBits,
                          examples := exs.toList }
      | some "implies", some fn, some wasm =>
        -- the binary's results stand in for the output variables, then the condition is decided
        let outBits := s.outputs.toList.map (·.2)
        let mut bins := #[]
        for a in cases do bins := bins.push (← binaryValue wasmtime wasm fn (a.zip bits) outBits)
        let mut ds ← decided root spec c.name
          ((cases.zip bins.toList).filterMap fun (a, b) => b.map (a ++ ·))
        let mut exs := #[]
        for (a, b) in cases.zip bins.toList do
          match b, ds with
          | some bv, (h, status) :: rest =>
            exs := exs.push { args := a, spec := none, binary := some bv, status, holds := h }
            ds := rest
          | _, _ => exs := exs.push { args := a, spec := none, binary := none, status := "trap" }
        row := { row with kind := "implies", fn := some fn, params := s.params.toList,
                          resultBits := outBits, examples := exs.toList }
      | some "decide", _, _ =>
        let ds ← decided root spec c.name cases
        let exs : List Example := (cases.zip ds).map fun (a, h, status) =>
          { args := a, spec := none, binary := none, status, holds := h }
        row := { row with kind := "decide", params := s.params.toList, examples := exs }
      | _, _, _ => pure ()
    rows := rows.push row
  let item (r : Row) (name statement : String) (head : String) :=
    let exs := r.examples.filterMap fun x => if x.status != "confirmed" then none else
      let call := s!"{r.fn.getD ""}({", ".intercalate (x.args.map toString)})"
      match r.kind, x.spec, x.binary, x.holds with
      | "returns", some v, _, _ => some s!"Example: {call} → spec says {v}\n"
      | "implies", _, some b, some h =>
        some s!"Example: {call} → the binary returns {b}; the claim's condition is {h}\n"
      | "decide", _, _, some h =>
        let vs := ", ".intercalate ((r.params.zip x.args).map fun ((n, _), a) => s!"{n} = {a}")
        some s!"Example: {if vs.isEmpty then "Lean decides" else vs} → the statement is {h}\n"
      | _, _, _, _ => none
    s!"## {name}\n{head}Formal statement: {statement}\n" ++
      s!"Explanation: {r.summary} {" ".intercalate r.details}\n" ++ String.join exs
  let shown (r : Row) : Row :=
    { r with summary := rn.restore r.summary, details := r.details.map rn.restore,
             caveats := r.caveats.map rn.restore }
  match reqs with
  | none =>
    let shownRows := rows.map shown
    let items := "\n\n".intercalate (shownRows.toList.map fun r =>
      let intent := r.intent.getD s!"none written; infer it from the name {r.name}"
      item r r.name r.statement s!"Intent: {intent}\n")
    let p2 ← ask "pass2" (comparePrompt items) compareSchema o
    let p2rows := (p2.getObjValD "claims").getArr?.toOption.getD #[]
    return (shownRows.toList.map fun r =>
      let v := find p2rows "name" r.name
      { r with verdict := (v.getObjValAs? String "verdict").toOption.getD "unknown",
               reason := (v.getObjValAs? String "reason").toOption.getD "no reply" }, [])
  | some (context, rs) =>
    let items := "\n\n".intercalate (rows.toList.map fun r =>
      item r (rn.apply r.name) (rn.apply r.statement) "")
    let reqText := "\n\n".intercalate (rs.map fun r => s!"## {r.id}\n{r.text}")
    let p2 ← ask "pass2" (reqPrompt context reqText items) reqSchema o
    let p2rows := (p2.getObjValD "requirements").getArr?.toOption.getD #[]
    let checks := rs.map fun q =>
      let v := (p2rows.find? fun j => (j.getObjValAs? String "id").toOption == some q.id).getD
        Json.null
      let said := (v.getObjValAs? (List String) "claims").toOption.getD []
      { id := q.id, text := q.text,
        claims := names.filter fun n => said.any (named · (rn.apply n)),
        verdict := (v.getObjValAs? String "verdict").toOption.getD "unknown",
        reason := rn.restore ((v.getObjValAs? String "reason").toOption.getD "no reply") :
        ReqRow }
    return (rows.toList.map fun r =>
      { shown r with verdict := "", serves := checks.filterMap fun q =>
          if q.claims.contains r.name then some q.id else none }, checks)

/-- Wrap `text` at 96 columns: the first line after `first`, the rest after `rest`. -/
def wrap (text first rest : String) : List String := Id.run do
  let mut lines := #[]
  let mut cur := first
  let mut empty := true
  for w in (text.splitOn " ").filter (!·.isEmpty) do
    if !empty && cur.length + 1 + w.length > 96 then
      lines := lines.push cur
      cur := rest ++ w
    else
      cur := if empty then cur ++ w else cur ++ " " ++ w
    empty := false
  return (lines.push cur).toList

/-- A value as unsigned, with its signed reading when that differs. -/
def num (v bits : Nat) : String :=
  if v ≥ 2 ^ (bits - 1) then s!"{v} (= {signed v bits} signed)" else toString v

/-- The plain report (human-facing). -/
def render (dir model trustVerdict : String) (saved : Option (String × Bool × Bool))
    (rows : List (Row × Bool × List String × List String))
    (reqs : Option (String × List ReqRow) := none) : String := Id.run do
  let clean := FVA.Tool.Trust.clean
  let mut out := #[s!"FVA explain — {clean dir}", "",
    s!"  Proof check (fva trust): {trustVerdict}" ++ (if trustVerdict == "PASS" then "" else
      " — the claims below are not all proven; run `fva trust` for the reasons"),
    s!"  The text below was written by {model} and can be wrong. It helps you read the spec;",
    "  it does not replace the proof check. The examples are computed, not written by the model."]
  if let some (generated, reused, stale) := saved then
    if stale then
      out := out ++ #["",
        s!"  STALE: the spec, the binary or the prompts changed after {generated}.",
        "  The text below describes the old version. Run again with --force to regenerate it."]
    else if reused then
      out := out ++ #["",
        s!"  Saved text from {generated} ({savedName}). The proof status is current.",
        "  Run again with --force to regenerate the text."]
    else
      out := out ++ #["",
        s!"  Saved to {savedName}. Later runs show this text; use --force to regenerate it."]
  let flat (t : String) := " ".intercalate (t.splitOn "\n" |>.map (·.trimAscii.toString))
  match reqs with
  | some (file, checks) =>
    out := out ++ #[""] ++ (wrap s!"({clean file}), each checked against the claims that state it"
      "Requirements " "  ").toArray
    for q in checks do
      let mark := if q.verdict == "matches" then "✓" else "✗"
      let by_ := if q.claims.isEmpty then "no claim" else ", ".intercalate (q.claims.map clean)
      out := out ++ (wrap s!"{q.verdict.toUpper} — {q.reason}" s!"  {mark} {clean q.id}: "
          "      ").toArray ++ (wrap (flat q.text) "      Requirement: " "        ").toArray ++
        (wrap by_ "      Stated by: " "        ").toArray
  | none =>
    out := out ++ #["",
      "  Each intent check compares a claim with its author's description. To check",
      "  the claims against your own requirements, write requirements.md beside the spec."]
  for (c, ok, mine, shared) in rows do
    let mark := if c.verdict == "matches" then "✓" else "✗"
    let proof := if ok then "✓ Proof: checked by fva trust" else
      "✗ Proof: not accepted — " ++ "; ".intercalate (mine.map clean ++
        (if shared.isEmpty then [] else [s!"project checks failed: {", ".intercalate shared}"]))
    out := out ++ #["", clean c.name] ++ (wrap proof "  " "    ").toArray ++
      (wrap c.summary "  In plain English: " "    ").toArray
    for d in c.details do out := out ++ (wrap d "    - " "      ").toArray
    unless c.caveats.isEmpty do
      out := out.push "  Watch for:"
      for d in c.caveats do out := out ++ (wrap d "    - " "      ").toArray
    if !c.examples.isEmpty then
      if c.kind == "returns" then
        out := out ++ #[
          "  Examples (spec value computed by Lean and checked by its kernel; binary value",
          "  from wasmtime):"]
      let widths := c.params.map (·.2)
      let nums (vs : List Nat) (bits : List Nat) := ", ".intercalate ((vs.zip bits).map
        fun (a, b) => num a b)
      let verdict (x : Example) : String := match x.holds, x.status with
        | some h, st => (if h then "holds" else "fails") ++
          (if st == "refused" then " (✗ the kernel does not accept this)" else "")
        | none, "stuck" => "cannot be decided"
        | none, _ => "too costly to decide"
      if c.kind == "implies" then
        out := out ++ #["  Examples (the binary's results from wasmtime; the claim's condition on",
          "  them decided by Lean and checked by its kernel):"]
        for x in c.examples do
          let call := s!"{c.fn.getD ""}({nums x.args widths})"
          let line := match x.binary with
            | none => s!"{call}: the binary traps (the claim says nothing for these inputs)"
            | some b => s!"{call} → {nums b c.resultBits}: the condition {verdict x}"
          out := out ++ (wrap line "    " "        ").toArray
      if c.kind == "decide" then
        out := out.push "  Examples (each case decided by Lean and checked by its kernel):"
        for x in c.examples do
          let vs := ", ".intercalate ((c.params.zip x.args).map fun ((n, b), a) =>
            s!"{n} = {num a b}")
          let line := if vs.isEmpty then s!"the statement {verdict x}"
            else s!"{vs}: the statement {verdict x}"
          out := out ++ (wrap line "    " "        ").toArray
      for x in c.examples.filter (fun _ => c.kind == "returns") do
        let call := s!"{c.fn.getD ""}({", ".intercalate ((x.args.zip widths).map fun (a, b) =>
          num a b)})"
        let sv := match x.spec, x.status with
          | none, "stuck" => "no value: Lean cannot reduce the result to numbers"
          | none, _ => "too costly to compute"
          | some v, st => ", ".intercalate ((v.zip c.resultBits).map fun (a, b) => num a b) ++
            (if st == "refused" then " (✗ the kernel does not accept this value)" else "")
        let agree := match x.spec, x.binary with
          | none, _ => ""
          | some v, some b => if v == b then "  binary agrees" else s!"  ✗ binary returns {b}"
          | some _, none => "  ✗ binary traps"
        out := out ++ (wrap s!"{call} → {sv}{agree}" "    " "        ").toArray
    else if c.fn.isNone && !c.statement.isEmpty then
      out := out ++ #["  Examples: none. FVA computes examples for claims over integer inputs of",
        "  the forms `Returns …`, `Returns … → condition` and a decidable condition. Lean reads",
        "  this claim as:"] ++
        (wrap (" ".intercalate (c.statement.splitOn "\n" |>.map (·.trimAscii.toString)))
          "    " "      ").toArray
    if reqs.isSome then
      let ids := if c.serves.isEmpty then "none" else ", ".intercalate (c.serves.map clean)
      out := out ++ (wrap ids "  Requirements it states: " "    ").toArray
    else
      let intent := c.intent.getD s!"(no description; inferred from the name {c.name})"
      out := out ++ (wrap (flat intent) "  Stated intent: " "    ").toArray ++
        (wrap s!"{c.verdict.toUpper} — {c.reason}" s!"  {mark} Intent check: " "    ").toArray
  return "\n".intercalate out.toList ++ "\n"

/-- `fva explain <lake-dir> --spec-module M [--root-module R] [--requirements F] [--model M]
[--effort E] [--force] [--json]`: rc 0 = trust PASS, text current, and every requirement (with a
requirements file) or else every intent check `matches`; 1 otherwise; 2 = usage. -/
def main (argv : List String) : IO UInt32 := do
  let o ← match parse {} argv with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"fva explain: {e}. Run \"fva explain --help\" to see the options."
      return 2
  let root ← try IO.FS.realPath o.dir catch e => IO.eprintln s!"fva explain: {e}"; return 2
  let fva ← FVA.Tool.Trust.fvaRoot
  let spec := o.spec.getD ""
  let self ← IO.appPath
  let tr ← IO.Process.output { cmd := self.toString, args := #["trust", root.toString,
    "--spec-module", spec, "--json"] ++ (o.root.map fun r => #["--root-module", r]).getD #[] }
  let t ← match (Json.parse tr.stdout).bind Trust.ofJson with
    | .ok t => pure t
    | .error _ =>
      IO.eprintln (s!"fva explain: fva trust gave no report (rc {tr.exitCode}):\n" ++
        ((tr.stdout ++ tr.stderr).takeEnd 1500).toString)
      return 2
  let specDir := (modFile root spec).parent.getD root
  let path := specDir / savedName
  -- D63: a project that does not build has no claims to explain; a saved text still shows
  if t.issues.any (·.1 == "build") && !(← path.pathExists) then
    if o.json then
      IO.println (Json.mkObj [("project", toJson root.toString),
        ("trustVerdict", toJson t.verdict), ("trustIssues", toJson (t.issues.map fun (k, d) =>
          Json.mkObj [("tag", toJson k), ("detail", toJson d)])), ("claims", Json.arr #[])]).pretty
    else
      IO.println (s!"FVA explain — {FVA.Tool.Trust.clean root.toString}\n\n" ++
        s!"  Proof check (fva trust): {t.verdict}\n" ++
        "  The project does not build, so there are no claims to explain.\n" ++
        "  To see the build errors, run `fva trust`.")
    return 1
  let reqPath : Option System.FilePath ← match o.reqs with
    | some f => pure (some f)
    | none => do
      let d := specDir / "requirements.md"
      pure (if ← d.pathExists then some d else none)
  let reqText ← match reqPath with
    | some f => try pure (some (← IO.FS.readFile f)) catch e =>
        IO.eprintln s!"fva explain: {e}"; return 2
    | none => pure none
  let reqs := reqText.map parseReqs
  if let some (_, []) := reqs then
    IO.eprintln s!"fva explain: {(reqPath.map toString).getD ""} has no `## <id>` requirement"
    return 2
  let reqName := reqPath.map fun f =>
    if f.toString.startsWith (root.toString ++ "/") then
      (f.toString.drop (root.toString.length + 1)).toString
    else f.toString
  let sha ← inputsSha o root fva t reqText
  let every := t.claims.flatMap fun c => c.name :: c.proofs
  let status (r : Row) : Bool × List String × List String :=
    match t.claims.find? (·.name == r.name) with
    | some c => proofStatus t.issues every (c.name :: c.proofs)
    | none => (false, [s!"{r.name} is no longer in the spec"], [])
  let ((rows, checks), saved) ← if !o.force && (← path.pathExists) then do
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let rows ← IO.ofExcept (j.getObjValAs? (List Row) "claims")
      let checks := (j.getObjValAs? (List ReqRow) "requirements").toOption.getD []
      let generated := (j.getObjValAs? String "generated").toOption.getD "?"
      let stale := isStale (j.getObjValAs? String "inputsSha").toOption sha (rows.map (·.name))
        (t.claims.map (·.name))
      pure ((rows, checks), (generated, true, stale))
    else do
      let (rows, checks) ← generate o root fva t reqs
      let now ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d %H:%M UTC"] }
      let generated := now.stdout.trimAscii.toString
      let rec_ := Json.mkObj [("inputsSha", toJson sha), ("generated", toJson generated),
        ("model", toJson o.model), ("effort", toJson o.effort), ("claims", toJson rows),
        ("requirementsFile", toJson reqName), ("requirements", toJson checks)]
      IO.FS.writeFile (path.addExtension "tmp") (rec_.pretty ++ "\n")
      IO.FS.rename (path.addExtension "tmp") path
      pure ((rows, checks), (generated, false, false))
  let withStatus := rows.map fun r => let (ok, mine, shared) := status r; (r, ok, mine, shared)
  if o.json then
    IO.println (Json.mkObj [("project", toJson root.toString), ("trustVerdict", toJson t.verdict),
      ("trustIssues", toJson (t.issues.map fun (k, d) => Json.mkObj [("tag", toJson k),
        ("detail", toJson d)])),
      ("saved", Json.mkObj [("file", toJson path.toString), ("generated", toJson saved.1),
        ("reused", toJson saved.2.1), ("stale", toJson saved.2.2)]),
      ("claims", Json.arr (withStatus.toArray.map fun (r, ok, mine, shared) =>
        (toJson r).mergeObj (Json.mkObj [("proof", Json.mkObj [("ok", toJson ok),
          ("issues", toJson mine), ("projectIssues", toJson shared)])]))),
      ("requirementsFile", toJson reqName), ("requirements", toJson checks)]).pretty
  else IO.print (render root.toString o.model t.verdict (some saved) withStatus
    (reqName.map (·, checks)))
  let intentOk := if reqs.isSome then checks.all (·.verdict == "matches")
    else rows.all (·.verdict == "matches")
  let good := t.verdict == "PASS" && !saved.2.2 && intentOk && withStatus.all (·.2.1)
  return if good then 0 else 1

end FVA.Tool.Explain
