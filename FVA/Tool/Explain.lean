import Lean
import FVA.Tool.Codex
import FVA.Tool.Trust
import FVA.Trust.Collect

/-!
# `fva explain` (advisory review aid; the verdict stays with `fva trust`)

The spec in plain English for a reader who cannot read Lean, by Claimcheck's two-pass round trip
(https://github.com/metareflection/claimcheck), reimplemented: pass 1 explains each claim from
the comment-stripped spec source plus its elaborated statement (it never sees the author's
intent), pass 2 compares that explanation with the intent (docstring, else name). Example inputs
come from pass 1 plus fixed `0`, `1` per argument; their outputs never come from the model: the
spec value is Lean's evaluation of the claim's `Returns` result, the binary value is wasmtime's.

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

/-- Seconds for one spec-value case (a too-costly case is shown as such). -/
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
- examples (required for every claim that calls an exported function on integer arguments):
  3 to 6 argument lists (inputs only, no outputs) that show the behavior, boundary cases
  included. Integers; negative values are allowed where the claim reads a value as signed. Keep
  values small where the result needs a loop or recursion over the input.

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
- weaker: the claim guarantees less (narrower inputs, missing cases, a looser result).
- stronger: the claim guarantees more than the intent says.
- different: the claim guarantees something else.
- vacuous: the claim is trivially true or says nothing about the function.
reason: one or two plain-English sentences a non-expert can follow; cite an example if one shows
the gap.

" ++ items

/-- Parsed options. -/
structure Opts where
  dir : String := ""
  spec : Option String := none
  root : Option String := none
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
  | "--model" :: m :: r => parse { o with model := m } r
  | "--effort" :: e :: r => parse { o with effort := e } r
  | "--force" :: r => parse { o with force := true } r
  | "--json" :: r => parse { o with json := true } r
  | a :: r =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if o.dir.isEmpty then parse { o with dir := a } r
    else .error s!"unexpected argument {a}"

/-- The source file of module `m` under `root`. -/
def modFile (root : System.FilePath) (m : String) : System.FilePath :=
  root / ("/".intercalate (m.splitOn "."))
    |>.addExtension "lean"

/-- Run `cmd` (stdout captured) under `timeout`; `none` = killed at the deadline. -/
def runTimed (cmd : String) (args : Array String) (cwd : System.FilePath) (secs : Nat) :
    IO (Option IO.Process.Output) := do
  let o ← IO.Process.output
    { cmd := "timeout", args := #["-s", "KILL", toString secs, cmd] ++ args, cwd }
  return if o.exitCode == 137 then none else some o

/-- `#eval` `cmd` (writing JSON lines to the file it is given) in a file importing the spec
module, under `lake env lean` in the project; the lines written + whether Lean finished. -/
def evalLean (root : System.FilePath) (spec : String) (cmd : System.FilePath → String)
    (secs : Nat) : IO (Array Json × Bool) :=
  IO.FS.withTempDir fun tmp => do
    let out := tmp / "out.jsonl"
    IO.FS.writeFile out ""
    let src := root / s!"FvaExplain_{(← IO.monoNanosNow)}.lean"
    IO.FS.writeFile src s!"import {spec}\nimport FVA.Explain\n{cmd out}\n"
    let r ← try runTimed "lake" #["env", "lean", src.toString] root secs finally
      IO.FS.removeFile src
    let lines := (← IO.FS.readFile out).splitOn "\n" |>.filter (!·.isEmpty)
    return (lines.toArray.filterMap fun l => (Json.parse l).toOption,
      r.any (·.exitCode == 0))

/-- One claim's shape, statement and docstring (`FVA.Explain.shapes`). -/
structure Shape where
  doc : Option String
  statement : String
  fn : Option String
  params : Array (String × Nat)

/-- Read every claim's `Shape`. -/
def shapes (root : System.FilePath) (spec : String) (claims : Array String) :
    IO (Std.HashMap String Shape) := do
  let names := ", ".intercalate (claims.toList.map ("`" ++ ·))
  let (rows, done) ← evalLean root spec
    (fun out => s!"#eval FVA.Explain.shapes [{names}] {repr out.toString}") 300
  unless done do throw <| .userError "fva explain: reading the claims' statements failed"
  let mut m := {}
  for r in rows do
    let some c := (r.getObjValAs? String "claim").toOption | continue
    let sh := r.getObjValD "shape"
    let ps := ((sh.getObjValD "params").getArr?.toOption.getD #[]).filterMap fun p =>
      match p.getObjValAs? String "name", p.getObjValAs? Nat "bits" with
      | .ok n, .ok b => some (n, b)
      | _, _ => none
    m := m.insert c { doc := (r.getObjValAs? String "doc").toOption,
                      statement := (r.getObjValAs? String "statement").toOption.getD "",
                      fn := (sh.getObjValAs? String "fn").toOption, params := ps }
  return m

/-- Spec value per case (`none` = too costly: the evaluation was killed or crashed). -/
partial def specValues (root : System.FilePath) (spec claim : String)
    (cases : List (List Nat)) : IO (List (Option (List (String × Nat)))) := do
  if cases.isEmpty then return []
  let lit := "[" ++ ", ".intercalate (cases.map fun c => toString c) ++ "]"
  let (rows, _) ← evalLean root spec
    (fun out => s!"#eval FVA.Explain.run `{claim} {lit} {repr out.toString}")
    (caseSeconds + 5 * cases.length)
  let vals := rows.toList.map fun r =>
    ((r.getObjValD "res").getArr?.toOption.getD #[]).toList.filterMap fun v =>
      match v.getObjValAs? String "type", v.getObjValAs? Nat "value" with
      | .ok t, .ok x => some (t, x)
      | _, _ => none
  let got := vals.take cases.length
  if got.length == cases.length then return got.map some
  -- the case after the last result was too costly: skip it, continue with the rest
  let rest ← specValues root spec claim (cases.drop (got.length + 1))
  return got.map some ++ [none] ++ rest

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

/-- One explained claim. -/
structure Row where
  name : String
  intent : Option String
  statement : String
  summary : String
  details : List String
  caveats : List String
  fn : Option String := none
  params : List (String × Nat) := []
  resultBits : List Nat := []
  examples : List Example := []
  verdict : String := "unknown"
  reason : String := ""

instance : ToJson Example where
  toJson e := Json.mkObj [("args", toJson e.args), ("spec", toJson e.spec),
    ("binary", toJson e.binary)]

instance : FromJson Example where
  fromJson? j := do
    let args ← j.getObjValAs? (List Nat) "args"
    let spec ← j.getObjValAs? (Option (List Nat)) "spec"
    let binary ← j.getObjValAs? (Option (List Nat)) "binary"
    return { args, spec, binary }

instance : ToJson Row where
  toJson r := Json.mkObj [("name", toJson r.name), ("intent", toJson r.intent),
    ("statement", toJson r.statement), ("summary", toJson r.summary),
    ("details", toJson r.details), ("caveats", toJson r.caveats), ("fn", toJson r.fn),
    ("params", toJson (r.params.map fun (n, b) => Json.mkObj [("name", toJson n),
      ("bits", toJson b)])),
    ("resultBits", toJson r.resultBits), ("examples", toJson r.examples),
    ("verdict", toJson r.verdict), ("reason", toJson r.reason)]

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
             examples, verdict, reason }

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

/-- The FVA files whose text the prompt carries (claim vocabulary) or the examples rest on. -/
def fvaFiles (fva : System.FilePath) : List System.FilePath :=
  [fva / "FVA/Spec/CAbi.lean", fva / "FVA/Spec/Claims.lean", fva / "FVA/Explain.lean"]

/-- sha256 of every input the saved text derives from: model, effort, prompts, schemas, the
review-surface files, the lifted modules (their numerals are the `.wasm` bytes), FVA's files. -/
def inputsSha (o : Opts) (root fva : System.FilePath) (t : Trust) : IO String :=
  IO.FS.withTempDir fun tmp => do
    let files := (t.reviewModules.map (modFile root) ++
      (t.claims.flatMap (·.subjects)).eraseDups.map (modFile root)).mergeSort
      (·.toString ≤ ·.toString) ++ fvaFiles fva
    let mut payload := toString (toJson [o.model, o.effort, explainPrompt "" "" "",
      comparePrompt "", explainSchema.compress, compareSchema.compress,
      toString fixedInputs, toString maxExamples])
    for f in files do
      payload := payload ++ "\x00" ++ f.toString ++ "\x00" ++
        (← try IO.FS.readFile f catch _ => pure "(missing)")
    IO.FS.writeFile (tmp / "in") payload
    let r ← IO.Process.output { cmd := "sha256sum", args := #[(tmp / "in").toString] }
    return (r.stdout.splitOn " ").headD ""

/-- Pass 1, examples, pass 2. -/
def generate (o : Opts) (root fva : System.FilePath) (t : Trust) : IO (List Row) := do
  let spec := o.spec.getD ""
  let names := t.claims.map (·.name)
  let sh ← shapes root spec names.toArray
  let specText ← t.reviewModules.foldlM (init := "") fun acc m => do
    let src ← try IO.FS.readFile (modFile root m) catch _ => pure ""
    return acc ++ s!"--- {m}\n{FVA.Trust.stripComments src}\n"
  let vocab ← (fvaFiles fva).take 2 |>.foldlM (init := "") fun acc f => do
    return acc ++ s!"--- {f.fileName.getD ""}\n{← IO.FS.readFile f}\n"
  let statements := "\n".intercalate (names.filterMap fun n =>
    (sh.get? n).map fun s => s!"{n} : Prop := {s.statement}")
  let p1 ← Codex.ask (explainPrompt statements specText vocab) explainSchema o.model o.effort
  let p1rows := (p1.getObjValD "claims").getArr?.toOption.getD #[]
  let find (rows : Array Json) (n : String) : Json :=
    let short := (n.splitOn ".").getLastD n
    (rows.find? fun r => let x := (r.getObjValAs? String "name").toOption.getD ""
      x == n || x == short).getD Json.null
  let wasmtime :=
    let p := fva / ".tools/bin/wasmtime"
    p.toString
  let mut rows := #[]
  for c in t.claims do
    let e := find p1rows c.name
    let strsOf (k : String) := (e.getObjValAs? (List String) k).toOption.getD []
    let s := sh.get? c.name
    let mut row : Row :=
      { name := c.name, intent := s.bind (·.doc), statement := (s.map (·.statement)).getD "",
        summary := (e.getObjValAs? String "summary").toOption.getD "",
        details := strsOf "details", caveats := strsOf "caveats" }
    if let (some s, [subj]) := (s, c.subjects) then
      if let some fn := s.fn then
        let bits := s.params.toList.map (·.2)
        let proposed := ((e.getObjValAs? (List (List Int)) "examples").toOption.getD []) ++
          fixedInputs.map fun v => List.replicate bits.length (Int.ofNat v)
        let cases := (proposed.filter (·.length == bits.length)).map fun xs =>
          (xs.zip bits).map fun (a, b) => (a % (2 ^ b : Int)).toNat
        let cases := (cases.eraseDups).take maxExamples
        let specV ← specValues root spec c.name cases
        let resBits := ((specV.findSome? id).getD []).map (typeBits ·.1)
        let wasm ← match ← liftedSource (modFile root subj) with
          | some w => pure (root / w)
          | none => pure (root / "missing.wasm")
        let mut exs := #[]
        for (a, v) in cases.zip specV do
          let b ← binaryValue wasmtime wasm fn (a.zip bits) resBits
          exs := exs.push { args := a, spec := v.map (·.map (·.2)), binary := b }
        row := { row with fn := some fn, params := s.params.toList, resultBits := resBits,
                          examples := exs.toList }
    rows := rows.push row
  let items := "\n\n".intercalate (rows.toList.map fun r =>
    let intent := r.intent.getD s!"none written; infer it from the name {r.name}"
    let exs := r.examples.filterMap fun x => x.spec.map fun v =>
      s!"Example: {r.fn.getD ""}({", ".intercalate (x.args.map toString)}) → spec says {v}\n"
    s!"## {r.name}\nIntent: {intent}\nFormal statement: {r.statement}\n" ++
      s!"Explanation: {r.summary} {" ".intercalate r.details}\n" ++ String.join exs)
  let p2 ← Codex.ask (comparePrompt items) compareSchema o.model o.effort
  let p2rows := (p2.getObjValD "claims").getArr?.toOption.getD #[]
  return rows.toList.map fun r =>
    let v := find p2rows r.name
    { r with verdict := (v.getObjValAs? String "verdict").toOption.getD "unknown",
             reason := (v.getObjValAs? String "reason").toOption.getD "no reply" }

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
    (rows : List (Row × Bool × List String × List String)) : String := Id.run do
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
      out := out.push "  Examples (spec value computed by Lean; binary value from wasmtime):"
      let widths := c.params.map (·.2)
      for x in c.examples do
        let call := s!"{c.fn.getD ""}({", ".intercalate ((x.args.zip widths).map fun (a, b) =>
          num a b)})"
        let sv := match x.spec with
          | none => "too costly to compute"
          | some v => ", ".intercalate ((v.zip c.resultBits).map fun (a, b) => num a b)
        let agree := match x.spec, x.binary with
          | none, _ => ""
          | some v, some b => if v == b then "  binary agrees" else s!"  ✗ binary returns {b}"
          | some _, none => "  ✗ binary traps"
        out := out ++ (wrap s!"{call} → {sv}{agree}" "    " "        ").toArray
    else if c.fn.isNone && !c.statement.isEmpty then
      out := out ++ #["  Examples: none. FVA computes examples only for claims of the form",
        "  `∀ inputs, Returns …` over integer arguments. Lean reads this claim as:"] ++
        (wrap (" ".intercalate (c.statement.splitOn "\n" |>.map (·.trimAscii.toString)))
          "    " "      ").toArray
    let intent := c.intent.getD s!"(no description; inferred from the name {c.name})"
    out := out ++ (wrap intent "  Stated intent: " "    ").toArray ++
      (wrap s!"{c.verdict.toUpper} — {c.reason}" s!"  {mark} Intent check: " "    ").toArray
  return "\n".intercalate out.toList ++ "\n"

/-- `fva explain <lake-dir> --spec-module M [--root-module R] [--model M] [--effort E] [--force]
[--json]`: rc 0 = trust PASS, every intent check `matches`, text current; 1 otherwise; 2 = usage. -/
def main (argv : List String) : IO UInt32 := do
  let o ← match parse {} argv with
    | .ok o => pure o
    | .error e => IO.eprintln s!"fva explain: {e}"; return 2
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
  let path := (modFile root spec).parent.getD root / savedName
  let sha ← inputsSha o root fva t
  let every := t.claims.flatMap fun c => c.name :: c.proofs
  let status (r : Row) : Bool × List String × List String :=
    match t.claims.find? (·.name == r.name) with
    | some c => proofStatus t.issues every (c.name :: c.proofs)
    | none => (false, [s!"{r.name} is no longer in the spec"], [])
  let (rows, saved) ← if !o.force && (← path.pathExists) then do
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
      let rows ← IO.ofExcept (j.getObjValAs? (List Row) "claims")
      let generated := (j.getObjValAs? String "generated").toOption.getD "?"
      let stale := isStale (j.getObjValAs? String "inputsSha").toOption sha (rows.map (·.name))
        (t.claims.map (·.name))
      pure (rows, (generated, true, stale))
    else do
      let rows ← generate o root fva t
      let now ← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d %H:%M UTC"] }
      let generated := now.stdout.trimAscii.toString
      let rec_ := Json.mkObj [("inputsSha", toJson sha), ("generated", toJson generated),
        ("model", toJson o.model), ("effort", toJson o.effort), ("claims", toJson rows)]
      IO.FS.writeFile (path.addExtension "tmp") (rec_.pretty ++ "\n")
      IO.FS.rename (path.addExtension "tmp") path
      pure (rows, (generated, false, false))
  let withStatus := rows.map fun r => let (ok, mine, shared) := status r; (r, ok, mine, shared)
  if o.json then
    IO.println (Json.mkObj [("project", toJson root.toString), ("trustVerdict", toJson t.verdict),
      ("trustIssues", toJson (t.issues.map fun (k, d) => Json.mkObj [("tag", toJson k),
        ("detail", toJson d)])),
      ("saved", Json.mkObj [("file", toJson path.toString), ("generated", toJson saved.1),
        ("reused", toJson saved.2.1), ("stale", toJson saved.2.2)]),
      ("claims", Json.arr (withStatus.toArray.map fun (r, ok, mine, shared) =>
        (toJson r).mergeObj (Json.mkObj [("proof", Json.mkObj [("ok", toJson ok),
          ("issues", toJson mine), ("projectIssues", toJson shared)])])))]).pretty
  else IO.print (render root.toString o.model t.verdict (some saved) withStatus)
  let good := t.verdict == "PASS" && !saved.2.2 &&
    withStatus.all fun (r, ok, _, _) => ok && r.verdict == "matches"
  return if good then 0 else 1

end FVA.Tool.Explain
