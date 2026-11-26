import FVA.Spec.Wasi.World
import FVA.Json

/-!
U29a E4: tester-5's blind call-level vectors (`FVATest/Wasi/vectors/*.json`, schema in
`docs/contracts/U29a-wasi.md`) checked against the reviewed model at `E`'s choices. Run by
`scripts/test-wasi`: `lake env lean --run scripts/wasi-vectors.lean DIR`. Prints `ok ID` or
`FAIL ID: reason` per vector; exit 0 all pass, 1 a mismatch, 2 setup. Lives outside `FVATest/`
so it stays out of the mutation module graph (`.claude/rules/fva-mutation.md`).
-/

open Lean FVA.Wasi FVA.Wasm FVA.Wasm.Exec

abbrev M := Except String

instance : Inhabited Tree := ⟨.dir []⟩

def field (j : Json) (k : String) : M Json := j.getObjVal? k

def hexBytes (s : String) : M Bytes := do
  let digit (c : Char) : M Nat :=
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"hex digit {c}"
  let cs := s.toList
  if cs.length % 2 ≠ 0 then throw "odd hex"
  (List.range (cs.length / 2)).mapM fun i => do
    pure (UInt8.ofNat (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!)))

/-- `{"text"}` (UTF-8) or `{"hex"}`. -/
def bytesOf (j : Json) : M Bytes :=
  match j.getObjValAs? String "text", j.getObjValAs? String "hex" with
  | .ok t, _ => pure t.toUTF8.toList
  | _, .ok h => hexBytes h
  | _, _ => throw s!"bytes {j.compress}"

partial def treeOf (j : Json) : M Tree :=
  match field j "file", field j "dir" with
  | .ok b, _ => return .file (← bytesOf b)
  | _, .ok (.obj kvs) => return .dir (← kvs.toList.mapM fun (k, v) => do
      return (k.toUTF8.toList, ← treeOf v))
  | _, _ => throw s!"tree {j.compress}"

def natOf (j : Json) : M Nat :=
  match j.getNat?, j.getStr? with
  | .ok n, _ => pure n
  | _, .ok s => match s.toNat? with
    | some n => pure n
    | none => throw s!"number {s}"
  | _, _ => throw s!"number {j.compress}"

def arr (j : Json) : M (List Json) := return (← j.getArr?).toList

/-- An argument: a number or a decimal string, negative ones two's complement at the width. -/
def intOf (j : Json) : M Int :=
  match j.getInt?, j.getStr? with
  | .ok n, _ => pure n
  | _, .ok s => match s.toInt? with
    | some n => pure n
    | none => throw s!"number {s}"
  | _, _ => throw s!"number {j.compress}"

def stateOf (w : Json) : M State := do
  let args ← (← arr (← field w "args")).mapM fun a => return (← a.getStr?).toUTF8.toList
  let env ← (← arr (← field w "env")).mapM fun a => return (← a.getStr?).toUTF8.toList
  let stdin ← bytesOf (← field w "stdin")
  let clocks ← (← arr (← field w "clocks")).mapM natOf
  let dirs ← (← arr (← field w "dirs")).mapM fun d => do
    -- a preopen's `tree` = its entries object (the `{"dir": …}` wrapper left implicit)
    return ((← (← field d "guest").getStr?).toUTF8.toList,
      ← treeOf (.mkObj [("dir", ← field d "tree")]))
  return State.init args env stdin dirs clocks

/-- The bytes a memory cell holds: `u32`/`u64` lists little-endian, `text`, `hex`. -/
def cellBytes (c : Json) : M Bytes :=
  match field c "u32", field c "u64" with
  | .ok v, _ => return (← (← arr v).mapM natOf).flatMap (le 4)
  | _, .ok v => return (← (← arr v).mapM natOf).flatMap (le 8)
  | _, _ => bytesOf c

/-- The tree under node `n` of `σ` (entries in name order). -/
partial def treeAt (σ : State) (n : Nat) : Tree :=
  match σ.nodes[n]? with
  | some ⟨_, .file d⟩ => .file d
  | some ⟨_, .dir es⟩ => .dir ((es.map fun e => (e.1, treeAt σ e.2)).mergeSort fun a b =>
      decide (String.fromUTF8! ⟨a.1.toArray⟩ ≤ String.fromUTF8! ⟨b.1.toArray⟩))
  | none => .dir []

partial def sortTree : Tree → Tree
  | .file d => .file d
  | .dir es => .dir ((es.map fun e => (e.1, sortTree e.2)).mergeSort fun a b =>
      decide (String.fromUTF8! ⟨a.1.toArray⟩ ≤ String.fromUTF8! ⟨b.1.toArray⟩))

partial def treeEq : Tree → Tree → Bool
  | .file a, .file b => a == b
  | .dir as, .dir bs => as.length == bs.length &&
      (as.zip bs).all fun (x, y) => x.1 == y.1 && treeEq x.2 y.2
  | _, _ => false

/-- Check one vector; `none` = pass, `some reason` = mismatch. -/
def check (v : Json) : M (Option String) := do
  let mut σ ← stateOf (← field v "world")
  let pages ← natOf (← field v "pages")
  let mut s : Store := { mems := [⟨pages, none, fun _ => 0⟩] }
  let steps ← arr (← field v "steps")
  for (st, i) in steps.zipIdx do
    let some c := Call.ofName (← (← field st "call").getStr?) | throw "call"
    let mut m := s.mems.headD ⟨pages, none, fun _ => 0⟩
    for w in (← arr ((field st "mem").toOption.getD (.arr #[]))) do
      m := writeBytes m (← natOf (← field w "addr")) (← cellBytes w)
    s := { s with mems := [m] }
    let args ← (← arr (← field st "args")).mapM intOf
    let vs := (args.zip c.info.2).map fun (a, w) =>
      if w then Val.i64 (BitVec.ofInt 64 a) else Val.i32 (BitVec.ofInt 32 a)
    let ex ← field st "expect"
    let outcome ← (← field ex "outcome").getStr?
    let inP := inProfile σ c s 0 vs
    if outcome == "out-of-profile" then
      if inP then return some s!"step {i}: in profile, expected out of profile"
      return none
    if !inP then return some s!"step {i}: out of profile"
    let (τ, o) := exec σ c s 0 vs {}
    match outcome, o with
    | "exit", .trapped s' =>
      let code ← natOf (← field ex "code")
      if τ.exited != some code then return some s!"step {i}: exit {τ.exited}, expected {code}"
      s := s'
    | "errno", .returned s' [.i32 e] | "any-bytes", .returned s' [.i32 e] =>
      let want ← natOf (← field ex "errno")
      if e.toNat != want then return some s!"step {i}: errno {e.toNat}, expected {want}"
      let m' := s'.mems.headD ⟨pages, none, fun _ => 0⟩
      for cell in (← arr ((field ex "mem").toOption.getD (.arr #[]))) do
        let a ← natOf (← field cell "addr")
        let want ← cellBytes cell
        let got := memBytes m' a want.length
        if got != want then return some s!"step {i}: memory at {a} = {got}, expected {want}"
      s := s'
    | _, _ => return some s!"step {i}: outcome ≠ {outcome}"
    σ := τ
  let fin ← field v "final"
  for (k, sel) in [("stdout", σ.stdout), ("stderr", σ.stderr)] do
    if let .ok b := field fin k then
      let want ← bytesOf b
      if sel != want then return some s!"final {k} {sel}, expected {want}"
  if let .ok (.obj fs) := field fin "files" then
    for (g, t) in fs.toList do
      let some r := σ.roots.lookup g.toUTF8.toList | return some s!"final: no root {g}"
      if !treeEq (treeAt σ r) (sortTree (← treeOf (.mkObj [("dir", t)]))) then
        return some s!"final files under {g} differ"
  if let .ok e := field fin "exited" then
    if let .ok k := natOf e then
      if σ.exited != some k then return some s!"final exited {σ.exited}, expected {k}"
  return none

def main (argv : List String) : IO UInt32 := do
  let some dir := argv.head? | IO.eprintln "usage: wasi-vectors DIR"; return 2
  let files := (← System.FilePath.readDir dir).filter (·.path.extension == some "json")
  if files.isEmpty then IO.eprintln s!"wasi-vectors: no vectors in {dir}"; return 2
  let mut fails := 0
  for f in files.qsort (·.fileName < ·.fileName) do
    let v ← match FVA.parseJson (← IO.FS.readFile f.path) with
      | .ok v => pure v
      | .error e => IO.eprintln s!"wasi-vectors: {f.fileName}: {e}"; return 2
    let id := (v.getObjValAs? String "id").toOption.getD f.fileName
    match check v with
    | .error e => IO.eprintln s!"wasi-vectors: {id}: setup: {e}"; return 2
    | .ok none => IO.println s!"ok {id}"
    | .ok (some r) => IO.println s!"FAIL {id}: {r}"; fails := fails + 1
  IO.println s!"wasi-vectors: {files.size - fails} pass, {fails} FAIL, {files.size} vectors"
  return if fails = 0 then 0 else 1
