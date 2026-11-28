import FVA.Impl.Exec.SysRunRem
import FVA.Impl.Exec.WasiHost
import FVA.Impl.Valid
import FVA.Tool.Pack
import FVA.Impl.Decode

/-!
# `fva run`: a WASI command on the verified machine (U29b2; trusted glue)

`docs/contracts/U29b-host.md` U29b2. Loads the module with the verified decoder + validator,
instantiates it on the machine (`instantiateU`), starts the world from the command line (argv,
`--env`, `--dir` trees read whole, stdin read whole, clocks 0), then advances the machine with the
verified WASI host: machine steps in step-counted segments (`sysRunRem`), each host call answered
through `answerHost` (`random_get` with fresh or `--random` bytes) and its stdout/stderr bytes
emitted at once. Every stop syncs each root's final tree back (a diff against the start tree,
applied in place) before the exit status: `proc_exit k` → k (k ≥ 126 → 1), `_start` returning
→ 0, a trap → 134, an uncaught exception → 1, anything FVA cannot continue → 2. FVA writes one
`fva run: ` diagnostic at most, after the program's last stderr byte.
-/

namespace FVA.Tool.Run

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi

/-- The command line. -/
structure Opts where
  /-- The module's path. -/
  wasm : Option String := none
  /-- Preopens: host directory + guest name, in order. -/
  dirs : Array (String × String) := #[]
  /-- Environment entries `K=V`, in order. -/
  env : Array String := #[]
  /-- Fixed bytes for every `random_get`. -/
  random : Option ByteArray := none
  /-- The step budget. -/
  fuel : Option Nat := none
  /-- The guest's arguments after argv[0]. -/
  args : Array String := #[]

/-- The bytes of a hex string with an even number of digits. -/
def unhex (s : String) : Option ByteArray := do
  let ds ← s.toList.mapM fun c =>
    if c.isDigit then some (c.toNat - 48)
    else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (c.toLower.toNat - 87) else none
  if ds.length % 2 != 0 then none
  else some ⟨((List.range (ds.length / 2)).map fun i =>
    UInt8.ofNat (16 * ds[2 * i]! + ds[2 * i + 1]!)).toArray⟩

/-- Parse `fva run`'s arguments (options before `--` in any order, each value the next
argument). -/
def parse : List String → Opts → Except String Opts
  | [], o => if o.wasm.isNone then .error "give the module: fva run <file.wasm>" else .ok o
  | "--" :: rest, o =>
    if o.wasm.isNone then .error "give the module before --"
    else .ok { o with args := rest.toArray }
  | "--dir" :: v :: rest, o =>
    let (h, g) := match v.splitOn "::" with
      | [h] => (h, h)
      | h :: g => (h, "::".intercalate g)
      | [] => (v, v)
    if h.isEmpty then .error "--dir needs a host directory" else
    parse rest { o with dirs := o.dirs.push (h, g) }
  | "--env" :: v :: rest, o =>
    if v.contains '=' then parse rest { o with env := o.env.push v }
    else .error s!"--env {v}: write NAME=VALUE"
  | "--random" :: v :: rest, o =>
    if o.random.isSome then .error "--random given twice" else
    match unhex v with
    | some b => parse rest { o with random := some b }
    | none => .error s!"--random {v}: give the bytes as hex digits, two per byte"
  | "--fuel" :: v :: rest, o =>
    if o.fuel.isSome then .error "--fuel given twice" else
    match v.toNat? with
    | some n => parse rest { o with fuel := some n }
    | none => .error s!"--fuel {v}: give a whole number of steps"
  | a :: rest, o =>
    if ["--dir", "--env", "--random", "--fuel"].contains a then .error s!"{a} needs a value"
    else if a.startsWith "-" then .error s!"unknown option {a}"
    else if o.wasm.isSome then .error s!"{a}: give the program's arguments after --"
    else parse rest { o with wasm := some a }

/-- A directory tree on the host, read whole: regular files and directories alone. -/
partial def readTree (root : System.FilePath) : IO Tree := do
  -- one `find` per root: types + link counts by relative path, NUL-separated
  let fargs := #[root.toString, "-mindepth", "1", "-printf", "%y %n %P\\0"]
  let child ← IO.Process.spawn
    { cmd := "find", args := fargs, stdout := .piped, stderr := .piped }
  let out ← child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  if (← child.wait) != 0 then throw (IO.userError s!"cannot list {root}: {err.trimAscii}")
  let recs ← (out.toList.splitOn 0).filter (· ≠ []) |>.mapM fun bs => do
    let some s := String.fromUTF8? ⟨bs.toArray⟩
      | throw (IO.userError s!"a name below {root} is not UTF-8")
    match s.splitOn " " with
    | ty :: n :: path => pure (ty, n.toNat?.getD 0, " ".intercalate path)
    | _ => throw (IO.userError s!"cannot read the listing of {root}")
  for (ty, n, path) in recs do
    match ty with
    | "d" => pure ()
    | "f" =>
      if n > 1 then throw (IO.userError s!"{root / path} has more than one name (hard link)")
    | "l" => throw (IO.userError s!"{root / path} is a symbolic link")
    | _ => throw (IO.userError s!"{root / path} is not a regular file or directory")
  build recs ""
where
  /-- The tree at relative directory `pre` (`""` = the root). -/
  build (recs : List (String × Nat × String)) (pre : String) : IO Tree := do
    let kids := recs.filter fun (_, _, p) =>
      if pre.isEmpty then !p.contains '/'
      else p.startsWith (pre ++ "/") && !((p.drop (pre.length + 1)).toString.contains '/')
    let key (r : String × Nat × String) : List UInt8 := r.2.2.toUTF8.data.toList
    let kids := kids.toArray.qsort (fun a b => key a < key b)
    let es ← kids.toList.mapM fun (ty, _, p) => do
      let name := if pre.isEmpty then p else (p.drop (pre.length + 1)).toString
      let t ← if ty == "d" then build recs p
        else pure (.file (← IO.FS.readBinFile (root / p)).data.toList)
      pure (name.toUTF8.data.toList, t)
    return .dir es

/-- Make host directory `h` hold tree `t'`, where it held `t`: entries equal in both stay
untouched. -/
partial def sync (h : System.FilePath) : Tree → Tree → IO Unit
  | .file d, .file d' => if d == d' then pure () else IO.FS.writeBinFile h ⟨d'.toArray⟩
  | .dir es, .dir es' => do
    for (n, t) in es do
      if (es'.lookup n).isNone then remove (h / (← name n)) t
    for (n, t') in es' do
      match es.lookup n with
      | some t => sync (h / (← name n)) t t'
      | none => create (h / (← name n)) t'
  | t, t' => do remove h t; create h t'
where
  /-- An entry name as a host path component. -/
  name (n : Bytes) : IO String := match String.fromUTF8? ⟨n.toArray⟩ with
    | some s => pure s
    | none => throw (IO.userError s!"a guest name below {h} is not UTF-8")
  /-- Delete `h`, which holds `t`. -/
  remove (h : System.FilePath) : Tree → IO Unit
    | .file _ => IO.FS.removeFile h
    | .dir _ => IO.FS.removeDirAll h
  /-- Create `h` holding `t`. -/
  create (h : System.FilePath) : Tree → IO Unit
    | .file d => IO.FS.writeBinFile h ⟨d.toArray⟩
    | .dir es => do
      IO.FS.createDir h
      for (n, t) in es do create (h / (← name n)) t

/-- Why a run stopped. -/
inductive Stop where
  /-- `proc_exit k`. -/
  | exited (k : Nat)
  /-- `_start` returned. -/
  | returned
  /-- A trap, reached or pending inside control frames. -/
  | trapped
  /-- An exception no handler caught. -/
  | thrown
  /-- A host call the host leaves unanswered: its name and why. -/
  | unanswered (call why : String)
  /-- A step the semantics leaves open (a NaN result's payload). -/
  | choice
  /-- No step and no ending. -/
  | stuck
  /-- The fuel ran out. -/
  | fuel
  /-- FVA's own input or output failed mid-run (emission, random bytes): what failed. -/
  | failed (what : String)

/-- Why process `m` (WASI memory `mem`) stopped in world `σ`, machine `ms`, `exhausted` = the
fuel ran out; at a host call = the host left it unanswered. -/
def stopOf (m : Module) (mem : Nat) (σ : State) (ms : MState) (exhausted : Bool) : Stop :=
  match σ.exited with
  | some k => .exited k
  | none =>
    if exhausted then .fuel else
    match ms.hostCall with
    | some (id, k, _) =>
      let vs := (ms.stack.take k).reverse
      match bind m id with
      | some c => .unanswered c.info.1 (why c vs)
      | none => .unanswered ((m.imports[id]?.map (·.name)).getD "?") "not a declared WASI call"
    | none =>
      match ms.code with
      | .trap :: _ => .trapped
      | _ => match ms.ending with
        | .returned _ => .returned
        | .trapped => .trapped
        | .thrown _ => .thrown
        | .stuck => if ms.step.isSome then .choice else .stuck
where
  /-- Why the host leaves call `c` on `vs` unanswered. -/
  why (c : Call) (vs : List Val) : String :=
    if ms.store.mems[mem]?.isNone then "the module has no memory at the WASI memory address"
    else if !inProfile σ c ms.store.abs mem vs then "arguments outside the profile domain"
    else "a result written outside the memory"

/-- The tree at node `n` of `σ` (`fuel` bounds the depth; `none` when it runs out or a node is
missing). -/
def exportTree (σ : State) : Nat → Nat → Option Tree
  | 0, _ => none
  | fuel + 1, n => match σ.nodes[n]? with
    | some ⟨_, .file d⟩ => some (.file d)
    | some ⟨_, .dir es⟩ => (es.mapM fun e => (exportTree σ fuel e.2).map (e.1, ·)).map .dir
    | none => none

/-- Read all of standard input. -/
partial def readStdin : IO ByteArray := do
  let s ← IO.getStdin
  let rec go (acc : ByteArray) : IO ByteArray := do
    let b ← s.read 65536
    if b.isEmpty then pure acc else go (acc ++ b)
  go .empty

/-- `fva run: ` + a message on stderr; a stderr that fails to take it changes nothing. -/
def note (msg : String) : IO Unit := do
  try
    let e ← IO.getStderr
    e.putStr s!"fva run: {msg}\n"
    e.flush
  catch _ => pure ()

/-- An error's text on one line (IO errors add a `file:` line). -/
def oneLine (e : IO.Error) : String :=
  " ".intercalate (((toString e).splitOn "\n").map (·.trimAscii.toString) |>.filter (· ≠ ""))

/-- Machine steps per segment (a segment ends early at each host call). -/
def segment : Nat := 1000000

/-- The run's world, machine, the stdout/stderr bytes emitted, the steps left. -/
structure Live where
  /-- World. -/
  σ : State
  /-- Machine. -/
  m : MState
  /-- stdout bytes emitted. -/
  out : Nat
  /-- stderr bytes emitted. -/
  err : Nat
  /-- Steps left (`none` = no limit). -/
  left : Option Nat

/-- Write the stdout/stderr bytes not emitted yet; an error names the stream. -/
def emit (l : Live) : IO Live := do
  let put (name : String) (h : IO.FS.Stream) (bs : Bytes) (done : Nat) : IO Unit := do
    if bs.length > done then
      try
        h.write ⟨(bs.drop done).toArray⟩
        h.flush
      catch e => throw (IO.userError s!"cannot write the program's {name} ({oneLine e})")
  put "stdout" (← IO.getStdout) l.σ.stdout l.out
  put "stderr" (← IO.getStderr) l.σ.stderr l.err
  return { l with out := l.σ.stdout.length, err := l.σ.stderr.length }

/-- Advance the process until it stops: machine steps in segments that end at each host call,
the call answered here by the verified host (`random_get` with fresh or `--random` bytes from
`rand`), its stdout/stderr bytes emitted before the program continues, so both streams keep the
program's write order. -/
partial def drive (mod : Module) (mem : Nat) (rand : Nat → IO ByteArray) (l : Live) :
    IO (Live × Stop) := do
  let n := match l.left with | some k => min k segment | none => segment
  let (σ, m, ex, rem) := sysRunRem State.exited (fun _ _ _ _ => none) n (l.σ, l.m)
  let l := { l with σ, m, left := l.left.map (· - (n - rem)) }
  if let (none, false, some (id, k, _)) := (σ.exited, ex, m.hostCall) then
    if l.left == some 0 then return (l, .fuel)
    let bytes ← match bind mod id with
      | some .randomGet =>
        let vs := (m.stack.take k).reverse
        match ← (rand (((Call.randomGet.args vs).bind (·[1]?)).getD 0)).toBaseIO with
        | .ok b => pure (some b.data.toList)
        | .error e => return (l, .failed s!"cannot get random bytes for random_get ({oneLine e})")
      | _ => pure none
    if let some (τ, m') := answerHost (wasiHost mod mem bytes) (σ, m) then
      let l := { l with σ := τ, m := m', left := l.left.map (· - 1) }
      match ← (emit l).toBaseIO with
      | .ok l => return ← drive mod mem rand l
      | .error e => return (l, .failed (oneLine e))
  match stopOf mod mem σ m ex with
  | .fuel => if l.left == some 0 then return (l, .fuel) else drive mod mem rand l
  | s => return (l, s)

/-- The module's `_start` export, if it is a function of type `[] → []`. -/
def startOf (ms : MStore) (inst : ModuleInst) : Option Nat := do
  let a ← inst.exportFunc "_start"
  match ms.base.funcs[a]? with
  | some (.wasm dt _ _) => match dt.expand with
    | some ⟨[], []⟩ => some a
    | _ => none
  | _ => none

/-- Why `m` cannot launch as a WASI command (load-time checks), if it cannot. -/
def loadError (m : Module) : Option String :=
  if !Valid.validate m then some "the module is not valid"
  else if m.start.isSome then some "the module has a start function"
  else if m.exports.any (·.name == "_initialize") then some "the module exports _initialize"
  else if !m.exports.any (fun e => e.name == "memory" && e.desc matches .mem _) then
    some "the module exports no memory"
  else match (List.range m.imports.length).find? fun i => (bind m i).isNone with
    | some i => match m.imports[i]? with
      | some im => some s!"import {im.module}.{im.name}: not one of FVA's WASI calls"
      | none => none
    | none => none

/-- The effect statement of a failure before the program starts. -/
def unstarted : String := "the program did not start and no file changed"

/-- `fva run`, unguarded: `main` turns an unexpected IO error into status 2. -/
def run (args : List String) : IO UInt32 := do
  match parse args {} with
  | .error e => note e; return 2
  | .ok o =>
  let some wasm := o.wasm | note "give the module"; return 2
  -- the trees, the module, stdin: everything is read before the program starts
  let mut dirs : Array (Bytes × Tree) := #[]
  let mut canon : Array System.FilePath := #[]
  for (h, g) in o.dirs do
    unless ← System.FilePath.isDir h do
      note s!"--dir {h}: not a directory"; return 2
    let c ← IO.FS.realPath h
    if canon.any fun d => d == c || (c.toString.startsWith (d.toString ++ "/")) ||
        (d.toString.startsWith (c.toString ++ "/")) then
      note s!"--dir {h}: overlaps another --dir"; return 2
    canon := canon.push c
    match ← (readTree h).toBaseIO with
    | .ok t => dirs := dirs.push (g.toUTF8.data.toList, t)
    | .error e => note s!"--dir {h}: {oneLine e}; {unstarted}"; return 2
  let bs ← match ← (IO.FS.readBinFile wasm).toBaseIO with
    | .ok bs => pure bs
    | .error e => do note s!"{wasm}: {oneLine e}"; return 2
  let mod ← match Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m => pure m
    | .error e => do note s!"{wasm}: FVA cannot decode it ({repr e})"; return 2
  if let some e := loadError mod then note s!"{wasm}: {e}"; return 2
  let some (ms, inst) := instantiateU (2 ^ 40) (hostMStore mod) mod (hostImports mod)
    | note s!"{wasm}: instantiation failed (an initializer or segment traps)"; return 2
  let some a := startOf ms inst | note s!"{wasm}: no _start function of type [] → []"; return 2
  let some mem := inst.exportMem "memory" | note s!"{wasm}: the module exports no memory"; return 2
  let stdin ← match ← readStdin.toBaseIO with
    | .ok b => pure b
    | .error e => do note s!"standard input: {oneLine e}; {unstarted}"; return 2
  let argv0 := (System.FilePath.mk wasm).fileName.getD wasm
  let σ₀ := State.init ((argv0 :: o.args.toList).map (·.toUTF8.data.toList))
    (o.env.toList.map (·.toUTF8.data.toList)) stdin.data.toList dirs.toList [0, 0, 0, 0]
  let rand (k : Nat) : IO ByteArray := match o.random with
    | some b => pure b
    | none => IO.getRandomBytes k.toUSize
  -- from here on FVA writes one diagnostic at most: a stop's message, then the --random label
  let finish (rc : UInt32) (msg : Option String) : IO UInt32 := do
    let label := if o.random.isSome then
      ["random_get returned the bytes given by --random, not fresh random bytes"] else []
    match msg.toList ++ label with
    | [] => pure ()
    | ms => note ("; ".intercalate ms)
    return rc
  let live : Live := { σ := σ₀, m := MState.ofInvoke ms a [], out := 0, err := 0, left := o.fuel }
  let (l, stop) ← drive mod mem rand live
  -- every stop syncs the trees back first
  let mut i := 0
  for ((g, t), (h, _)) in dirs.toList.zip o.dirs.toList do
    let root := (l.σ.roots[i]?.map (·.2)).getD 0
    i := i + 1
    match exportTree l.σ (l.σ.nodes.length + 1) root with
    | some t' =>
      match ← (sync h t t').toBaseIO with
      | .ok () => pure ()
      | .error e => return ← finish 2 (some s!"--dir {h}: syncing the files back failed \
          ({oneLine e}); the directory may hold partial changes")
    | none => return ← finish 2 (some s!"--dir {h} ({String.fromUTF8! ⟨g.toArray⟩}): the final \
        tree cannot be read; no file changed")
  match stop with
  | .exited k =>
    if k < 126 then finish k.toUInt32 none else
    finish 1 (some s!"the program exited with status {k}; statuses from 126 on are reported as 1")
  | .returned => finish 0 none
  | .trapped => finish 134 (some "the program trapped")
  | .thrown => finish 1 (some "the program threw an exception that no handler caught")
  | .unanswered c why => finish 2 (some s!"host call {c} stopped the run: {why}")
  | .choice =>
    finish 2 (some "the next step has more than one allowed result (a NaN payload): FVA stops")
  | .stuck => finish 2 (some "the machine is stuck")
  | .fuel => finish 2 (some s!"step limit {o.fuel.getD 0} reached")
  | .failed what => finish 2 (some s!"{what}; the run stopped early, so the program's effects \
      are partial (FVA wrote its file changes back)")

/-- `fva run` (exit status: the program's, or 2 when FVA cannot run or finish it). -/
def main (args : List String) : IO UInt32 := do
  match ← (run args).toBaseIO with
  | .ok rc => return rc
  | .error e => note (oneLine e); return 2

end FVA.Tool.Run
