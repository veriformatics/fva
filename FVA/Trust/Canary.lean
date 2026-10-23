import Lean
import FVA.Spec.Trust
import FVA.Trust.Replay

/-!
# Kernel canaries (trusted glue, contract F6)

Known-false exports every run-set kernel must refuse, plus positive controls for the kernel
matrix: the pinned set `trust/canaries/set.tsv` (name, sha256, `bad` | `good`), fetched by
`scripts/fetch-canaries` into `.cache/canaries/`. A
file whose bytes miss its sha256 is never run, so its runs stay absent and the coverage rule of
`Pass.checker` fails. Statuses are cached per (kernel binary sha256, invocation, canary sha256)
under `.cache/canaries/results`: a pinned toolchain runs each pair once per machine.
`trust/canaries/known.tsv` (kernel, canary, reason) lists acceptances that are a kernel's
documented design; another run-set kernel must reject each of them.
-/

namespace FVA.Trust

/-- One pinned canary. -/
structure Canary where
  /-- `arena/bad/bugs/constlevels`, `prelude-15704/exploit`, … (path without `.ndjson`). -/
  name : String
  /-- sha256 of the file. -/
  sha256 : String
  /-- Known-false (`bad`) or a positive control (`good`). -/
  bad : Bool

/-- The canary's file (fetched by `scripts/fetch-canaries`). -/
def Canary.path (fvaRoot : System.FilePath) (c : Canary) : System.FilePath :=
  fvaRoot / ".cache" / "canaries" / (c.name ++ ".ndjson")

/-- Fields of each non-empty, non-`#` line of a tab-separated file (absent file = none). -/
def tsvRows (path : System.FilePath) : IO (Array (List String)) := do
  unless ← path.pathExists do return #[]
  return ((← IO.FS.readFile path).splitOn "\n").toArray.filterMap fun l =>
    if l.isEmpty || l.startsWith "#" then none else some (l.splitOn "\t")

/-- The pinned canary set (`trust/canaries/set.tsv`). -/
def defaultCanarySet (fvaRoot : System.FilePath) : System.FilePath :=
  fvaRoot / "trust" / "canaries" / "set.tsv"

/-- The documented acceptances (`trust/canaries/known.tsv`). -/
def defaultKnown (fvaRoot : System.FilePath) : System.FilePath :=
  fvaRoot / "trust" / "canaries" / "known.tsv"

/-- The canaries of a set file. -/
def readCanaries (set : System.FilePath) : IO (Array Canary) := do
  return (← tsvRows set).filterMap fun
    | [name, sha256, kind] => some { name, sha256, bad := kind == "bad" }
    | _ => none

/-- (kernel, canary) pairs whose acceptance is the kernel's documented design. -/
def readKnown (known : System.FilePath) : IO (Array (String × String)) := do
  return (← tsvRows known).filterMap fun
    | k :: c :: _ => some (k, c)
    | _ => none

/-- sha256 of each existing file, by one `sha256sum` call. -/
def sha256Of (paths : Array System.FilePath) : IO (Std.HashMap String String) := do
  let present ← paths.filterM (·.pathExists)
  if present.isEmpty then return {}
  let o ← IO.Process.output { cmd := "sha256sum", args := present.map (·.toString) }
  let mut out := {}
  for l in o.stdout.splitOn "\n" do
    if let [h, p] := l.splitOn "  " then out := out.insert p h
  return out

/-- Status word for the result cache. -/
def Status.word : Status → String
  | .accept => "accept"
  | .reject => "reject"
  | .decline => "decline"
  | .crash => "crash"
  | .timeout => "timeout"

/-- Parse a cached status word. -/
def Status.ofWord? : String → Option Status
  | "accept" => some .accept
  | "reject" => some .reject
  | "decline" => some .decline
  | "crash" => some .crash
  | "timeout" => some .timeout
  | _ => none

/-- One kernel × canary result: status + wall-clock ms (0 when cached without a time). -/
structure CanaryResult where
  kernel : String
  canary : Canary
  status : Status
  ms : Nat

/-- Run every kernel of `ks` on every canary of `cs` whose file matches its sha256 (cached per
sha256 pair; `jobs` runs at a time, `limit` seconds each). A canary with a missing or altered
file yields no result. -/
def runCanaries (fvaRoot : System.FilePath) (ks : List Kernel) (cs : Array Canary)
    (limit jobs : Nat) : IO (Array CanaryResult) := do
  let bins ← ks.toArray.mapM fun k => return (k.name, ← k.path)
  let khash ← sha256Of (bins.map (·.2))
  let chash ← sha256Of (cs.map (·.path fvaRoot))
  let ok := cs.filter fun c => chash.get? (c.path fvaRoot).toString == some c.sha256
  let cache := fvaRoot / ".cache" / "canaries" / "results"
  IO.FS.createDirAll cache
  let todo := ks.toArray.flatMap fun k => ok.map fun c => (k, c)
  IO.FS.withTempDir fun tmp => do
    let mut out := #[]
    for batch in (List.range ((todo.size + jobs - 1) / jobs)).map fun b =>
        todo.extract (b * jobs) (b * jobs + jobs) do
      let tasks ← batch.mapIdxM fun i (k, c) => IO.asTask do
        let bin : System.FilePath := ((bins.find? (·.1 == k.name)).map (·.2)).getD k.bin
        let ksha := (khash.get? bin.toString).getD "missing"
        let cfg := String.ofList (Nat.toDigits 16 (hash k.configId).toNat)
        let entry := cache / s!"{k.name}-{ksha.take 16}-{cfg}-{c.sha256.take 16}"
        if ← entry.pathExists then
          if let [w, ms] := (← IO.FS.readFile entry).trimAscii.toString.splitOn " " then
            if let some st := Status.ofWord? w then
              return { kernel := k.name, canary := c, status := st, ms := ms.toNat?.getD 0 }
        let (st, ms) ← runKernel k bin (c.path fvaRoot) (tmp / s!"nanoda-{i}.json") limit
        -- an unknown kernel binary (no hash) or an undecided run (timeout) is never cached
        if ksha != "missing" && st != .timeout then IO.FS.writeFile entry s!"{st.word} {ms}"
        return ({ kernel := k.name, canary := c, status := st, ms } : CanaryResult)
      for t in tasks do
        out := out.push (← IO.ofExcept (← IO.wait t))
    return out

end FVA.Trust
