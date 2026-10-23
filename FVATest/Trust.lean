import FVA.Trust.Collect
import FVA.Trust.Replay
import FVA.Trust.Canary
import FVA.Trust.Verdict

/-!
# Trust glue checks (U7; built by `scripts/test-trust`)

The collector's pure parts by `#guard`, its file-system parts by `#eval` in temporary
directories (an exception fails the build). Outside `FVATest.Main` on purpose: the files of
`fvatest`'s dispatch enter every U12 test-kill digest.
-/

namespace FVA.Trust.Check

open FVA.Trust Lean

/-! ## Code lines (D11): comments + docstrings out; string, char and `«…»` contents in -/

#guard codeLines "def s := \"--x\"" == 1
#guard codeLines "-- comment" == 0
#guard codeLines "/- c -/ def x := 1" == 1
#guard codeLines "/- multi\nline -/ def y := 2" == 1
#guard codeLines "/- c\n-/ def hidden : Prop := False" == 1
#guard codeLines "/-- doc -/" == 0
#guard codeLines "/-! module doc\n  def notCode := 1\n-/" == 0
#guard codeLines "/- /- nested -/ still a comment -/" == 0
#guard codeLines "def c := '\"' -- quote char" == 1
#guard codeLines "def h' := 1 -- prime" == 1
#guard codeLines "def α' := '-'" == 1
#guard codeLines "def r := r#\"a \"-- b\"#" == 1
#guard codeLines "def m := \"a\n-- not a comment\nb\"" == 3
#guard codeLines "def q := \"a\\\"--\" -- c" == 1
#guard codeLines "def e := '\\''  /- c\n -/ x" == 2
#guard codeLines "def «a--b» := 1" == 1
#guard codeLines "\n\n  \n" == 0

/-! ## Report text (E4): status words, link faults in check order, the canary count, axioms -/

#guard [Status.accept, .reject, .decline, .crash, .timeout].map Status.name ==
  ["accepted", "rejected", "declined", "crashed", "timed out"]
#guard Link.problems ⟨"L.lean", .wasm, true, true, true, true, true⟩ == []
#guard Link.problems ⟨"L.lean", .wasm, false, false, false, false, false⟩ ==
  ["the file is missing or outside the project", "`bytes` is not the file's bytes",
   "`len` is not the file's size", "`decode_eq` is missing or mistyped",
   "the module is not its generator's output for the file"]
#guard (ruleChecker { (default : Report) with
    canarySet := ["a", "b", "c"], replay := [⟨"k", "lean", .accept⟩],
    canaries := [⟨"k", "a", .reject, false⟩] }).map (·.detail) ==
  ["k did not decide 2 pinned canaries (first: b; missing file: scripts/fetch-canaries; " ++
   "timeout: --canary-limit)"]
#guard (ruleAxiom { (default : Report) with
    claims := [⟨"c", false, [⟨"p", ["propext", "Classical.choice", "Quot.sound", "sorryAx"]⟩],
      ["S"]⟩] }).map (·.detail) == ["p (proof of c) depends on sorryAx"]

/-! ## Link kinds (U9): a blob has no `decode_eq`; every other part counts as for a lifted module -/

#guard Link.problems ⟨"B.lean", .blob, true, true, true, false, true⟩ == []
#guard Link.problems ⟨"B.lean", .blob, false, false, false, false, false⟩ ==
  ["the file is missing or outside the project", "`bytes` is not the file's bytes",
   "`len` is not the file's size", "the module is not its generator's output for the file"]
#guard (⟨"B.lean", .blob, true, true, true, false, true⟩ : Link).ok
#guard !(⟨"L.lean", .wasm, true, true, true, false, true⟩ : Link).ok
#guard Link.problems ⟨"L.lean", .wasm, true, true, true, false, true⟩ ==
  ["`decode_eq` is missing or mistyped"]

/-- Write a Lake manifest pinning `pkgs` (name, url, rev) under packages directory `dir`. -/
def writeManifest (root : System.FilePath) (dir : String)
    (pkgs : List (String × String × String)) : IO Unit := do
  IO.FS.createDirAll root
  let ps := pkgs.map fun (name, url, rev) =>
    Json.mkObj [("type", "git"), ("name", name), ("url", url), ("rev", rev)]
  IO.FS.writeFile (root / "lake-manifest.json")
    (Json.mkObj [("packagesDir", dir), ("packages", Json.arr ps.toArray)]).compress

/-- Check out package `name` under `root/dir` with `.git/HEAD` = `head`. -/
def checkout (root : System.FilePath) (dir name head : String) : IO Unit := do
  IO.FS.createDirAll (root / dir / name / ".git")
  IO.FS.writeFile (root / dir / name / ".git" / "HEAD") (head ++ "\n")

/-- Fail the build unless `got = want`. -/
def expect {α : Type} [BEq α] [ToString α] (what : String) (got want : α) : IO Unit :=
  unless got == want do throw <| .userError s!"{what}: got {got}, want {want}"

-- Mathlib origin (F2): only packages pinned exactly as FVA pins them, checked out at that pin
#eval show IO Unit from IO.FS.withTempDir fun tmp => do
  let fva := tmp / "fva"
  writeManifest fva ".lake/packages"
    [("mathlib", "u/m", "a1"), ("batteries", "u/b", "b1"), ("aesop", "u/a", "c1"),
     ("Qq", "u/q", "d1")]
  let proj := tmp / "proj"
  writeManifest proj ".lake/packages"
    [("mathlib", "u/m", "a1"), ("batteries", "u/b", "b2"), ("aesop", "u/a", "c1"),
     ("Qq", "u/fork", "d1"), ("evil", "u/e", "e1")]
  for (name, head) in [("mathlib", "a1"), ("batteries", "b2"), ("aesop", "c2"), ("Qq", "d1"),
      ("evil", "e1")] do
    checkout proj ".lake/packages" name head
  let root ← IO.FS.realPath proj
  -- re-pinned (batteries), checked out elsewhere (aesop), forked (Qq), unknown (evil): project
  expect "trusted packages" (← trustedPackages root fva)
    #[root / ".lake" / "packages" / "mathlib"]
  -- the manifest's own packages directory is honored
  let proj2 := tmp / "proj2"
  writeManifest proj2 "deps" [("mathlib", "u/m", "a1")]
  checkout proj2 "deps" "mathlib" "a1"
  let root2 ← IO.FS.realPath proj2
  expect "custom packagesDir" (← trustedPackages root2 fva) #[root2 / "deps" / "mathlib"]

-- Link artifact path (F4): relative, no `..`, inside the project after symlinks
#eval show IO Unit from IO.FS.withTempDir fun tmp => do
  let proj := tmp / "proj"
  IO.FS.createDirAll (proj / "sub")
  IO.FS.writeFile (proj / "a.wasm") ""
  IO.FS.writeFile (tmp / "outside.wasm") ""
  let ln ← IO.Process.output
    { cmd := "ln", args := #["-s", (tmp / "outside.wasm").toString, (proj / "link.wasm").toString] }
  expect "ln rc" ln.exitCode 0
  let root ← IO.FS.realPath proj
  let ok (src : String) : IO Bool := return (← artifactPath root src).isSome
  expect "a.wasm" (← ok "a.wasm") true
  expect "absent file (reported absent later)" (← ok "missing.wasm") true
  expect "parent escape" (← ok "../outside.wasm") false
  expect "dot-dot inside" (← ok "sub/../a.wasm") false
  expect "absolute" (← ok (tmp / "outside.wasm").toString) false
  expect "symlink escape" (← ok "link.wasm") false

-- Replay statuses (F5): exit codes, plus a kernel's resource messages turning rc 1 into decline
#eval show IO Unit from IO.FS.withTempDir fun tmp => do
  let fake (name body : String) : IO System.FilePath := do
    let p := tmp / name
    IO.FS.writeFile p s!"#!/bin/sh\n{body}\n"
    let _ ← IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
    return p
  let k : Kernel :=
    { name := "k", lineage := "lean", bin := "k", args := ["EXPORT"],
      declineOn := ["deep recursion detected"] }
  let st (bin : System.FilePath) : IO Status := return (← runKernel k bin "x" (tmp / "c.json") 30).1
  expect "rc 0" (repr (← st (← fake "ok" "exit 0"))).pretty "FVA.Trust.Status.accept"
  expect "rc 1" (repr (← st (← fake "no" "echo 'type mismatch' >&2; exit 1"))).pretty
    "FVA.Trust.Status.reject"
  expect "rc 1 + resource message" (repr (← st (← fake "deep"
    "echo '(kernel) deep recursion detected, use set_option' >&2; exit 1"))).pretty
    "FVA.Trust.Status.decline"
  expect "rc 2" (repr (← st (← fake "dec" "exit 2"))).pretty "FVA.Trust.Status.decline"
  expect "panic" (repr (← st (← fake "panic" "exit 101"))).pretty "FVA.Trust.Status.crash"
  expect "signal" (repr (← st (← fake "sig" "kill -SEGV $$"))).pretty "FVA.Trust.Status.crash"
  let slow : Kernel := { k with declineOn := [] }
  let (slept, _) ← runKernel slow (← fake "slow" "sleep 30") "x" (tmp / "s.json") 1
  expect "timeout" (repr slept).pretty "FVA.Trust.Status.timeout"

-- Canary runs (F6): a decided status is cached per sha256 pair, a timeout never is
#eval show IO Unit from IO.FS.withTempDir fun root => do
  IO.FS.createDirAll (root / ".cache" / "canaries" / "t")
  IO.FS.writeFile (root / ".cache" / "canaries" / "t" / "c.ndjson") "canary"
  let csha := ((← sha256Of #[root / ".cache" / "canaries" / "t" / "c.ndjson"]).toList.head!).2
  let c : Canary := { name := "t/c", sha256 := csha, bad := true }
  let mk (name body : String) : IO Kernel := do
    let p := root / name
    IO.FS.writeFile p s!"#!/bin/sh\n{body}\n"
    let _ ← IO.Process.output { cmd := "chmod", args := #["+x", p.toString] }
    return { name, lineage := "lean", bin := name, args := ["EXPORT"], binPath := p.toString }
  let rejects ← mk "rejects" "exit 1"
  let slow ← mk "slow" "sleep 30"
  let altered : Canary := { c with sha256 := String.ofList (List.replicate 64 '0') }
  let rs ← runCanaries root [rejects, slow] #[c, altered] 1 4
  expect "results (the altered canary never runs)" rs.size 2
  let statusOf (k : String) : String :=
    ((rs.find? (·.kernel == k)).map fun x => (repr x.status).pretty).getD "none"
  expect "reject" (statusOf "rejects") "FVA.Trust.Status.reject"
  expect "timeout" (statusOf "slow") "FVA.Trust.Status.timeout"
  let cached ← (root / ".cache" / "canaries" / "results").readDir
  expect "cache entries (the timeout uncached)" cached.size 1

end FVA.Trust.Check
