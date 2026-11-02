import Lean

/-!
# Process + hashing helpers for the mutation runner

`sha256sum` (coreutils) supplies every digest: file contents in batches, strings through
temporary files. Stage commands run under `timeout -k` (it signals the whole process group,
so Lake's `lean` children die with it) in a cleared environment (`env -i`, contract K3), their
anonymous memory summed over that process group and capped (K7).
-/

namespace FVA.Mutate

/-- Run `cmd args` in `cwd`; stdout, stderr and the exit code. -/
def run (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd }

/-- Run and require exit code 0; stdout. -/
def runOk (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO String := do
  let o ← run cmd args cwd
  if o.exitCode != 0 then
    throw <| IO.userError s!"{cmd} {" ".intercalate args.toList} (rc {o.exitCode}): {o.stderr}"
  return o.stdout

/-- sha256 of each file (paths relative to `root`), in chunks of 200 paths. -/
def sha256Files (root : System.FilePath) (paths : Array String) :
    IO (Std.HashMap String String) := do
  let mut out := {}
  let mut i := 0
  while i < paths.size do
    let chunk := paths.extract i (i + 200)
    let txt ← runOk "sha256sum" (#["--"] ++ chunk) root
    for line in txt.splitOn "\n" do
      if line.length > 66 then
        out := out.insert (line.drop 66).toString (line.take 64).toString
    i := i + 200
  return out

/-- sha256 of each string (a fresh directory per call: worker threads call it concurrently). -/
def sha256Strings (tmp : System.FilePath) (strs : Array String) : IO (Array String) := do
  if strs.isEmpty then return #[]
  let dir := tmp / s!"{← IO.monoNanosNow}-{← IO.rand 0 1000000000}"
  IO.FS.createDirAll dir
  let names := strs.mapIdx fun i _ => s!"s{i}"
  for (n, s) in names.zip strs do IO.FS.writeFile (dir / n) s
  let hs ← sha256Files dir names
  IO.FS.removeDirAll dir
  return names.map fun n => hs.getD n ""

/-- How a timed command ended. -/
inductive Ended where
  | exit (rc : UInt32)
  | timeout
  /-- The process group's anonymous memory passed the cap; the group was killed. -/
  | memory

/-- Anonymous resident memory (KiB) summed over the processes of group `pg`: file-backed pages
(the `.olean`s every `lean` maps, 1.5–2.7 GB each) stay out, the heap a growth mutant fills
counts. -/
def groupAnonKiB (pg : Nat) : IO Nat := do
  let mut kib := 0
  for e in ← System.FilePath.readDir "/proc" do
    let some pid := e.fileName.toNat? | continue
    let some stat ← (try some <$> IO.FS.readFile s!"/proc/{pid}/stat" catch _ => pure none)
      | continue
    -- the process group is field 5, after the parenthesized command name (it may hold spaces)
    let some pgrp := ((stat.splitOn ") ").getLast!.splitOn " ")[2]?.bind (·.toNat?) | continue
    if pgrp != pg then continue
    let some st ← (try some <$> IO.FS.readFile s!"/proc/{pid}/status" catch _ => pure none)
      | continue
    for l in st.splitOn "\n" do
      if l.startsWith "RssAnon:" then
        kib := kib + (((l.drop 8).trimAscii.toString.splitOn " ")[0]!.toNat?.getD 0)
  return kib

/-- Run `argv` under `limitSec` seconds and `memMiB` MiB of anonymous memory for its whole
process group (`timeout` leads that group; 0 = no memory cap), sampled every 200 ms. -/
def runTimed (cwd : System.FilePath) (argv : List String) (limitSec memMiB : Nat)
    (log : System.FilePath) : IO Ended := do
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let home := (← IO.getEnv "HOME").getD "/tmp"
  let args := #["-k", "10", toString limitSec, "env", "-i", s!"PATH={path}", s!"HOME={home}",
    "LANG=C.UTF-8", "bash", "-c", "exec \"$@\" >\"$0\" 2>&1", log.toString] ++ argv.toArray
  let child ← IO.Process.spawn
    { cmd := "timeout", args, cwd, stdin := .null, stdout := .null, stderr := .null }
  let ended (rc : UInt32) : Ended := if rc == 124 || rc == 137 then .timeout else .exit rc
  if memMiB == 0 then return ended (← child.wait)
  let pg := child.pid.toNat
  while true do
    if let some rc ← child.tryWait then return ended rc
    if (← groupAnonKiB pg) > memMiB * 1024 then
      discard <| run "bash" #["-c", s!"kill -KILL -- -{pg}"]
      discard child.wait
      return .memory
    IO.sleep 200
  return .timeout

/-- Copy `src` to `dst` (reflink where the file system allows), replacing `dst`. -/
def copyTree (src dst : System.FilePath) : IO Unit := do
  if ← dst.pathExists then discard <| runOk "rm" #["-rf", dst.toString]
  discard <| runOk "cp" #["-a", "--reflink=auto", src.toString, dst.toString]

/-- Escape tabs, newlines and backslashes (one TSV cell). -/
def esc (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\t" "\\t" |>.replace "\n" "\\n"

end FVA.Mutate
