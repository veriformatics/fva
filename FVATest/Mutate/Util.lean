import Lean

/-!
# Process + hashing helpers for the mutation runner

`sha256sum` (coreutils) supplies every digest: file contents in batches, strings through
temporary files. Stage commands run under `timeout -k` (it signals the whole process group,
so Lake's `lean` children die with it) in a cleared environment (`env -i`, contract K3).
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

/-- Outcome of a timed command: its exit code, or `none` when the limit was hit. -/
def runTimed (cwd : System.FilePath) (argv : List String) (limitSec : Nat)
    (log : System.FilePath) : IO (Option UInt32) := do
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let home := (← IO.getEnv "HOME").getD "/tmp"
  let args := #["-k", "10", toString limitSec, "env", "-i", s!"PATH={path}", s!"HOME={home}",
    "LANG=C.UTF-8", "bash", "-c", "exec \"$@\" >\"$0\" 2>&1", log.toString] ++ argv.toArray
  let child ← IO.Process.spawn
    { cmd := "timeout", args, cwd, stdin := .null, stdout := .null, stderr := .null }
  let rc ← child.wait
  return if rc == 124 || rc == 137 then none else some rc

/-- Copy `src` to `dst` (reflink where the file system allows), replacing `dst`. -/
def copyTree (src dst : System.FilePath) : IO Unit := do
  if ← dst.pathExists then discard <| runOk "rm" #["-rf", dst.toString]
  discard <| runOk "cp" #["-a", "--reflink=auto", src.toString, dst.toString]

/-- Escape tabs, newlines and backslashes (one TSV cell). -/
def esc (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\t" "\\t" |>.replace "\n" "\\n"

end FVA.Mutate
