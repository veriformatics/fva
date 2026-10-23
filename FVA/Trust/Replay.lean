import Lean
import FVA.Spec.Trust

/-!
# Kernel replay (trusted glue, contract F5)

The bundled exporter writes the closure of the claims, the proofs and the kernel's fixed bundle
from the built `.olean`s; each kernel of the run set reads that export directly. Statuses come
from each kernel's own exit code (0 accept, 1 reject, 2 decline; a signal, a panic or any other
code = crash; the wall limit = timeout): `lake check` would label every nonzero code "rejected".
A declaration that entered the environment without a kernel check is checked here.
-/

namespace FVA.Trust

/-- A kernel binary bundled with the toolchain. -/
structure Kernel where
  /-- Report name. -/
  name : String
  /-- Implementation lineage (`"lean"` = Lean's own kernel family: lean4lean ports its
  inductive types). -/
  lineage : String
  /-- Binary name in the toolchain's `bin/`. -/
  bin : String
  /-- Arguments; `EXPORT` and `CONFIG` are replaced by the paths. -/
  args : List String
  /-- Output that turns an exit code 1 into a decline (the kernel ran out of a resource; it
  never decided the file). -/
  declineOn : List String := []
  /-- An absolute binary path in place of the toolchain's (planted kernels in checks). -/
  binPath : Option String := none

/-- Every bundled kernel (Lake `Check.lean` `bundledKernels` + `leanchecker`). -/
def kernels : List Kernel :=
  [{ name := "leanchecker", lineage := "lean", bin := "leanchecker",
     args := ["--silent", "--from-export", "EXPORT"] },
   { name := "leanchecker-paranoid", lineage := "lean", bin := "leanchecker-paranoid",
     args := ["--silent", "--from-export", "EXPORT"] },
   -- lean4lean (export mode) exits 1 on its own limits, never on a refuted proof: its recursion
   -- limit (FVA's self export, `instrStep_sound`) and constants it needs before the export
   -- introduces them (`Char.ofNat` under a string literal, `Decidable.intro` under `Nat.mod`)
   { name := "lean4lean", lineage := "lean", bin := "lean4lean", args := ["--import", "EXPORT"],
     declineOn := ["deep recursion detected", "unknown constant"] },
   { name := "nanoda", lineage := "nanoda", bin := "nanoda_bin", args := ["CONFIG"] },
   { name := "con-leche", lineage := "con", bin := "con-leche", args := ["EXPORT"] },
   { name := "con-ron", lineage := "con", bin := "con-ron", args := ["EXPORT"] }]

/-- The default run set: Lean's kernel + con-leche, whose default mode carries a machine-checked
guarantee that no file declaring a theorem of `False` is accepted. -/
def defaultKernels : List String := ["leanchecker", "con-leche"]

/-- Status of a kernel exit (`none` = the wall limit hit). -/
def statusOf : Option UInt32 → Status
  | none => .timeout
  | some 0 => .accept
  | some 1 => .reject
  | some 2 => .decline
  | some _ => .crash

/-- Write the export of `decls` (+ their closure) from module `root` to `out`; `true` = ok.
`exportPath` names avoid the `export` keyword. -/
def exportDecls (root : Lean.Name) (decls : Array Lean.Name) (out : System.FilePath) :
    IO Bool := do
  let bin := (← Lean.findSysroot) / "bin" / "leanexport"
  let child ← IO.Process.spawn
    { cmd := "bash",
      args := #["-c", "out=$1; shift; exec \"$@\" >\"$out\"", "_", out.toString, bin.toString,
        root.toString, "--"] ++ decls.map (·.toString),
      stdout := .null, stderr := .null, stdin := .null }
  return (← child.wait) == 0

/-- nanoda's configuration for `exportPath`. `unpermitted_axiom_hard_error`: without it nanoda
skips (never type-checks) an axiom outside `permitted_axioms` and accepts the file, as it does
the arena's `011_nonTypeAxiom` canary; Lake's bundled setup leaves it off. -/
def nanodaConfig (exportPath : String) : Lean.Json := Lean.Json.mkObj
  [("use_stdin", false), ("export_file_path", exportPath),
   ("permitted_axioms", Lean.toJson standardAxioms), ("unpermitted_axiom_hard_error", true),
   ("num_threads", 4), ("nat_extension", true), ("string_extension", true)]

/-- Everything about invoking `k` besides its binary and input (keys cached canary results). -/
def Kernel.configId (k : Kernel) : String :=
  " ".intercalate k.args ++ (if k.args.contains "CONFIG" then (nanodaConfig "EXPORT").compress
    else "") ++ "|" ++ "|".intercalate k.declineOn

/-- The toolchain's binary of `k`. -/
def Kernel.path (k : Kernel) : IO System.FilePath := do
  match k.binPath with
  | some p => return p
  | none => return (← Lean.findSysroot) / "bin" / k.bin

/-- Run kernel binary `bin` (of `k`) on the export within `limit` seconds; status + wall-clock
ms. `config` = where nanoda's configuration file goes (a private path; its output lands
beside it). -/
def runKernel (k : Kernel) (bin exportPath config : System.FilePath) (limit : Nat) :
    IO (Status × Nat) := do
  IO.FS.writeFile config (nanodaConfig exportPath.toString).compress
  let args := k.args.map fun a =>
    if a == "EXPORT" then exportPath.toString else if a == "CONFIG" then config.toString else a
  let t0 ← IO.monoMsNow
  let out := config.withExtension "out"
  let child ← IO.Process.spawn
    { cmd := "bash", args := #["-c", "out=$1; shift; exec \"$@\" >\"$out\" 2>&1", "_",
        out.toString, "timeout", "-k", "10", toString limit, bin.toString] ++ args.toArray,
      stdout := .null, stderr := .null, stdin := .null }
  let rc ← child.wait
  let ms := (← IO.monoMsNow) - t0
  let st := statusOf (if rc == 124 || rc == 137 then none else some rc)
  if st == .reject && !k.declineOn.isEmpty then
    let text ← IO.FS.readFile out
    if k.declineOn.any fun p => (text.splitOn p).length > 1 then return (.decline, ms)
  return (st, ms)

end FVA.Trust
