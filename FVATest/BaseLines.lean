import Lean
import FVA.Trust.Lines

/-!
# Reviewed-once base size (contract U28a E8)

Comment-stripped code lines of every `FVA/Spec/**` source, counted by `FVA.Trust.codeLines` with
FVA's own token table, as `scripts/make-base-manifest` commits them (`trust/base-lines.tsv`): every
change to the reviewed base shows its size in the diff.
-/

namespace FVA.Test.BaseLines

open Lean

/-- `fvatest base-lines` (under `lake env`): `path<TAB>lines` per spec source, then `total`. -/
def run : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `FVA }] {}
  let files := ((← System.FilePath.walkDir "FVA/Spec").filter (·.extension == some "lean")).qsort
    (·.toString < ·.toString)
  let mut total := 0
  for f in files do
    let n := FVA.Trust.codeLines env (← IO.FS.readFile f)
    total := total + n
    IO.println s!"{f}\t{n}"
  IO.println s!"total\t{total}"
  return 0

end FVA.Test.BaseLines
