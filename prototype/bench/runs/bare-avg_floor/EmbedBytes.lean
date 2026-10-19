import Lean

/-! Binary analogue of Lean's built-in `include_str`: read the file at
elaboration time and emit a literal list of natural numbers, not an axiom.
Relative paths are resolved against the Lean source file's directory. -/
open Lean Elab Term in
elab "include_bytes " path:str : term => do
  let ctx ← readThe Lean.Core.Context
  let some dir := (System.FilePath.mk ctx.fileName).parent
    | throwError "cannot determine source directory"
  let bytes ← IO.FS.readBinFile (dir / path.getString)
  Lean.Meta.mkListLit (Lean.mkConst ``Nat)
    (bytes.toList.map (fun byte => Lean.mkNatLit byte.toNat))

