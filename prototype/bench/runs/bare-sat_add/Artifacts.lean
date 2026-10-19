import Wasm
import Lean

/-!
Read the repository artifacts during elaboration, then prove facts about the
resulting literals by kernel reduction. This is ordinary file inclusion, not an
axiom, a native_decide proof, or a call to an external verifier.
-/

open Lean Elab Term in
elab "include_binary " path:str : term => do
  let context ← readThe Lean.Core.Context
  let directory := (System.FilePath.mk context.fileName).parent.getD "."
  let bytes ← IO.FS.readBinFile (directory / path.getString)
  return toExpr (bytes.toList.map UInt8.toNat)

namespace SatAdd

def sourceText : String := include_str "sat_add.c"

/-- Fail the check if even a byte of the manually translated C source changes. -/
theorem source_matches : sourceText =
    "/* Saturating addition of 32-bit signed integers. */\nint sat_add(int a, int b) {\n  long long s = (long long)a + b;\n  if (s > 2147483647) return 2147483647;\n  if (s < -2147483647 - 1) return -2147483647 - 1;\n  return (int)s;\n}\n" := by rfl

namespace Wasm

def artifactBytes : List Nat := include_binary "sat_add.wasm"

/-- The on-disk module, including all metadata and immediates, decodes to program. -/
theorem artifact_decodes : decodeModule artifactBytes = some program := by decide

def artifactRun (a b : BitVec 32) : Option (BitVec 32) := do
  let code ← decodeModule artifactBytes
  invoke code a b

/-- Complete symbolic execution of the decoded shipped function, for all inputs. -/
theorem artifact_eq_c (a b : BitVec 32) : artifactRun a b = some (cSatAdd a b) := by
  simp [artifactRun, artifact_decodes, invoke_program, optimized_eq_c]

/-- R1 for the bytes of the shipped WebAssembly module. -/
theorem artifact_R1 (a b : BitVec 32) (h : InInt32 (a.toInt + b.toInt)) :
    (artifactRun a b).map BitVec.toInt = some (a.toInt + b.toInt) := by
  rw [artifact_eq_c, Option.map_some, SatAdd.R1 a b h]

/-- R2 for the bytes of the shipped WebAssembly module. -/
theorem artifact_R2 (a b : BitVec 32) (h : max32 < a.toInt + b.toInt) :
    (artifactRun a b).map BitVec.toInt = some max32 := by
  rw [artifact_eq_c, Option.map_some, SatAdd.R2 a b h]

/-- R3 for the bytes of the shipped WebAssembly module. -/
theorem artifact_R3 (a b : BitVec 32) (h : a.toInt + b.toInt < min32) :
    (artifactRun a b).map BitVec.toInt = some min32 := by
  rw [artifact_eq_c, Option.map_some, SatAdd.R3 a b h]

theorem artifact_correct (a b : BitVec 32) :
    (artifactRun a b).map BitVec.toInt = some (spec a.toInt b.toInt) := by
  rw [artifact_eq_c, Option.map_some, c_correct]

end Wasm
end SatAdd
