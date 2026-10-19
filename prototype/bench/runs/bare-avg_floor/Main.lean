import Artifact

/-- Runtime identity checks guard against stale cached file embeddings.
Run from the repository root. The proofs themselves are in the imported modules. -/
def main : IO Unit := do
  let source ← IO.FS.readFile "avg_floor.c"
  unless source == AvgFloor.Artifact.expectedSource do
    throw (IO.userError "avg_floor.c differs from the proved snapshot; review and reverify")
  let binary ← IO.FS.readBinFile "avg_floor.wasm"
  unless binary.toList.map UInt8.toNat == AvgFloor.Artifact.expectedBytes do
    throw (IO.userError "avg_floor.wasm differs from the proved bytes; review and reverify")
  IO.println "Source and all 64 artifact bytes match the Lean-verified snapshots."
  IO.println "R1 and R2 are REFUTED: avg_floor(INT_MAX, INT_MAX) = -1, expected 2147483647."
  IO.println "Proven: exact all-input behavior; correctness iff the signed sum fits int32."

