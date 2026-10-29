import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def fresh : Store × ModuleInst :=
  (instantiate 10000 {} Lifted.module []).getD ({}, {})


theorem initializes : (instantiate 10000 {} Lifted.module []).isSome = true := by
  decide +kernel


theorem freshInstance (H : HostSem) : Instance Lifted.module H fresh.1 fresh.2 := by
  apply instantiate_sound (fuel := 10000)
  · simp [ImportsMatch, Lifted.module]
  · have h := initializes
    unfold fresh
    cases he : instantiate 10000 {} Lifted.module [] with
    | none => simp [he] at h
    | some a => simp [he]


theorem freshExport : fresh.2.exportFunc "lz4_decompress" = some 7 := by
  decide +kernel


theorem freshSize : (fresh.1.mems[0]?).map MemInst.size = some 2097152 := by
  decide +kernel


theorem freshParams : (fresh.1.funcs[7]?).map (fun fi => fi.type.params) =
    some [.num .i32, .num .i32, .num .i32, .num .i32] := by
  decide +kernel

end Proofs
