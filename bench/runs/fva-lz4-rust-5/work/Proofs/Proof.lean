import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Valid.Validator

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

 theorem artifactLayout_holds : artifactLayout := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

 theorem wasmValid_holds : wasmValid := by
  exact FVA.Wasm.Valid.validate_sound (by decide +kernel)

 theorem emptyInputPreservesStore_holds : emptyInputPreservesStore := by
  intro H s inst src dst cap hf
  unfold invokeConfig
  wasm_run [hf, Lifted.func7]
  exact Must.done (o := .returned s [.i32 (-1)]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

end Proofs
