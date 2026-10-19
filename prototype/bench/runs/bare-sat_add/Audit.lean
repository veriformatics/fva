import Artifacts

/-! Fail on sorryAx, native-evaluation axioms, or any other nonstandard axiom.
The allowlist is Lean's ordinary logical axioms, not project-specific assumptions.
-/

open Lean in
run_meta do
  let targets := #[
    ``SatAdd.input_bounds, ``SatAdd.addition_safe, ``SatAdd.widening_exact,
    ``SatAdd.wideSum_exact, ``SatAdd.narrowing_exact, ``SatAdd.final_cast_safe,
    ``SatAdd.lower_constant_safe, ``SatAdd.R1, ``SatAdd.R2, ``SatAdd.R3,
    ``SatAdd.c_correct, ``SatAdd.all_signed_inputs, ``SatAdd.source_matches,
    ``SatAdd.Wasm.optimized_eq_c, ``SatAdd.Wasm.invoke_program,
    ``SatAdd.Wasm.artifact_decodes, ``SatAdd.Wasm.artifact_eq_c,
    ``SatAdd.Wasm.artifact_R1, ``SatAdd.Wasm.artifact_R2,
    ``SatAdd.Wasm.artifact_R3, ``SatAdd.Wasm.artifact_correct]
  for target in targets do
    let axioms ← collectAxioms target
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {target}"
  logInfo m!"Axiom audit passed for {targets.size} theorems."

#print axioms SatAdd.c_correct
#print axioms SatAdd.Wasm.artifact_correct
