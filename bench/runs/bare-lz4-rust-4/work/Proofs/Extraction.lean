import Proofs.Program

namespace LZ4Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem extraction_exact :
    extractedProgram.map (fun (n, code) => (n, annotate code)) =
    some (24, program) := by
  have h : extractedProgram.map (fun (n, code) => (n, (annotate code).toList)) =
      some (24, program.toList) := by decide +kernel
  have hh := congrArg (Option.map (fun (p : Nat × List Instr) => (p.1, p.2.toArray))) h
  simpa only [Option.map_map, Function.comp_def, Array.toArray_toList, Option.map_some] using hh

end LZ4Verification
