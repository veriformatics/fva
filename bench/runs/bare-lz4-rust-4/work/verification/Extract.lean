import Proofs.Wasm

open LZ4Verification

def emitTree : Nat → List Instr → String
  | 0, _ => ".empty"
  | fuel+1, xs =>
    match xs with
    | [] => ".empty"
    | [i] => s!"(.leaf ⟨{i.op}, {i.arg}⟩)"
    | _ =>
      let n := xs.length / 2
      s!"(.node {n} {emitTree fuel (xs.take n)} {emitTree fuel (xs.drop n)})"

def main : IO Unit := do
  let some (n, code) := extractedProgram | throw (IO.userError "extraction failed")
  let code := annotate code
  IO.println s!"locals={n}; instructions={code.size}"
  let entries := code.toList.map (fun i => s!"  ⟨{i.op}, {i.arg}⟩,")
  let text := "import Proofs.Wasm\n\nnamespace LZ4Verification\n\n" ++
    "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
    "-- Cached extraction; `extraction_exact` checks it against the full binary.\n" ++
    "def program : Array Instr := #[\n" ++ String.intercalate "\n" entries ++
    "\n]\n\n" ++
    "def programTree : CodeTree :=\n  " ++ emitTree 20 code.toList ++ "\n\n" ++
    s!"def vmProgram : Code := ⟨programTree, {code.size}⟩\n\n" ++
    "theorem program_tree_exact : programTree.toList = program.toList ∧\n" ++
    "    programTree.wellFormed = true ∧ vmProgram.size = program.size := by decide +kernel\n\n" ++
    "end LZ4Verification\n"
  IO.FS.writeFile "Proofs/Program.lean" text
  IO.FS.writeFile "Proofs/Extraction.lean" <|
    "import Proofs.Program\n\nnamespace LZ4Verification\n" ++
    "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
    "theorem extraction_exact :\n" ++
    "    extractedProgram.map (fun (n, code) => (n, annotate code)) =\n" ++
    s!"    some ({n}, program) := by\n" ++
    "  have h : extractedProgram.map (fun (n, code) => (n, (annotate code).toList)) =\n" ++
    s!"      some ({n}, program.toList) := by decide +kernel\n" ++
    "  have hh := congrArg (Option.map (fun (p : Nat × List Instr) => (p.1, p.2.toArray))) h\n" ++
    "  simpa only [Option.map_map, Function.comp_def, Array.toArray_toList, Option.map_some] using hh\n\nend LZ4Verification\n"
