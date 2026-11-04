import FVA.Tool.Lift
import FVA.Tool.Blob
import FVA.Tool.Codex
import FVA.Tool.Pack
import FVATest.Fuzz.Mutate
import FVA.Json

/-!
# Fuzz entries (D70): FVA's readers of untrusted bytes, as `fva` runs them

Each entry takes the input bytes and returns 0 (handled) or 1 (cleanly rejected); a panic
(`LEAN_ABORT_ON_PANIC=1`), a stack overflow or a memory blowup is the finding. The decoder's
results are fixed by theorems; the compiled code's depth, memory and time on hostile input are
not, nor is the glue around it. Drivers: `scripts/fuzz-build` (libFuzzer, coverage on FVA's own
modules), `fvafuzz TARGET FILE…` (replay; the gate's `fuzz-replay` step).
-/

namespace FVA.Test.Fuzz

open Lean

/-- `fva lift`: decode, then render the lifted module. -/
@[export fva_fuzz_lift]
def lift (bs : ByteArray) : UInt32 :=
  match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
  | .ok m => if (FVA.Tool.Lift.file "Fuzz" bs m "fuzz.wasm").isEmpty then 1 else 0
  | .error _ => 1

/-- `fva blob` (and `fva certify`, which writes its input and output files through it). -/
@[export fva_fuzz_blob]
def blob (bs : ByteArray) : UInt32 :=
  if (FVA.Tool.Blob.file "Fuzz" bs "fuzz.bin").isEmpty then 1 else 0

/-- `codex app-server` replies as `fva explain` reads them: each line classified, an agent
message's text parsed as the reply JSON. -/
@[export fva_fuzz_codex]
def codex (bs : ByteArray) : UInt32 := Id.run do
  let some text := String.fromUTF8? bs | return 1
  let mut rc := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match FVA.Tool.Codex.Line.parse line with
    | .ok (.message m) =>
      if let some t := FVA.Tool.Codex.agentText m then
        unless (FVA.parseJson t).isOk do rc := 1
    | .ok _ => pure ()
    | .error _ => rc := 1
  return rc

/-- The entry for a target name. -/
def entry : String → Option (ByteArray → UInt32)
  | "lift" => some lift
  | "blob" => some blob
  | "codex" => some codex
  | _ => none

end FVA.Test.Fuzz
