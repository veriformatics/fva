import FVA.Impl.Valid
import FVA.Tool.Decode

namespace FVA.Test.ValidRun

/-- Batch validator boundary: one tab-separated verdict per artifact; undecoded inputs retain
an explicit category so differential checks can report their coverage. -/
def run (files : List String) : IO UInt32 := do
  let mut bad := false
  try
    for file in files do
      let bytes ← IO.FS.readBinFile file
      let verdict := match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bytes) bytes.size with
        | .error (.malformed ..) => "malformed"
        | .error (.unsupported ..) => "unsupported"
        | .ok m => if FVA.Wasm.Valid.validate m then "valid" else "invalid"
      IO.println s!"{file}\t{verdict}"
      if verdict != "valid" then bad := true
    return if bad then 1 else 0
  catch e =>
    IO.eprintln s!"fvatest validate: {e}"
    return 2

end FVA.Test.ValidRun
