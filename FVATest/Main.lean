import FVATest.Basic
import FVATest.Encode

/-- Runtime checks (no arguments): the lakefile version matches `FVA.version`.
`reencode <in.wasm> <out.wasm>`: decode, then write the re-encoding (decoder differential, E2). -/
def main : List String → IO UInt32
  | ["reencode", src, dst] => do
    let bs ← IO.FS.readBinFile src
    match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m =>
      IO.FS.writeBinFile dst ⟨(FVA.Test.Encode.module m).toArray⟩
      return 0
    | .error e =>
      IO.eprintln s!"fvatest reencode: {repr e}"
      return 1
  | _ => do
    let lake ← IO.FS.readFile "lakefile.toml"
    let want := s!"version = \"{FVA.version}\""
    if (lake.splitOn "\n").contains want then
      IO.println s!"fvatest: ok (version {FVA.version})"
      return 0
    IO.eprintln s!"fvatest: lakefile.toml lacks {want}"
    return 1
