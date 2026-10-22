import FVATest.Basic
import FVATest.Encode
import FVATest.Numeric
import FVATest.FloatDiff

/-- Runtime checks (no arguments): the lakefile version matches `FVA.version`.
`reencode <in.wasm> <out.wasm>`: decode, then write the re-encoding (decoder differential, E2).
`numeric <script.json>…`: run numeric test scripts (U3 E1); prints `name pass fail skip`.
`floatdiff <dir> <seed> <nBin> <nOther>`: write `f32.wast` + `f64.wast` (U3 E3). -/
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
  | "numeric" :: scripts => do
    let mut bad := false
    for path in scripts do
      let p : System.FilePath := path
      let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile p))
      let t ← FVA.Test.Numeric.runScript (p.parent.getD ".") json
      IO.println s!"{p.fileStem.getD path} {t.pass} {t.fail} {t.skip}"
      for f in t.failures.toList.take 10 do IO.println s!"  FAIL {f}"
      if t.fail > 0 then bad := true
    return if bad then 1 else 0
  | ["floatdiff", dir, seed, nBin, nOther] => do
    FVA.Test.FloatDiff.run dir seed.toNat!.toUInt64 nBin.toNat! nOther.toNat!
    return 0
  | _ => do
    let lake ← IO.FS.readFile "lakefile.toml"
    let want := s!"version = \"{FVA.version}\""
    if (lake.splitOn "\n").contains want then
      IO.println s!"fvatest: ok (version {FVA.version})"
      return 0
    IO.eprintln s!"fvatest: lakefile.toml lacks {want}"
    return 1
