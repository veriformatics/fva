import FVATest.Basic
import FVA.Tool.Encode
import FVATest.Numeric
import FVATest.FloatDiff
import FVATest.Spec
import FVATest.P2
import FVATest.RawExec
import FVATest.ValidRun
import FVATest.Valid
import FVATest.Trust
import FVATest.Explain
import FVATest.Props
import FVATest.Profile
import FVATest.BaseLines

/-- Runtime checks (no arguments): the lakefile version matches `FVA.version`; the fixed-seed
property tests (`FVATest.Props`, D69).
`reencode <in.wasm> <out.wasm>`: decode, then write the re-encoding (decoder differential, E2).
`numeric <script.json>…`: run numeric test scripts (U3 E1); prints `name pass fail skip`.
`spec <script.json>…`: run execution scripts through `Exec.Ref`, with the same tally format
plus validation-category counts.
`validate <file.wasm>…`: print `file<TAB>valid|invalid|malformed|unsupported` per artifact.
`classify <file.wasm>…`: `file<TAB>p-prime|print-failed|<excluded classes><TAB>memories` (U28a E6).
`profile`: the support manifest `FVA.Profile` as JSON (U28a E7).
`base-lines`: comment-stripped code lines per `FVA/Spec/**` source + total (U28a E8; under
`lake env`).
`floatdiff <dir> <seed> <nBin> <nOther>`: write `f32.wast` + `f64.wast` (U3 E3). -/
def main : List String → IO UInt32
  | ["reencode", src, dst] => do
    let bs ← IO.FS.readBinFile src
    match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m =>
      IO.FS.writeBinFile dst ⟨(FVA.Tool.Encode.module m).toArray⟩
      return 0
    | .error e =>
      IO.eprintln s!"fvatest reencode: {repr e}"
      return 1
  | "validate" :: files => FVA.Test.ValidRun.run files
  | "classify" :: files => FVA.Test.Profile.run files
  | ["base-lines"] => FVA.Test.BaseLines.run
  | ["profile"] => do
    IO.println FVA.Test.Profile.manifest.pretty
    return 0
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
  | "spec" :: scripts => do
    try
      let mut bad := false
      for path in scripts do
        let p : System.FilePath := path
        let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile p))
        let t ← FVA.Test.Spec.runScript (p.parent.getD ".") json
        IO.println s!"{p.fileStem.getD path} {t.pass} {t.fail} {t.skip}"
        IO.println s!"validation {p.fileStem.getD path} {t.validation.summary}"
        for f in t.failures do IO.println s!"  FAIL {f}"
        if (← IO.getEnv "FVA_SPEC_SKIPS") == some "1" then
          for skip in t.skips do IO.println s!"  SKIP {skip}"
        if t.fail > 0 then bad := true
      return if bad then 1 else 0
    catch e =>
      IO.eprintln s!"fvatest spec: {e}"
      return 2
  | "p2" :: scripts => do
    try
      let mut bad := false
      -- steps per command; `FVA_P2_FUEL` raises it for the million-call tail recursions
      let fuel := ((← IO.getEnv "FVA_P2_FUEL").bind String.toNat?).getD 2000000
      for path in scripts do
        let p : System.FilePath := path
        let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile p))
        let t ← FVA.Test.P2.runScript (p.parent.getD ".") json fuel
        IO.println s!"{p.fileStem.getD path} {t.pass} {t.fail} {t.skip}"
        for f in t.failures do IO.println s!"  FAIL {f}"
        if (← IO.getEnv "FVA_SPEC_SKIPS") == some "1" then
          for skip in t.skips do IO.println s!"  SKIP {skip}"
        if t.fail > 0 then bad := true
      return if bad then 1 else 0
    catch e =>
      IO.eprintln s!"fvatest p2: {e}"
      return 2
  | ["floatdiff", dir, seed, nBin, nOther] => do
    FVA.Test.FloatDiff.run dir seed.toNat!.toUInt64 nBin.toNat! nOther.toNat!
    return 0
  | _ => do
    let lake ← IO.FS.readFile "lakefile.toml"
    let want := s!"version = \"{FVA.version}\""
    if (lake.splitOn "\n").contains want then
      IO.println s!"fvatest: ok (version {FVA.version})"
      return ← FVA.Test.Props.run
    IO.eprintln s!"fvatest: lakefile.toml lacks {want}"
    return 1
