import FVATest.Basic

/-- Runtime checks: the lakefile version matches `FVA.version`. -/
def main : IO UInt32 := do
  let lake ← IO.FS.readFile "lakefile.toml"
  let want := s!"version = \"{FVA.version}\""
  if (lake.splitOn "\n").contains want then
    IO.println s!"fvatest: ok (version {FVA.version})"
    return 0
  IO.eprintln s!"fvatest: lakefile.toml lacks {want}"
  return 1
