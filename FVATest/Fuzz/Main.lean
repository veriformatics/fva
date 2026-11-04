import FVATest.Fuzz

/-- `fvafuzz TARGET FILE…`: each file through the target's entry (D70 replay; a crash input
aborts the run under `LEAN_ABORT_ON_PANIC=1`); prints `FILE<TAB>rc`. rc 2 = usage. -/
def main : List String → IO UInt32
  | target :: files@(_ :: _) => do
    let some f := FVA.Test.Fuzz.entry target
      | IO.eprintln s!"fvafuzz: unknown target {target} (lift | blob | codex)"; return 2
    for file in files do
      IO.println s!"{file}\t{f (← IO.FS.readBinFile file)}"
    return 0
  | _ => do
    IO.eprintln "usage: fvafuzz lift|blob|codex FILE…"
    return 2
