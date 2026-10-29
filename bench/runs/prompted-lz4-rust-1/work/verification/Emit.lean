import Proofs.Results

-- Native evaluation here only transfers the already kernel-checked test vectors
-- to the independent runtime harness. It is not used to prove any theorem.
def main : IO Unit := do
  for c in Results.cases do
    let input := String.intercalate "," (c.input.map toString)
    let out := match c.expected with
      | none => "-"
      | some bs => String.intercalate "," (bs.map toString)
    IO.println s!"{input}|{c.cap}|{out}"
