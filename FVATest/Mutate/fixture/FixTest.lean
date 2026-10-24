import Fix.Clean
import Fix.Odd

#guard 2 ^ ((Fix.panicky - 1) * 2 ^ 64) + Fix.panicky = 2

/-- Prints the values `test.sh` checks. -/
def main : IO Unit :=
  IO.println s!"{Fix.dbl 3} {Fix.slow} {Fix.crashy} {Fix.infra}"
