import Fix.Clean
import Fix.Odd

/-- Prints the values `test.sh` checks. -/
def main : IO Unit :=
  IO.println s!"{Fix.dbl 3} {Fix.slow} {Fix.crashy} {Fix.infra}"
