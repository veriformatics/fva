import Lean.Data.Json

/-!
# Bounded JSON parsing

Lean's `Json.parse` turns a number's exponent into `10 ^ e` eagerly: `1e9999999999` aborts the
process (`INTERNAL PANIC: Nat.pow exponent is too big`, which no handler catches) and
`1e100000000` builds a 10^8-digit number. FVA parses the JSON it reads (project manifests and
config, saved explanations, `codex app-server` replies) through `parseJson`, which refuses a
larger exponent first (D70: the codex fuzz target's first crash input). `scripts/check-scope`
keeps `Json.parse` out of every other FVA file.
-/

namespace FVA

open Lean

/-- The largest exponent magnitude `parseJson` hands to `Json.parse`. -/
def maxJsonExponent : Nat := 4096

/-- Whether every number outside the strings of `s` has an exponent of magnitude at most
`maxJsonExponent` (a scan, no parse: `true`, `false` and `null` hold no `e` after a digit). -/
def boundedExponents (s : String) : Bool := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  let mut inStr := false
  while i < cs.size do
    let c := cs[i]!
    if inStr then
      if c == '\\' then i := i + 2; continue
      if c == '"' then inStr := false
      i := i + 1
    else if c == '"' then
      inStr := true; i := i + 1
    else if (c == 'e' || c == 'E') && i > 0 && (cs[i - 1]!.isDigit || cs[i - 1]! == '.') then
      let mut j := i + 1
      if j < cs.size && (cs[j]! == '+' || cs[j]! == '-') then j := j + 1
      let mut e := 0
      while j < cs.size && cs[j]!.isDigit do
        e := e * 10 + (cs[j]!.toNat - '0'.toNat)
        if e > maxJsonExponent then return false
        j := j + 1
      i := j
    else i := i + 1
  return true

/-- `Json.parse`, refusing a number exponent over `maxJsonExponent` before parsing. -/
def parseJson (s : String) : Except String Json :=
  if boundedExponents s then Json.parse s
  else .error s!"a JSON number's exponent exceeds {maxJsonExponent}"

end FVA
