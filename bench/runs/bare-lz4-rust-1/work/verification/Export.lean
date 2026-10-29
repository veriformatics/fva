import Proofs.Cases

open Verification Lean

def number (n : Nat) : Json := toJson n
def numbers (ns : List Nat) : Json := toJson ns

def main (args : List String) : IO Unit := do
  let mut failures := 0
  let mut output := #[]
  for c in cases do
    if !c.certify then
      failures := failures + 1
      let s := c.execute
      IO.eprintln s!"FAIL {c.name} src={c.src} dst={c.dst} cap={c.cap}: {repr s.status}, expected={c.returnWord}"
      for a in s.accesses do
        if !Wasm.confined c.src c.dst c.input.length c.cap a then
          IO.eprintln s!"  forbidden access: {repr a}"
      IO.eprintln s!"  output={s.mem.readBytes c.dst c.output.length}; expected={c.output}"
    output := output.push (Json.mkObj
      [("name", toJson c.name), ("src", number c.src), ("dst", number c.dst),
       ("cap", number c.cap), ("input", numbers c.input),
       ("returnWord", number c.returnWord), ("output", numbers c.output)])
  if failures ≠ 0 then throw (IO.userError s!"{failures} failed certificates")
  if args == ["--diagnose"] then
    IO.println s!"PASS: {cases.length} execution certificates"
  else
    IO.println (Json.arr output).compress
