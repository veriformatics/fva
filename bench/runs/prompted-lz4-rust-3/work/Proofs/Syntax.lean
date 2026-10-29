namespace Wasm

def word : Nat := 4294967296

def leb : Nat → List Nat → Option (Nat × Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: bs =>
    if b < 128 then some (b, 7, bs) else do
      let (v, k, rest) ← leb f bs
      pure (b % 128 + 128 * v, k + 7, rest)

def immediate (bs : List Nat) : Option (Nat × List Nat) := do
  let (v, _, rest) ← leb 6 bs
  pure (v, rest)

def signed (bs : List Nat) : Option (Nat × List Nat) := do
  let (v, k, rest) ← leb 6 bs
  pure (if v < 2^(k-1) then v % word
        else (v % word + word - (2^k % word)) % word, rest)

-- The three components are opcode, first immediate, and second immediate.
def instruction (bs : List Nat) : Option (Nat × Nat × Nat × List Nat) := do
  let op :: rest := bs | none
  if op == 2 || op == 3 then
    let 64 :: rest := rest | none
    pure (op, 0, 0, rest)
  else if [12, 13, 16, 32, 33, 34].contains op then
    let (v, rest) ← immediate rest
    pure (op, v, 0, rest)
  else if op == 65 then
    let (v, rest) ← signed rest
    pure (op, v, 0, rest)
  else if [40, 41, 45, 47, 54, 55, 58, 59].contains op then
    let (align, rest) ← immediate rest
    let (offset, rest) ← immediate rest
    pure (op, offset, align, rest)
  else if op == 252 then
    let (sub, rest) ← immediate rest
    let (m, rest) ← immediate rest
    if m != 0 then none else
      if sub == 10 then
        let (m', rest) ← immediate rest
        if m' == 0 then pure (266, 0, 0, rest) else none
      else if sub == 11 then pure (267, 0, 0, rest) else none
  else if [0, 11, 15, 27, 69, 70, 71, 73, 75, 77, 79, 106, 107, 113, 118].contains op
    then pure (op, 0, 0, rest)
  else none

inductive Instr where
  | prim (op immediate : Nat)
  | block (body : List Instr)
  | loop (body : List Instr)
  deriving Repr

-- The terminating end byte is consumed, including the implicit function end.
def parse : Nat → List Nat → Option (List Instr × List Nat)
  | 0, _ => none
  | f+1, bs => do
    let (op, a, _, rest) ← instruction bs
    if op == 11 then pure ([], rest) else
      let (ins, rest) ←
        if op == 2 || op == 3 then do
          let (body, rest) ← parse f rest
          pure (if op == 2 then Instr.block body else Instr.loop body, rest)
        else pure (Instr.prim op a, rest)
      let (tail, rest) ← parse f rest
      pure (ins :: tail, rest)

end Wasm
