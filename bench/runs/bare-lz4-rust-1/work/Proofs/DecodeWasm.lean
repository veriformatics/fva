import Proofs.Wasm

/- Independent binary instruction decoder used to check the generated instruction
   array against the raw body. Unsupported instructions are never executed in a
   successful certificate. This decoder accepts only the decoder's opcode set. -/
namespace Wasm

abbrev Reader := StateT (List Nat) Option

def byte : Reader Nat := do
  let x :: xs ← get | failure
  set xs
  pure x

def uleb : Nat → Reader Nat
  | 0 => failure
  | fuel+1 => do
    let b ← byte
    if b < 128 then pure b else return b%128 + 128 * (← uleb fuel)

def sleb : Nat → Reader Int
  | 0 => failure
  | fuel+1 => do
    let b ← byte
    if b < 128 then pure (if b < 64 then (b : Int) else (b : Int)-128)
    else return (b%128 : Nat) + 128 * (← sleb fuel)

def skipLocals : Nat → Reader Nat
  | 0 => pure 0
  | groups+1 => do
    let n ← uleb 5
    let ty ← byte
    guard (ty = 127 ∨ ty = 126)
    return n + (← skipLocals groups)

def immediate : Reader Nat := uleb 5

def decodeOp : Reader Op := do
  let op ← byte
  match op with
  | 0x00 => pure .unreachable
  | 0x02 => guard ((← byte) = 0x40); pure (.block 0)
  | 0x03 => guard ((← byte) = 0x40); pure (.loop 0)
  | 0x0b => pure .end
  | 0x0c => return .br (← immediate)
  | 0x0d => return .brIf (← immediate)
  | 0x0f => pure .ret
  | 0x10 => let _ ← immediate; pure (.unsupported op)
  | 0x1b => pure .select
  | 0x20 => return .get (← immediate)
  | 0x21 => return .set (← immediate)
  | 0x22 => return .tee (← immediate)
  | 0x28 | 0x29 | 0x2d | 0x2f =>
    let _align ← immediate
    let off ← immediate
    pure (.load (if op = 0x28 then 4 else if op = 0x29 then 8
                 else if op = 0x2d then 1 else 2) off)
  | 0x36 | 0x37 | 0x3a | 0x3b =>
    let _align ← immediate
    let off ← immediate
    pure (.store (if op = 0x36 then 4 else if op = 0x37 then 8
                  else if op = 0x3a then 1 else 2) off)
  | 0x41 => return .const ((← sleb 5) % 4294967296).toNat
  | 0x45 => pure .eqz
  | 0x46 => pure .eq
  | 0x47 => pure .ne
  | 0x49 => pure .lt
  | 0x4b => pure .gt
  | 0x4d => pure .le
  | 0x4f => pure .ge
  | 0x6a => pure .add
  | 0x6b => pure .sub
  | 0x71 => pure .band
  | 0x76 => pure .shr
  | 0xfc =>
    let sub ← immediate
    if sub = 10 then
      guard ((← byte) = 0)
      guard ((← byte) = 0)
      pure .copy
    else if sub = 11 then
      guard ((← byte) = 0)
      pure .fill
    else failure
  | _ => failure

def decodeOps : Nat → Array Op → List Nat → Reader (Array Op)
  | 0, _, _ => failure
  | fuel+1, ops, labels => do
    if (← get).isEmpty then
      guard labels.isEmpty
      pure ops
    else
      let op ← decodeOp
      let pc := ops.size
      match op with
      | .block _ | .loop _ => decodeOps fuel (ops.push op) (pc :: labels)
      | .end =>
        match labels with
        | [] =>
          guard (← get).isEmpty
          pure (ops.push op)
        | start :: rest =>
          let isLoop := match ops[start]? with | some (.loop _) => true | _ => false
          decodeOps fuel ((ops.set! start (if isLoop then .loop pc else .block pc)).push op) rest
      | _ => decodeOps fuel (ops.push op) labels

def decodeBody (raw : List Nat) : Option (Nat × Array Op) := do
  let ((n, code), rest) ← (do
    let groups ← immediate
    let n ← skipLocals groups
    let ops ← decodeOps raw.length #[] []
    pure (n, ops)).run raw
  guard rest.isEmpty
  pure (n, code)

end Wasm
