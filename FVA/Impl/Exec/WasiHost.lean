import FVA.Spec.Wasi.World
import FVA.Impl.Exec.Process

/-!
# The executable WASI host (U29b H1)

`wasiHost m mem rand` answers a host call of module `m` on machine stores with `E`'s outcome: the
world step `step σ (decode …) {bytes := b}` of the reviewed model, its writes replayed on memory
`mem`'s chunk trie. It leaves unanswered (`none`, fail closed) an id `bind` does not bind, a call
outside the profile domain, `random_get` without bytes (`rand = none`: the driver supplies one
call's bytes through `answerHost`), and a write outside the memory. `FVA.Proof.Wasi.Host`: every
answer is the restricted world's only outcome (`rand = none`) or one of its outcomes (`some`).
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine

/-- The machine store `Launch` instantiates in: `hostStore m`, no memory. -/
def hostMStore (m : Module) : MStore := { base := hostStore m, mems := [] }

/-- `mm` with each `(address, bytes)` of `ws` stored, in order. -/
def writeAll (mm : MMem) (ws : List (Nat × Bytes)) : MMem :=
  ws.foldl (fun mm w => mm.writeBytes w.1 (w.2.map UInt8.toNat)) mm

/-- The random bytes call `c` reads: `rand` for `random_get`, none for the others. -/
def callBytes (c : Call) (rand : Option Bytes) : Option Bytes :=
  if c = .randomGet then rand else some []

/-- Module `m`'s WASI host on machine stores, its calls using memory `mem`, `random_get` answered
with `rand`'s bytes. -/
def wasiHost (m : Module) (mem : Nat) (rand : Option Bytes) (σ : State) (id : Nat) (ms : MStore)
    (vs : List Val) : Option (State × MStore × MHostOut) := do
  let c ← bind m id
  let mm ← ms.mems[mem]?
  let a ← c.args vs
  guard (inProfile σ c ms.abs mem vs)
  let b ← callBytes c rand
  match step σ (decode c mm.abs a) { bytes := b } with
  | (τ, .ok ws) =>
    guard (ws.all fun w => w.1 + w.2.length ≤ mm.size)
    pure (τ, { ms with mems := ms.mems.set mem (writeAll mm ws) }, .returned [.i32 0])
  | (τ, .err e) => pure (τ, ms, .returned [.i32 (BitVec.ofNat 32 e)])
  | (τ, .exit _) => pure (τ, ms, .trapped)

end FVA.Wasi
