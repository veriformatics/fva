import FVA.Spec.Exec.Instantiate

/-!
# Claim vocabulary for compiled exports (reviewed once; contract U8 C1)

How a claim about a C, C++ or Rust function compiled to core Wasm (one C ABI for all of them,
tool-conventions BasicCABI.md) names its calls: from a fresh instance of the import-free module,
optionally after the caller grew memory 0 and wrote bytes into it, the export returns given
values (and leaves given bytes in memory 0), or traps. Integer
arguments travel as `i32`/`i64` values, pointers as `i32` byte addresses into memory 0, arrays as
little-endian elements at a pointer.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- A fresh instance of the import-free module `m`: instantiated into the empty store with no
imports (start function and initializers run), under host semantics `H`. -/
def Instance (m : Module) (H : HostSem) (s : Store) (inst : ModuleInst) : Prop :=
  Instantiated H m {} [] s inst

/-- The import-free module `m` has a successfully initialized fresh instance under every host
semantics (other initialization outcomes stay possible): a claim about every fresh instance is
then never true for want of one. -/
def Instantiable (m : Module) : Prop :=
  ∀ H, ∃ s inst, Instance m H s inst

/-- Export `name` of the import-free module `m`, called on `args` in a fresh instance, returns
exactly `results`: `m` is instantiable, and under every host semantics every execution of the call
ends, none traps. -/
def Returns (m : Module) (name : String) (args results : List Val) : Prop :=
  Instantiable m ∧
    ∀ H s inst, Instance m H s inst → CallReturns H s inst name args fun _ vs => vs = results

/-- Memory 0 of `s` exists and has room for `n` bytes at address `p`. -/
def Fits (s : Store) (p n : Nat) : Prop :=
  ∃ mem, s.mems[0]? = some mem ∧ p + n ≤ mem.size

/-- `mem` after the caller wrote bytes `bs` at address `p` (the rest unchanged). -/
def MemInst.withBytes (mem : MemInst) (p : Nat) (bs : List UInt8) : MemInst :=
  { mem with byte := fun a => if p ≤ a ∧ a < p + bs.length then bs[a - p]! else mem.byte a }

/-- `s` after the caller wrote bytes `bs` into memory 0 at address `p` (a fresh instance's
memory 0 is the store's memory 0). -/
def Store.withBytes (s : Store) (p : Nat) (bs : List UInt8) : Store :=
  { s with mems := s.mems.modify 0 (·.withBytes p bs) }

/-- The little-endian bytes of a 32-bit value. -/
def le32 (x : BitVec 32) : List UInt8 :=
  (List.range 4).map fun k => UInt8.ofNat (x.toNat / 256 ^ k)

/-- An `int32_t`/`uint32_t` array as memory bytes: the elements' little-endian bytes in order. -/
def le32s (xs : List (BitVec 32)) : List UInt8 := xs.flatMap le32

/-- Export `name` of the import-free module `m`, called on `args` after the caller wrote `bs` at
address `p` of a fresh instance's memory, returns exactly `results`: under every host semantics
`m` has a fresh instance with room for `bs` at `p`, and from every such instance every execution
of the call ends, none traps. -/
def ReturnsAfterWrite (m : Module) (p : Nat) (bs : List UInt8) (name : String)
    (args results : List Val) : Prop :=
  (∀ H, ∃ s inst, Instance m H s inst ∧ Fits s p bs.length) ∧
    ∀ H s inst, Instance m H s inst → Fits s p bs.length →
      CallReturns H (s.withBytes p bs) inst name args fun _ vs => vs = results

/-- One step of the caller's preparation of memory 0 before a call, through the embedder's
memory interface: `grow k` grows it by `k` pages (`memory.grow`, §4.5.3.8), `write p bs` writes
bytes `bs` at address `p`. -/
inductive Prep where
  | grow (k : Nat)
  | write (p : Nat) (bs : List UInt8)
  | fill (p n : Nat) (f : Nat → UInt8)

/-- `mem` after `f (a - p)` is placed at each address `a` in `[p, p + n)` (a region memset, the
byte at offset `i` taken from `f i`). -/
def MemInst.fill (mem : MemInst) (p n : Nat) (f : Nat → UInt8) : MemInst :=
  { mem with byte := fun a => if p ≤ a ∧ a < p + n then f (a - p) else mem.byte a }

/-- `s` after the preparation steps `ps` in order; `none` when memory 0 is missing, a growth
fails, or a write/fill does not fit in memory 0. `fill` writes a region from a function (a
constant or periodic pattern, read in O(1)); `write` places explicit bytes. -/
def Store.prep (s : Store) : List Prep → Option Store
  | [] => some s
  | .grow k :: ps =>
    match s.mems[0]?.bind (·.grow k) with
    | some mem => { s with mems := s.mems.set 0 mem }.prep ps
    | none => none
  | .write p bs :: ps =>
    match s.mems[0]? with
    | some mem => if p + bs.length ≤ mem.size then (s.withBytes p bs).prep ps else none
    | none => none
  | .fill p n f :: ps =>
    match s.mems[0]? with
    | some mem => if p + n ≤ mem.size then
        ({ s with mems := s.mems.set 0 (mem.fill p n f) }).prep ps else none
    | none => none

/-- A fresh instance `inst` of the import-free module `m` after the caller's preparation `ps`:
`s` = the store once every step succeeded. -/
def Prepared (m : Module) (H : HostSem) (ps : List Prep) (s : Store) (inst : ModuleInst) : Prop :=
  ∃ s₀, Instance m H s₀ inst ∧ s₀.prep ps = some s

/-- Memory 0 of `s` exists and holds bytes `bs` at address `p`. -/
def Holds (s : Store) (p : Nat) (bs : List UInt8) : Prop :=
  ∃ mem, s.mems[0]? = some mem ∧ p + bs.length ≤ mem.size ∧
    ∀ i, i < bs.length → mem.byte (p + i) = bs[i]!

/-- Export `name` of the import-free module `m`, called on `args` after the caller's preparation
`ps` of a fresh instance, returns exactly `results` and leaves bytes `out` at address `q`: under
every host semantics `m` has such a prepared instance with room for `out` at `q`, and from every
one every execution of the call ends, none traps, the results are `results` and the final
memory 0 holds `out` at `q`. A statement about final contents: a call that leaves bytes already
equal to `out` there satisfies it. -/
def ReturnsOut (m : Module) (ps : List Prep) (name : String) (args results : List Val) (q : Nat)
    (out : List UInt8) : Prop :=
  (∀ H, ∃ s inst, Prepared m H ps s inst ∧ Fits s q out.length) ∧
    ∀ H s inst, Prepared m H ps s inst → Fits s q out.length →
      CallReturns H s inst name args fun s' vs => vs = results ∧ Holds s' q out

/-- Export `name` of the import-free module `m`, called on `args` after the caller's preparation
`ps` of a fresh instance, traps: under every host semantics `m` has such a prepared instance, and
from every one every execution of the call traps. -/
def TrapsAfter (m : Module) (ps : List Prep) (name : String) (args : List Val) : Prop :=
  (∀ H, ∃ s inst, Prepared m H ps s inst) ∧
    ∀ H s inst, Prepared m H ps s inst → CallTraps H s inst name args fun _ => True

end FVA.Wasm.Exec
