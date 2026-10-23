import FVA.Spec.Exec.Instantiate

/-!
# Claim vocabulary for compiled exports (reviewed once; contract U8 C1)

How a claim about a C, C++ or Rust function compiled to core Wasm (one C ABI for all of them,
tool-conventions BasicCABI.md) names its calls: from a fresh instance of the import-free module,
optionally after the caller wrote bytes into memory 0, the export returns given values. Integer
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

end FVA.Wasm.Exec
