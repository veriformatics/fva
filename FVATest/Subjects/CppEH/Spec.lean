import FVATest.Subjects.CppEH.Lifted
import FVA.Spec.Wasi.World

/-!
# A C++ function that throws and catches (claim; contract U28g, Decisions: C++ example)

`eh.wasm` = `eh.cpp` built by the pinned wasi-sdk 34.0 with standard Wasm exception handling
(`build`), linked against the stock libc++abi + libunwind runtime. The claim fixes one start:
argument `eh.wasm`, no environment, empty stdin, no preopened directory, the clocks at 0. From it
every launch of the export `eh` on any 32-bit input returns one value, under the reviewed WASI
model restricted to `E`, with fitting growth.
-/

namespace Subjects.CppEH

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- ASCII text as bytes. -/
def ascii (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

/-- The process start: argument `eh.wasm`, no environment, empty stdin, no preopened
directory, every clock at 0. -/
def start : State := State.init [ascii "eh.wasm"] [] [] [] [0, 0, 0, 0]

/-- `eh` launches on every input `x`. From `start`, every launch returns exactly one value: the
successor of `x` modulo 2^32 for an even `x`, and `x` XOR `0xa5a5a5a5` for an odd `x` (the
function throws `x` and catches it). -/
@[fva_claim] def r1 : Prop :=
  ∀ x : BitVec 32, (∃ c mem, Launch Lifted.module "eh" [.i32 x] c mem) ∧
    ∀ c mem, Launch Lifted.module "eh" [.i32 x] c mem →
      SysMust ((world Lifted.module mem).restrict (E Lifted.module mem)) true
        (fun o => ∃ τ s, o = .returned τ s
          [.i32 (if x.toNat % 2 = 0 then x + 1 else x ^^^ 0xa5a5a5a5)]) (start, c)

end Subjects.CppEH
