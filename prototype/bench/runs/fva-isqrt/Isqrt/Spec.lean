import FVA.Wasm.Semantics
import Isqrt.Lifted

/-! Requirements for the exact shipped WebAssembly. Products and the candidate `s`
are natural numbers: neither square is a wrapping machine multiplication.
This module imports no proof-support code. -/

namespace Isqrt
open FVA.Wasm

/-- R1: Every unsigned 32-bit input returns the largest natural number whose square
is at most the input. `Returns` also requires a finite, nontrapping execution. -/
def correctness : Prop :=
  ∀ n : BitVec 32, ∃ r : BitVec 32,
    Returns Lifted.module "isqrt" [.i32 n] [.i32 r] ∧
    r.toNat * r.toNat ≤ n.toNat ∧
    ∀ s : Nat, s * s ≤ n.toNat → s ≤ r.toNat

/-- R2: Every unsigned 32-bit input terminates without trapping and returns a value. -/
def termination : Prop :=
  ∀ n : BitVec 32, ∃ r : BitVec 32,
    Returns Lifted.module "isqrt" [.i32 n] [.i32 r]

end Isqrt
