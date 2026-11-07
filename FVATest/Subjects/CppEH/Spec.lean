import FVATest.Subjects.CppEH.Lifted
import FVA.Spec.CAbi

/-! D29: non-binding draft retained until U27+U29b expose the system vocabulary. The selected
claim form is `SysMust` under the declared WASI environment profile `E`, with environment
contents stated, for every input. The stock runtime stays. `Returns` below is import-free
and must be replaced, not proved, once MAIN supplies the exact imported-module/system API. -/

namespace Subjects.CppEH

open FVA.Wasm FVA.Wasm.Exec

/-- For every unsigned 32-bit input, `eh` terminates. An even input returns its successor
modulo 2^32. An odd input throws that value, catches it in the same C++ function, and returns
its bitwise XOR with 0xa5a5a5a5. -/
@[fva_claim] def r1 : Prop :=
  ∀ x : BitVec 32, Returns Lifted.module "eh" [.i32 x]
    [.i32 (if x.toNat % 2 = 0 then x + 1 else x ^^^ 0xa5a5a5a5)]

end Subjects.CppEH
