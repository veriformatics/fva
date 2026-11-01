import FVATest.Subjects.Lz4C.Lifted
import FVA.Spec.CAbi

/-! # A call of `LZ4_decompress_safe` on caller-written buffers (vocabulary for `Spec`) -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

/-- Both buffers lie in addresses 131072 to 2097151, each shorter than 2^31 bytes, and they do
not overlap unless one is empty. -/
def Buffers (src dst : Nat) (input initDst : List UInt8) : Prop :=
  131072 ≤ src ∧ src + input.length ≤ 2097152 ∧ 131072 ≤ dst ∧ dst + initDst.length ≤ 2097152 ∧
    input.length < 2 ^ 31 ∧ initDst.length < 2 ^ 31 ∧
    (input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src)

/-- The caller writes `input` at `src` and `initDst` at `dst` into a fresh instance, then calls
`LZ4_decompress_safe(src, dst, input.length, initDst.length)`: such an instance exists, and `P`
holds of every one, given the call's arguments. -/
def OnCall (src dst : Nat) (input initDst : List UInt8)
    (P : HostSem → Store → ModuleInst → List Val → Prop) : Prop :=
  (∀ H, ∃ s inst, Prepared Lifted.module H [.write src input, .write dst initDst] s inst) ∧
    ∀ H s inst, Prepared Lifted.module H [.write src input, .write dst initDst] s inst →
      P H s inst [.i32 (BitVec.ofNat 32 src), .i32 (BitVec.ofNat 32 dst),
        .i32 (BitVec.ofNat 32 input.length), .i32 (BitVec.ofNat 32 initDst.length)]

end Subjects.Lz4C
