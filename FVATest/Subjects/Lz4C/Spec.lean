import FVATest.Subjects.Lz4C.Lifted
import FVATest.Subjects.Lz4.Format
import FVATest.Subjects.Lz4.Any
import FVA.Spec.CAbi

/-! # Requirements for `LZ4_decompress_safe` on the shipped `lz4-c.wasm` -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

/-- R1: For all bytes in disjoint in-range buffers, every call terminates with one `i32` result.
Among addresses 131072 to 2097151, it reads only the input and destination buffers and writes
only the destination buffer. An empty buffer may lie anywhere in range. -/
def r1 : Prop :=
  ∀ (src dst : Nat) (input initDst : List UInt8),
    131072 ≤ src → src + input.length ≤ 2097152 →
    131072 ≤ dst → dst + initDst.length ≤ 2097152 →
    input.length < 2 ^ 31 → initDst.length < 2 ^ 31 →
    (input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) →
    let ps := [Prep.write src input, .write dst initDst]
    let args := [Val.i32 (BitVec.ofNat 32 src), .i32 (BitVec.ofNat 32 dst),
      .i32 (BitVec.ofNat 32 input.length), .i32 (BitVec.ofNat 32 initDst.length)]
    (∀ H, ∃ s inst, Prepared Lifted.module H ps s inst) ∧
      ∀ H s inst, Prepared Lifted.module H ps s inst →
        CallWithin H s inst "LZ4_decompress_safe" args
          (fun _ a => a < 131072 ∨ 2097152 ≤ a ∨
            (src ≤ a ∧ a < src + input.length) ∨ (dst ≤ a ∧ a < dst + initDst.length))
          (fun _ a => a < 131072 ∨ 2097152 ≤ a ∨ (dst ≤ a ∧ a < dst + initDst.length)) ∧
        CallReturns H s inst "LZ4_decompress_safe" args
          (fun _ vs => ∃ result : BitVec 32, vs = [.i32 result])

/-- R2: A valid independent LZ4 block that fits in the destination returns its decoded length
and leaves its decoded bytes there. The destination has at least one byte unless the block is
`[0]`. Both buffers lie in range and are disjoint unless one is empty. -/
def r2 : Prop :=
  ∀ (src dst : Nat) (input initDst : List UInt8),
    131072 ≤ src → src + input.length ≤ 2097152 →
    131072 ≤ dst → dst + initDst.length ≤ 2097152 →
    input.length < 2 ^ 31 → initDst.length < 2 ^ 31 →
    (input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) →
    let ps := [Prep.write src input, .write dst initDst]
    let args := [Val.i32 (BitVec.ofNat 32 src), .i32 (BitVec.ofNat 32 dst),
      .i32 (BitVec.ofNat 32 input.length), .i32 (BitVec.ofNat 32 initDst.length)]
    (∀ H, ∃ s inst, Prepared Lifted.module H ps s inst) ∧
      ∀ H s inst, Prepared Lifted.module H ps s inst →
        ∀ c, Lz4.Valid input c → c.length ≤ initDst.length →
          (1 ≤ initDst.length ∨ input = [0]) →
          CallReturns H s inst "LZ4_decompress_safe" args
            (fun s' vs => vs = [.i32 (BitVec.ofNat 32 c.length)] ∧ Holds s' dst c)

/-- R3: Every call on disjoint in-range buffers terminates with one `i32` result. A nonnegative
result is at most the destination capacity and is the length of decoded bytes left there. The
whole input parses into LZ4 sequences with matches referring only to this block's decoded
prefix. End-of-block conditions need not hold; offset 0 fills its match with bytes of value 0.
An empty buffer may lie anywhere in range. -/
def r3 : Prop :=
  ∀ (src dst : Nat) (input initDst : List UInt8),
    131072 ≤ src → src + input.length ≤ 2097152 →
    131072 ≤ dst → dst + initDst.length ≤ 2097152 →
    input.length < 2 ^ 31 → initDst.length < 2 ^ 31 →
    (input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) →
    let ps := [Prep.write src input, .write dst initDst]
    let args := [Val.i32 (BitVec.ofNat 32 src), .i32 (BitVec.ofNat 32 dst),
      .i32 (BitVec.ofNat 32 input.length), .i32 (BitVec.ofNat 32 initDst.length)]
    (∀ H, ∃ s inst, Prepared Lifted.module H ps s inst) ∧
      ∀ H s inst, Prepared Lifted.module H ps s inst →
        CallReturns H s inst "LZ4_decompress_safe" args (fun s' vs =>
          ∃ result : BitVec 32, vs = [.i32 result] ∧
            (0 ≤ result.toInt → result.toInt ≤ (initDst.length : Int) ∧
              ∃ ss last content, Lz4.ParsesAny input ss last ∧
                (Lz4.decode ss []).map (· ++ last) = some content ∧
                content.length = result.toInt.toNat ∧ Holds s' dst content))

end Subjects.Lz4C
