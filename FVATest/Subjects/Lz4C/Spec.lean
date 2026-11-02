import FVATest.Subjects.Lz4C.Call
import FVATest.Subjects.Lz4.Format
import FVATest.Subjects.Lz4.Any

/-! # Requirements for `LZ4_decompress_safe` on the shipped `lz4-c.wasm` -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

/-- R1: every call terminates with one `i32` result. Among addresses 131072 to 2097151, it reads
only the input and destination buffers and writes only the destination buffer. -/
@[fva_claim] def r1 : Prop :=
  ∀ src dst input initDst, Buffers src dst input initDst → OnCall src dst input initDst
    fun H s inst args =>
      CallWithin H s inst "LZ4_decompress_safe" args
        (fun _ a => a < 131072 ∨ 2097152 ≤ a ∨
          (src ≤ a ∧ a < src + input.length) ∨ (dst ≤ a ∧ a < dst + initDst.length))
        (fun _ a => a < 131072 ∨ 2097152 ≤ a ∨ (dst ≤ a ∧ a < dst + initDst.length)) ∧
      CallReturns H s inst "LZ4_decompress_safe" args
        (fun _ vs => ∃ result : BitVec 32, vs = [.i32 result])

/-- R2: a valid independent LZ4 block that fits in the destination returns its decoded length
and leaves its decoded bytes there. The destination has at least one byte unless the block is
`[0]`. -/
@[fva_claim] def r2 : Prop :=
  ∀ src dst input initDst, Buffers src dst input initDst → OnCall src dst input initDst
    fun H s inst args => ∀ c, Lz4.Valid input c → c.length ≤ initDst.length →
      (1 ≤ initDst.length ∨ input = [0]) →
      CallReturns H s inst "LZ4_decompress_safe" args
        (fun s' vs => vs = [.i32 (BitVec.ofNat 32 c.length)] ∧ Holds s' dst c)

/-- R3: every call terminates with one `i32` result. A nonnegative result is at most the
destination capacity and is the length of decoded bytes left there. The whole input parses into
LZ4 sequences with matches referring only to this block's decoded prefix. End-of-block conditions
need not hold; offset 0 fills its match with bytes of value 0. -/
@[fva_claim] def r3 : Prop :=
  ∀ src dst input initDst, Buffers src dst input initDst → OnCall src dst input initDst
    fun H s inst args => CallReturns H s inst "LZ4_decompress_safe" args (fun s' vs =>
      ∃ result : BitVec 32, vs = [.i32 result] ∧
        (0 ≤ result.toInt → result.toInt ≤ (initDst.length : Int) ∧
          ∃ ss last content, Lz4.ParsesAny input ss last ∧
            (Lz4.decode ss []).map (· ++ last) = some content ∧
            content.length = result.toInt.toNat ∧ Holds s' dst content))

end Subjects.Lz4C
