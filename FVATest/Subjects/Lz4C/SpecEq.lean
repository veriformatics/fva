import FVATest.Subjects.Lz4C.Numeric
import FVATest.Subjects.Lz4C.Spec

/-! The decoder claims as stated before the factoring (`Buffers`, `OnCall` in `Call.lean`), spelled
out apart from them, and each factored claim equivalent to its unfactored form (proof side; outside
the spec's import closure). -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

/-- `r1` as the unfactored statement (`Spec.lean` before `Call.lean`). -/
def r1Unfactored : Prop :=
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

/-- `r2` as the unfactored statement (`Spec.lean` before `Call.lean`). -/
def r2Unfactored : Prop :=
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

/-- `r3` as the unfactored statement (`Spec.lean` before `Call.lean`). -/
def r3Unfactored : Prop :=
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

theorem r1_iff : r1 ↔ r1Unfactored := by simp only [r1, r1Unfactored, Buffers, OnCall, and_imp]

theorem r2_iff : r2 ↔ r2Unfactored := by simp only [r2, r2Unfactored, Buffers, OnCall, and_imp]

theorem r3_iff : r3 ↔ r3Unfactored := by simp only [r3, r3Unfactored, Buffers, OnCall, and_imp]

end Subjects.Lz4C
