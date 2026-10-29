import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

attribute [local wasm_step] BitVec.reduceEq BitVec.reduceToNat BitVec.reduceOfNat
  BitVec.reduceAnd Num.iadd Num.isub Num.igtU Num.iltU Num.igeU Num.ileU
  Num.ine Num.ieq Num.ieqz Num.ishrU Num.iand Num.bool
  ge_iff_le

private theorem export_decoder : allocation.2.exportFunc "lz4_decompress" = some 7 := rfl

private theorem decoder (mem : MemInst) :
    (codeStore mem).funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩
      allocation.2 Lifted.func7) := rfl


theorem one_literal_holds : one_literal := by
  intro H mem hp hb
  have imem : allocation.2.mems = [0] := rfl
  have smem : (codeStore mem).mems = [mem] := rfl
  have hsize : mem.size = 2097152 := by simp [MemInst.size, hp]
  have hread : mem.read 131072 1 = 16 := by simp [MemInst.read, hb]
  have hdata : mem.read 131073 1 = (mem.byte 131073).toNat := by simp [MemInst.read]
  refine ⟨7, export_decoder, ⟨_, decoder mem, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  wasm_run [decoder, Lifted.func7, imem, smem, hsize, hread, hdata, Val.intBits]
  refine Must.done (o := .returned _ [.i32 1]) ⟨rfl, rfl⟩ ?_
  refine ⟨rfl, mem.write 131104 1 (BitVec.ofNat 32 (mem.byte 131073).toNat).toNat, ?_, ?_, ?_⟩
  · simp only [Store.setMem, smem, List.set_cons_zero, List.getElem?_cons_zero]
  · have hlt : (mem.byte 131073).toNat < 2 ^ 32 :=
      Nat.lt_trans (UInt8.toNat_lt _) (by decide)
    simp [MemInst.write, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · intro a ha
    have hn : ¬ (131104 ≤ a ∧ a < 131104 + 1) := by omega
    simp [MemInst.write, hn]

end Proofs
