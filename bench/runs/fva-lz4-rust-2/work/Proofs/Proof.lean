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


theorem zero_input_holds : zero_input := by
  intro H mem src dst cap
  refine ⟨7, export_decoder, ⟨_, decoder mem, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  wasm_run [decoder, Lifted.func7]
  exact Must.done (o := .returned (codeStore mem) [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

theorem empty_block_holds : empty_block := by
  intro H mem hp hb
  have imem : allocation.2.mems = [0] := rfl
  have smem : (codeStore mem).mems = [mem] := rfl
  have hsize : mem.size = 2097152 := by simp [MemInst.size, hp]
  have hread : mem.read 131072 1 = 0 := by simp [MemInst.read, hb]
  refine ⟨7, export_decoder, ⟨_, decoder mem, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  wasm_run [decoder, Lifted.func7, imem, smem, hsize, hread]
  exact Must.done (o := .returned (codeStore mem) [.i32 0]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

theorem zero_offset_holds : zero_offset := by
  intro H mem hp h0 h1 h2
  have imem : allocation.2.mems = [0] := rfl
  have smem : (codeStore mem).mems = [mem] := rfl
  have hsize : mem.size = 2097152 := by simp [MemInst.size, hp]
  have hread : mem.read 131072 1 = 0 := by simp [MemInst.read, h0]
  have hoffset : mem.read 131073 2 = 0 := by simp [MemInst.read, h1, h2]
  refine ⟨7, export_decoder, ⟨_, decoder mem, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  wasm_run [decoder, Lifted.func7, imem, smem, hsize, hread, hoffset]
  exact Must.done (o := .returned (codeStore mem) [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

end Proofs
