import FVATest.Subjects.Lz4C.Seg

/-! `ErrRet` (the error epilogue, `Seg.lean`) by stepping: `local 4 ← ~v + src`, the end of block
`@1`, the function's last `local.get 4`, the end of its label and frame (proof support; outside
the review surface). -/

namespace Subjects.Lz4C.Cut

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.Lz4C

/-- The code after block `@2` in block `@1`: `local 4 ← (local 4 ^ −1) + local 0`. -/
def epi : List Instr := [.localGet 4, .iconst .w32 4294967295, .ibinop .w32 .xor, .localGet 0,
  .ibinop .w32 .add, .localSet 4]

theorem epi_eq : body1.drop 54 = epi := by kernel_rfl

theorem fn_tail : Lifted.func2.body.drop 3 = [.localGet 4] := by kernel_rfl

theorem xor_neg1 (x : BitVec 32) : x ^^^ 4294967295#32 = ~~~x := by
  rw [show (4294967295#32 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes]

theorem errRet : ErrRet := by
  rintro H st inst src dst n cap v c ⟨ls, hcl, h4, rfl⟩ _ _
  have h0 := hcl.2.1
  have hln := hcl.1
  rw [epi_eq]
  wasm_cstepu [epi, h4]
  · wasm_within [epi]
  wasm_cstepu [epi]
  · wasm_within [epi]
  wasm_cstepu [epi, h0]
  · wasm_within [epi]
  wasm_cstepu [epi]
  · wasm_within [epi]
  wasm_cstepu [epi, show 4 < ls.length by omega]
  · wasm_within [epi]
  rw [ctx1, Context.fill.eq_2, fn_tail]
  wasm_cstepu []
  · wasm_within []
  wasm_cstepu [List.getElem?_set_self (show 4 < ls.length by omega)]
  · wasm_within []
  rw [F0, fnCtx, Context.fill.eq_2]
  wasm_cstepu []
  · wasm_within []
  rw [Context.fill.eq_3]
  wasm_cstepu []
  · wasm_within []
  refine Until.done ?_
  simp only [Context.fill, ixor, iadd, xor_neg1, BitVec.add_def, vals, List.map]

end Subjects.Lz4C.Cut
