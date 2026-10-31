import FVATest.Subjects.Lz4C.Lifted
import FVA.Proof.Lib.Context

/-! Named slices of `LZ4_decompress_safe` (func 2), each read out of `Lifted.func2` by position
(proof support; outside the review surface). Block numbers follow `wasm-tools print`'s labels:
`@1 … @9` enclose the main loop `@5` and the literal-length extension loop. -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

noncomputable def body1 : List Instr := blockCode (Lifted.func2.body.getD 2 .nop)
noncomputable def body2 : List Instr := blockCode (body1.getD 53 .nop)
noncomputable def body3 : List Instr := blockCode (body2.getD 0 .nop)
noncomputable def body4 : List Instr := blockCode (body3.getD 0 .nop)
/-- The main decode loop (`@5`). -/
noncomputable def mainLoop : Instr := body4.getD 0 .nop
noncomputable def body5 : List Instr := loopCode mainLoop
noncomputable def body6 : List Instr := blockCode (body5.getD 4 .nop)
noncomputable def body7 : List Instr := blockCode (body6.getD 0 .nop)
noncomputable def body8 : List Instr := blockCode (body7.getD 0 .nop)
noncomputable def body9 : List Instr := blockCode (body8.getD 3 .nop)
/-- The literal-length extension loop (`read_variable_length`, inlined). -/
noncomputable def extLoop : Instr := body9.getD 3 .nop

/-- One iteration: `p' = p + 1`; exit to `@3` when `p' > lim`; `acc += mem[p]`; exit to `@3` when
`acc` is negative as an `i32`; `p = p'`; repeat while the byte is 255. Locals: 2 = `p`,
4 = `p'`, 14 = `lim`, 15 = the byte, 17 = `acc`. -/
def extBody : List Instr :=
  [.localGet 2, .iconst .w32 1, .ibinop .w32 .add, .localTee 4, .localGet 14,
    .irelop .w32 (.gt .u), .brIf 7, .localGet 17, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 0⟩,
    .localTee 15, .ibinop .w32 .add, .localTee 17, .iconst .w32 0, .irelop .w32 (.lt .s),
    .brIf 7, .localGet 4, .localSet 2, .localGet 15, .iconst .w32 255, .irelop .w32 .eq, .brIf 0]

theorem extLoop_eq : extLoop = .loop .empty extBody := by kernel_rfl

/-- The labels `@9 … @3` around the extension loop (`@9` innermost), each with the code after
it; `C` = the rest (`@2`, `@1`, the function's label and frame, the caller). -/
noncomputable def ctx9 (C : Ref.Context) : Ref.Context :=
  .label 0 [] ((body8.drop 4).map .plain) <|
  .label 0 [] ((body7.drop 1).map .plain) <|
  .label 0 [] ((body6.drop 1).map .plain) <|
  .label 0 [] ((body5.drop 5).map .plain) <|
  .label 0 [mainLoop] ((body4.drop 1).map .plain) <|
  .label 0 [] ((body3.drop 1).map .plain) <|
  .label 0 [] ((body2.drop 1).map .plain) C

/-- The labels `@8 … @3`: where the normal exit continues. -/
noncomputable def ctx8 (C : Ref.Context) : Ref.Context :=
  .label 0 [] ((body7.drop 1).map .plain) <|
  .label 0 [] ((body6.drop 1).map .plain) <|
  .label 0 [] ((body5.drop 5).map .plain) <|
  .label 0 [mainLoop] ((body4.drop 1).map .plain) <|
  .label 0 [] ((body3.drop 1).map .plain) <|
  .label 0 [] ((body2.drop 1).map .plain) C

end Subjects.Lz4C
