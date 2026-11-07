import FVATest.Subjects.Lz4C.Eval.S4
import FVA.Proof.Lib.BlockNumeric

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

def shortCode : List Instr :=
  [.localGet 4, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .localTee 16,
    .iconst .w32 4, .ibinop .w32 (.shr .u), .localTee 2, .iconst .w32 15,
    .irelop .w32 .eq, .brIf 0,
    .block .empty [.localGet 15, .localGet 8, .irelop .w32 (.lt .u), .brIf 0,
      .localGet 15, .localSet 4, .br 2],
    .block .empty [.localGet 3, .localGet 6, .irelop .w32 (.le .u), .brIf 0,
      .localGet 15, .localSet 4, .br 2],
    .localGet 3, .localGet 15, .iconst .w32 16, .call 3, .drop,
    .localGet 3, .localGet 2, .ibinop .w32 .add, .localTee 17,
    .localGet 15, .localGet 2, .ibinop .w32 .add, .localTee 3,
    .loadPacked .w32 .p16 .u ⟨0, 0⟩, .localTee 18, .ibinop .w32 .sub, .localSet 2,
    .localGet 3, .iconst .w32 2, .ibinop .w32 .add, .localSet 4,
    .localGet 16, .iconst .w32 15, .ibinop .w32 .and, .localTee 15,
    .iconst .w32 15, .irelop .w32 .eq, .brIf 2,
    .localGet 18, .iconst .w32 8, .irelop .w32 (.lt .u), .brIf 2,
    .localGet 2, .localGet 1, .irelop .w32 (.lt .u), .brIf 3,
    .localGet 17, .localGet 2, .iconst .w32 8, .call 3, .drop,
    .localGet 17, .iconst .w32 8, .ibinop .w32 .add,
    .localGet 2, .iconst .w32 8, .ibinop .w32 .add,
    .iconst .w32 8, .call 3, .drop,
    .localGet 17, .iconst .w32 16, .ibinop .w32 .add,
    .localGet 2, .iconst .w32 16, .ibinop .w32 .add,
    .iconst .w32 2, .call 3, .drop,
    .localGet 17, .localGet 15, .ibinop .w32 .add, .iconst .w32 4,
    .ibinop .w32 .add, .localSet 3, .br 4]

noncomputable def shortRest5 : List Instr := body5.drop 5
noncomputable def shortRest6 : List Instr := body6.drop 1
noncomputable def shortRest7 : List Instr := body7.drop 1
noncomputable def shortRest8 : List Instr := body8.drop 1

theorem short_main_code : mainLoop = .loop .empty body5 := by kernel_rfl

theorem short_body5 : body5 =
    [.localGet 4, .iconst .w32 1, .ibinop .w32 .add, .localSet 15, .block .empty body6] ++
      shortRest5 := by kernel_rfl

theorem short_body6 : body6 = .block .empty body7 :: shortRest6 := by kernel_rfl

theorem short_body7 : body7 = .block .empty body8 :: shortRest7 := by kernel_rfl

theorem short_body8 : body8 = .block .empty shortCode :: shortRest8 := by kernel_rfl

theorem short_instr_step (st : Store) (f : Frame) (vs : List Val) :
    instrStep st f mainLoop vs =
      some (st, f, vs, [.label 0 [mainLoop] (body5.map .plain)]) := by
  simp [short_main_code, instrStep, BlockType.expand]

theorem short_toVal : toVal (.plain mainLoop) = none := by rw [short_main_code]; rfl

theorem short_unique (vs : List Val) : instrUnique false mainLoop vs = true := by
  rw [short_main_code]; rfl

theorem short_ne_br (k : Nat) : mainLoop ≠ .br k := by rw [short_main_code]; intro h; cases h

theorem short_ne_return : mainLoop ≠ .return_ := by rw [short_main_code]; intro h; cases h

theorem short_access (st : Store) (f : Frame) (vs : List Val) :
    instrAccess st f mainLoop vs = none := by rw [short_main_code]; rfl

end Subjects.Lz4C.Eval
