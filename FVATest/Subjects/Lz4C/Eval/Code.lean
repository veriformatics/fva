import FVATest.Subjects.Lz4C.Short
import FVA.Proof.Lib.BlockFacts

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- The one-byte tail of compiled `memcpy`. -/
def cp1 : List Instr :=
  [.localGet 4, .localGet 2, .loadPacked .w32 .p8 .u ⟨0, 0⟩,
    .storePacked .w32 .p8 ⟨0, 0⟩, .localGet 2, .iconst .w32 1, .ibinop .w32 .add,
    .localSet 2, .localGet 4, .iconst .w32 1, .ibinop .w32 .add, .localSet 4,
    .localGet 3, .iconst .w32 4294967295, .ibinop .w32 .add, .localTee 3, .brIf 0]

/-- The four-byte unrolled loop of compiled `memcpy`. -/
def cp4 : List Instr :=
  [.localGet 0, .localGet 4, .ibinop .w32 .add, .localTee 2,
    .localGet 1, .localGet 4, .ibinop .w32 .add, .localTee 6,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 2, .iconst .w32 1, .ibinop .w32 .add,
    .localGet 6, .iconst .w32 1, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 2, .iconst .w32 2, .ibinop .w32 .add,
    .localGet 6, .iconst .w32 2, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 2, .iconst .w32 3, .ibinop .w32 .add,
    .localGet 6, .iconst .w32 3, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 5, .localGet 4, .iconst .w32 4, .ibinop .w32 .add, .localTee 4,
    .irelop .w32 .ne, .brIf 0]

def cpBlock : List Instr :=
  [.localGet 2, .iconst .w32 4, .irelop .w32 (.lt .u), .brIf 0,
    .localGet 2, .iconst .w32 4294967292, .ibinop .w32 .and, .localSet 5,
    .iconst .w32 0, .localSet 4, .loop .empty cp4,
    .localGet 3, .itestEqz .w32, .brIf 1]

def cpOuter : List Instr :=
  [.localGet 2, .itestEqz .w32, .brIf 0, .localGet 2,
    .iconst .w32 3, .ibinop .w32 .and, .localSet 3,
    .iconst .w32 0, .localSet 4, .block .empty cpBlock,
    .localGet 1, .localGet 4, .ibinop .w32 .add, .localSet 2,
    .localGet 0, .localGet 4, .ibinop .w32 .add, .localSet 4,
    .loop .empty cp1]

def cpBody : List Instr := [.block .empty cpOuter, .localGet 0]

theorem cpBody_eq : Lifted.func3.body = cpBody := by kernel_rfl

theorem cpDefaults_eq : Lifted.func3.localDefaults = [vI 0, vI 0, vI 0, vI 0] := by kernel_rfl

theorem cpLocals_eq : Lifted.func3.locals = [(4, .num .i32)] := by kernel_rfl

end Subjects.Lz4C.Eval
