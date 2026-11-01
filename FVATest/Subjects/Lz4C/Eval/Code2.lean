import FVATest.Subjects.Lz4C.Eval.MoveFacts

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

def permLocal : Nat → Nat
  | 2 => 3 | 3 => 6 | 5 => 2 | 6 => 5 | i => i

def permInstr : Instr → Instr
  | .localGet i => .localGet (permLocal i)
  | .localSet i => .localSet (permLocal i)
  | .localTee i => .localTee (permLocal i)
  | i => i

def mp1 : List Instr := cp1.map permInstr

def mp4 : List Instr := cp4.map permInstr

def mpBlock : List Instr :=
  [.localGet 2, .iconst .w32 4, .irelop .w32 (.lt .u), .brIf 0,
    .localGet 2, .iconst .w32 4294967292, .ibinop .w32 .and, .localSet 2,
    .iconst .w32 0, .localSet 4, .loop .empty mp4,
    .localGet 6, .itestEqz .w32, .brIf 1]

def mpTail : List Instr :=
  [.localGet 1, .localGet 4, .ibinop .w32 .add, .localSet 3,
    .localGet 0, .localGet 4, .ibinop .w32 .add, .localSet 4, .loop .empty mp1]

def mpForward : List Instr :=
  [.localGet 2, .itestEqz .w32, .brIf 0, .localGet 2,
    .iconst .w32 3, .ibinop .w32 .and, .localSet 6,
    .iconst .w32 0, .localSet 4, .block .empty mpBlock] ++ mpTail

def mb1 : List Instr :=
  [.localGet 6, .localGet 3, .ibinop .w32 .add,
    .localGet 5, .localGet 3, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 3, .iconst .w32 4294967295, .ibinop .w32 .add, .localSet 3,
    .localGet 4, .iconst .w32 4294967295, .ibinop .w32 .add, .localTee 4, .brIf 0]

def mb4 : List Instr :=
  [.localGet 1, .localGet 3, .ibinop .w32 .add, .localTee 4,
    .iconst .w32 3, .ibinop .w32 .add,
    .localGet 6, .localGet 3, .ibinop .w32 .add, .localTee 5,
    .iconst .w32 3, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 4, .iconst .w32 2, .ibinop .w32 .add,
    .localGet 5, .iconst .w32 2, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 4, .iconst .w32 1, .ibinop .w32 .add,
    .localGet 5, .iconst .w32 1, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 4, .localGet 5, .loadPacked .w32 .p8 .u ⟨0, 0⟩,
    .storePacked .w32 .p8 ⟨0, 0⟩,
    .localGet 3, .iconst .w32 4294967292, .ibinop .w32 .add,
    .localTee 3, .brIf 0, .br 2]

def mbRem : List Instr :=
  [.localGet 2, .iconst .w32 3, .ibinop .w32 .and, .localTee 4,
    .itestEqz .w32, .brIf 0, .localGet 1, .iconst .w32 4294967295,
    .ibinop .w32 .add, .localSet 5, .localGet 0, .iconst .w32 4294967295,
    .ibinop .w32 .add, .localSet 6, .localGet 2, .localSet 3, .loop .empty mb1]

def mbInner : List Instr :=
  [.localGet 0, .localGet 1, .irelop .w32 (.lt .u), .brIf 0,
    .localGet 2, .itestEqz .w32, .brIf 1, .localGet 2, .localSet 3,
    .block .empty mbRem, .localGet 2, .iconst .w32 4, .irelop .w32 (.lt .u), .brIf 1,
    .localGet 1, .iconst .w32 4294967292, .ibinop .w32 .add, .localSet 6,
    .localGet 0, .iconst .w32 4294967292, .ibinop .w32 .add, .localSet 1,
    .loop .empty mb4]

def mpOuter : List Instr := [.block .empty mbInner] ++ mpForward

def mpBody : List Instr := [.block .empty mpOuter, .localGet 0]

theorem mpBody_eq : Lifted.func4.body = mpBody := by kernel_rfl

theorem mpLocals_eq : Lifted.func4.locals = [(4, .num .i32)] := by kernel_rfl

end Subjects.Lz4C.Eval
