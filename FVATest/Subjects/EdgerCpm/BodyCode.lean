import FVATest.Subjects.EdgerCpm.BodySupport

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec

def blockCode : Instr → List Instr
  | .block _ code => code
  | _ => []

def loopCode : Instr → List Instr
  | .loop _ code => code
  | _ => []

def thenCode : Instr → List Instr
  | .if_ _ code _ => code
  | _ => []

def elseCode : Instr → List Instr
  | .if_ _ _ code => code
  | _ => []

noncomputable def outerLoop : Instr := Lifted.func86.body.getD 14 .nop
noncomputable def outerCode : List Instr := blockCode ((loopCode outerLoop).getD 0 .nop)
noncomputable def processCode : List Instr := thenCode (outerCode.getD 3 .nop)
noncomputable def rowLoop : Instr := processCode.getD 16 .nop
noncomputable def rowCode : List Instr := loopCode rowLoop
noncomputable def columnLoop : Instr := rowCode.getD 18 .nop
noncomputable def columnCode : List Instr := loopCode columnLoop
noncomputable def cellCode : List Instr := elseCode (columnCode.getD 3 .nop)
noncomputable def freeLoop : Instr := (thenCode (rowCode.getD 3 .nop)).getD 0 .nop

noncomputable def prefixFrame (x : Input) (l : Layout) (inst : ModuleInst) : Frame :=
  ⟨[.i32 0, .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c), .i32 (.ofNat 32 x.m),
    .i32 0, .i32 0, .i32 (.ofNat 32 x.n), .i32 0, .i32 1, .i32 0, .i32 0, .i32 0], inst⟩

noncomputable def tableFrame (x : Input) (l : Layout) (inst : ModuleInst) (t : BitVec 32) :
    Frame :=
  ⟨(prefixFrame x l inst).locals.set 4 (.i32 t), inst⟩

noncomputable def allocatedHead (x : Input) (l : Layout) (inst : ModuleInst)
    (t : BitVec 32) : List AInstr :=
  [.frame 0 ⟨(tableFrame x l inst t).locals.set 0 (.i32 1), inst⟩
    [.label 0 [] ((Lifted.func86.body.drop 14).map .plain)]]

noncomputable def mainFrame (x : Input) (l : Layout) (inst : ModuleInst)
    (t : BitVec 32) (r j : Nat) (p b : BitVec 32) : Frame :=
  ⟨[.i32 (.ofNat 32 j), .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c),
    .i32 (.ofNat 32 r), .i32 t, .i32 p, .i32 (.ofNat 32 x.n), .i32 0, .i32 1,
    .i32 (.ofNat 32 x.n), .i32 (.ofNat 32 x.m), .i32 b], inst⟩

noncomputable def columnHead (tail : List AInstr) : List AInstr :=
  .label 0 [rowLoop] (.plain columnLoop :: (rowCode.drop 19).map .plain) :: tail

end Subjects.EdgerCpm.Body
