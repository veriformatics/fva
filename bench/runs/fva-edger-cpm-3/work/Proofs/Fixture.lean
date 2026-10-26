import Proofs.Lifted
import FVA.Spec.CAbi

/-! Explicit linked-state fixture, not a model of the C arithmetic. Only the two
reachable edgeR functions are installed; both bodies come from the decoded artifact.
Allocation/free are Wasm implementations supplied by this fixture. Full dynamic
loading is exercised independently by verification/reproduce.py. -/
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

def address (i : Nat) : Nat :=
  if i = 12 then 0 else if i = 13 then 1 else if i = 160 then 2
  else if i = 207 then 3 else 4

noncomputable def fixtureInstance : ModuleInst :=
  { types := Lifted.module.types
    funcs := (List.range 246).map address
    mems := [0]
    exports := [{ name := "calc_cpm_raw", value := .func (address 160) }] }

def allocator : Func :=
  { type := 1, locals := [(1, .num .i32)]
    body := [.globalGet 0, .localTee 2, .localGet 0, .localGet 1,
      .ibinop .w32 .mul, .ibinop .w32 .add, .iconst .w32 7, .ibinop .w32 .add,
      .iconst .w32 4294967288, .ibinop .w32 .and, .globalSet 0,
      .localGet 2, .iconst .w32 0, .localGet 0, .localGet 1,
      .ibinop .w32 .mul, .memoryFill, .localGet 2] }

def fixtureMemory (c L : Nat) : MemInst :=
  let m : MemInst := { pages := 2, max := none, byte := fun _ => 0 }
  let m := (m.write 24576 4 25600).write 24584 4 1
  let m := (m.write 24588 4 1).write 24600 4 1
  let m := (m.write 24608 4 25608).write 24616 4 1
  let m := (m.write 24620 4 1).write 24632 4 1
  ((m.write 25600 8 c).write 25608 8 L).write 25616 8 c

noncomputable def fixtureStore (c L : Nat) : Store :=
  { funcs := [
      .wasm ⟨[.num .i32, .num .i32], [.num .i32]⟩
        { mems := [0], globals := [0] } allocator,
      .wasm ⟨[.num .i32], []⟩ {} { type := 3, locals := [], body := [] },
      .wasm ⟨[.num .i32, .num .i32, .num .i32, .num .i32], []⟩
        fixtureInstance (Lifted.module.funcs[86]?.getD { type := 0, locals := [], body := [] }),
      .wasm ⟨[.num .i32, .num .i32, .num .i32], []⟩
        fixtureInstance (Lifted.module.funcs[133]?.getD { type := 0, locals := [], body := [] })]
    mems := [fixtureMemory c L]
    globals := [{ type := ⟨.var, .num .i32⟩, value := .i32 32768 }] }

def fixtureArgs : List Val := [.i32 24576, .i32 24608, .i32 25616, .i32 1]

def outputBits (s : Store) : Nat :=
  ((s.mems[0]?).map (fun m => m.read 25616 8)).getD 0

/-- Binary64 evaluation of the R cutoff expression 10 / 18 * 1e6. -/
def cutoffConfig : Config :=
  ⟨{}, ⟨[], {}⟩, [.plain (.fconst .w64 0x4024000000000000),
    .plain (.fconst .w64 0x4032000000000000), .plain (.fbinop .w64 .div),
    .plain (.fconst .w64 0x412e848000000000), .plain (.fbinop .w64 .mul)]⟩

end Proofs
