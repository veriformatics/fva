import FVA.Spec.CAbi
import Proofs.Lifted

/-! Claims: `Prop`-valued definitions about the artifact, read by a reviewer. Import only
FVA's specs and the lifted artifact here; proofs go to `Proof.lean`. -/

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec

/-- A concrete wasm32 execution environment for the two functions exercised below.
Function indices keep their artifact values. Only the two allocator imports are
implemented here; both allocation requests have fresh, initially zero storage.
This is a function-execution harness, not a proof of dynamic linking or startup. -/
noncomputable def testInst : ModuleInst :=
  { types := Lifted.module.types, funcs := List.range 246, mems := [0],
    exports := [⟨"calc_cpm_raw", .func 160⟩] }

/-- On this test's two allocation requests, return 32848 (4 bytes) or 32856 (8 bytes).
They are aligned, disjoint, zero-initialized and outside the input buffers. -/
def testAlloc : Func :=
  { type := 1, locals := [], body :=
    [.localGet 1, .iconst .w32 4, .irelop .w32 .eq,
     .if_ (.val (.num .i32)) [.iconst .w32 32848] [.iconst .w32 32856]] }

/-- Free has no observable effect for this terminating two-allocation execution. -/
def testFree : Func := { type := 3, locals := [], body := [] }

/-- A one-row, one-column matrix view at 32768, a scalar library view at 32800,
and cpm at 32832 and library data at 32840, both initially 2^1023 (bits 0x7fe0000000000000).
All other bytes, including both allocation regions, initially zero. -/
def testByte (a : Nat) : UInt8 :=
  if a = 32776 ∨ a = 32780 ∨ a = 32792 ∨ a = 32808 ∨ a = 32812 ∨ a = 32824 then 1
  else if a = 32769 ∨ a = 32801 then 128
  else if a = 32768 then 64
  else if a = 32800 then 72
  else if a = 32816 then 3
  else if a = 32838 ∨ a = 32846 then 224
  else if a = 32839 ∨ a = 32847 then 127
  else 0

/-- The exact decoded function bodies at addresses 160 and 207, with the
test allocator/free at the artifact's import addresses 12 and 13.
Other function slots are unreachable in this execution. -/
noncomputable def testStore : Store :=
  { funcs := (List.range 246).map fun n =>
      if n = 12 then .wasm ⟨[.num .i32, .num .i32], [.num .i32]⟩ testInst testAlloc
      else if n = 13 then .wasm ⟨[.num .i32], []⟩ testInst testFree
      else if n = 160 then .wasm ⟨List.replicate 4 (.num .i32), []⟩ testInst Lifted.func86
      else if n = 207 then .wasm ⟨List.replicate 3 (.num .i32), []⟩ testInst Lifted.func133
      else .host ⟨[], []⟩ n,
    mems := [⟨1, none, testByte⟩] }

/-- R1 counterexample on the artifact's complete calc_cpm_raw and get_row
bodies: with c=L=2^1023, all executions in this test environment terminate
without a trap and write positive infinity to cpm[0]. The export and both
function bodies are also checked against the byte-bound decoded module.
The exact mathematical answer is 1000000; hence there is no finite absolute
or relative error bound over all of R1's stated domain. -/
def r1_overflow : Prop :=
  (∃ e ∈ Lifted.module.exports, e.name = "calc_cpm_raw" ∧ e.desc = .func 160) ∧
  Lifted.module.funcs[86]? = some Lifted.func86 ∧
  Lifted.module.funcs[133]? = some Lifted.func133 ∧
  ∀ H, CallReturns H testStore testInst "calc_cpm_raw"
    [.i32 32768, .i32 32800, .i32 32832, .i32 1] fun s vs =>
      vs = [] ∧ ∃ m, s.mems[0]? = some m ∧ (List.range 8).map (fun k => m.byte (32832 + k)) = [0, 0, 0, 0, 0, 0, 240, 127]

end Proofs
