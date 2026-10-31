import FVATest.Subjects.Lz4C.O1.Lifted
import FVATest.Subjects.Lz4C.Ext

/-!
# Checkpoint 1, perturbation M4: the same loop in an `-O1` build (contract U19)

`lz4-c-O1.wasm` = `bench/subjects/wasm/lz4-c.wasm`'s sources and flags with `-O1` for `-O2`.
`ExtL1O1` = `ExtL1`'s statement re-bound to this code: the loop keeps `q = p + 1` (pre-incremented,
reading `q − 1`), both guards leave the loop's block for an error path that sets local 17 to −1,
and the normal exit branches past it. Bytes, partial sums, bounds and footprint are `ExtL1`'s.
-/

namespace Subjects.Lz4C.O1

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

noncomputable def b1 : List Instr := blockCode (Lifted.func2.body.getD 2 .nop)
noncomputable def b2 : List Instr := blockCode (b1.getD 48 .nop)
noncomputable def b3 : List Instr := blockCode (b2.getD 0 .nop)
noncomputable def b4 : List Instr := loopCode (b3.getD 0 .nop)
noncomputable def b5 : List Instr := blockCode (b4.getD 7 .nop)
noncomputable def b6 : List Instr := blockCode (b5.getD 0 .nop)
noncomputable def b7 : List Instr := blockCode (b6.getD 0 .nop)
noncomputable def b8 : List Instr := blockCode (b7.getD 0 .nop)
noncomputable def b9 : List Instr := blockCode (b8.getD 0 .nop)
noncomputable def b10 : List Instr := blockCode (b9.getD 0 .nop)
noncomputable def b11 : List Instr := blockCode (b10.getD 0 .nop)
noncomputable def b12 : List Instr := blockCode (b11.getD 1 .nop)
noncomputable def b13 : List Instr := blockCode (b12.getD 18 .nop)
noncomputable def extLoop : Instr := b13.getD 0 .nop

/-- One iteration: locals 18 = `q`, 19 = `acc`, 14 = `lim`; 4 = `acc` then `acc + byte`, 3 = `q`,
20 = the byte read at `q − 1`, 16/17 = the pointer and sum handed on. -/
def extBody : List Instr :=
  [.localGet 19, .localSet 4, .localGet 18, .localTee 3, .localGet 14, .irelop .w32 (.gt .u),
    .brIf 1, .localGet 4, .localGet 3, .iconst .w32 4294967295, .ibinop .w32 .add,
    .loadPacked .w32 .p8 .u ⟨0, 0⟩, .localTee 20, .ibinop .w32 .add, .localTee 4,
    .iconst .w32 0, .irelop .w32 (.lt .s), .brIf 1, .localGet 3, .iconst .w32 1,
    .ibinop .w32 .add, .localSet 18, .localGet 4, .localSet 19, .localGet 3, .localSet 16,
    .localGet 4, .localSet 17, .localGet 20, .iconst .w32 255, .irelop .w32 .eq, .brIf 0, .br 2]

theorem extLoop_eq : extLoop = .loop .empty extBody := by kernel_rfl

/-- The two blocks around the loop: the one holding it (its error path after it) and the one
the normal exit leaves; `C` = the rest. -/
noncomputable def ctx (C : Context) : Context :=
  .label 0 [] ((b12.drop 19).map .plain) <| .label 0 [] ((b11.drop 2).map .plain) C

/-- `f'` = entry locals `ls`, except the listed ones (`none` = unchanged). -/
def LocalsAt (ls : List Val) (inst : ModuleInst) (f' : Frame) (u : List (Nat × Option Nat)) :
    Prop :=
  f'.inst = inst ∧ f'.locals.length = ls.length ∧
  ∀ i, f'.locals[i]? = match u.lookup i with
    | some v => v.map vI <|> ls[i]?
    | none => ls[i]?

/-- The loop's exits. -/
def ExtExit (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (p lim acc : Nat)
    (b : Nat → UInt8) (c : Config) : Prop :=
  (∃ k f', (∀ j < k, b j = 255) ∧ b k ≠ 255 ∧ p + k + 1 ≤ lim ∧ (∀ i ≤ k, psum acc b i < 2 ^ 31) ∧
    LocalsAt ls inst f' [(18, some (p + k + 2)), (19, some (psum acc b k)),
      (4, some (psum acc b k)), (3, some (p + k + 1)), (20, some (b k).toNat),
      (16, some (p + k + 1)), (17, some (psum acc b k))] ∧
    c = C.fill ⟨s, f', (b11.drop 2).map .plain⟩) ∨
  (∃ k f', (∀ j < k, b j = 255) ∧ lim < p + k + 1 ∧ (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
    LocalsAt ls inst f' [(18, some (p + k + 1)),
      (19, some (if k = 0 then acc else psum acc b (k - 1))),
      (4, some (if k = 0 then acc else psum acc b (k - 1))), (3, some (p + k + 1)),
      (20, if k = 0 then none else some (b (k - 1)).toNat),
      (16, if k = 0 then none else some (p + k)),
      (17, if k = 0 then none else some (psum acc b (k - 1)))] ∧
    c = (Context.label 0 [] ((b11.drop 2).map .plain) C).fill ⟨s, f', (b12.drop 19).map .plain⟩) ∨
  (∃ k f', (∀ j < k, b j = 255) ∧ p + k + 1 ≤ lim ∧ (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
    2 ^ 31 ≤ psum acc b k ∧
    LocalsAt ls inst f' [(18, some (p + k + 1)),
      (19, some (if k = 0 then acc else psum acc b (k - 1))), (4, some (psum acc b k)),
      (3, some (p + k + 1)), (20, some (b k).toNat),
      (16, if k = 0 then none else some (p + k)),
      (17, if k = 0 then none else some (psum acc b (k - 1)))] ∧
    c = (Context.label 0 [] ((b11.drop 2).map .plain) C).fill ⟨s, f', (b12.drop 19).map .plain⟩)

/-- `ExtL1` for the `-O1` loop. -/
def ExtL1O1 : Prop :=
  ∀ (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (ma : Nat)
    (mem : MemInst) (p lim acc : Nat),
    ls[18]? = some (vI (p + 1)) → ls[14]? = some (vI lim) → ls[19]? = some (vI acc) →
    20 < ls.length → inst.mems[0]? = some ma → s.mems[ma]? = some mem →
    p ≤ lim → lim + 1 < 2 ^ 32 → lim ≤ mem.size → acc < 2 ^ 31 →
    Until H (Within (fun m a => m = ma ∧ p ≤ a ∧ a < lim) (fun _ _ => False))
      (ExtExit C s inst ls p lim acc fun j => mem.byte (p + j))
      ((ctx C).fill ⟨s, ⟨ls, inst⟩, [.plain extLoop]⟩)

end Subjects.Lz4C.O1
