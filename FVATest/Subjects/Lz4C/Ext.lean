import FVATest.Subjects.Lz4C.Code
import FVA.Proof.Lib.Footprint

/-!
# Checkpoint 1 statement: the literal-length extension loop (contract U19, frozen)

From `loop @10` with locals `2 = p`, `14 = lim`, `17 = acc`, every execution leaves the loop at one
of three exits and, before it, reads only bytes `[p, lim)` of memory `ma` and writes nothing. The
exits, with bytes `b j = mem[p + j]` and partial sums `psum acc b i = acc + b 0 + … + b i`:

* normal, after `k + 1` reads: `b j = 255` for `j < k`, `b k ≠ 255`; execution continues after
  block `@9`;
* bound, before the `k`-th read: `p + k + 1 > lim`; execution continues after block `@3`;
* overflow, at the `k`-th read: the sum reaches `2^31`; execution continues after block `@3`.

Both proof routes prove `ExtL1` as written (proof-side, not a claim).
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- `acc + b 0 + … + b i`. -/
def psum (acc : Nat) (b : Nat → UInt8) (i : Nat) : Nat :=
  acc + ((List.range (i + 1)).map fun j => (b j).toNat).sum

/-- An `i32` local holding `n` (mod 2^32). -/
abbrev vI (n : Nat) : Val := .i32 (BitVec.ofNat 32 n)

/-- Frame `f'` = entry locals `ls` of instance `inst`, except locals 2, 4, 15, 17, which hold
`l2`, `l4`, `l15`, `l17` (`none` = unchanged). -/
def Locals (ls : List Val) (inst : ModuleInst) (f' : Frame) (l2 l4 : Nat)
    (l15 l17 : Option Nat) : Prop :=
  f'.inst = inst ∧ f'.locals.length = ls.length ∧
  (∀ i, i ≠ 2 → i ≠ 4 → i ≠ 15 → i ≠ 17 → f'.locals[i]? = ls[i]?) ∧
  f'.locals[2]? = some (vI l2) ∧ f'.locals[4]? = some (vI l4) ∧
  f'.locals[15]? = (l15.map vI <|> ls[15]?) ∧ f'.locals[17]? = (l17.map vI <|> ls[17]?)

/-- The loop's exits. -/
def ExtExit (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (p lim acc : Nat)
    (b : Nat → UInt8) (c : Config) : Prop :=
  (∃ k f', (∀ j < k, b j = 255) ∧ b k ≠ 255 ∧ p + k + 1 ≤ lim ∧ (∀ i ≤ k, psum acc b i < 2 ^ 31) ∧
    Locals ls inst f' (p + k + 1) (p + k + 1) (some (b k).toNat) (some (psum acc b k)) ∧
    c = (ctx8 C).fill ⟨s, f', (body8.drop 4).map .plain⟩) ∨
  (∃ k f', (∀ j < k, b j = 255) ∧ lim < p + k + 1 ∧ (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
    Locals ls inst f' (p + k) (p + k + 1)
      (if k = 0 then none else some (b (k - 1)).toNat)
      (if k = 0 then none else some (psum acc b (k - 1))) ∧
    c = C.fill ⟨s, f', (body2.drop 1).map .plain⟩) ∨
  (∃ k f', (∀ j < k, b j = 255) ∧ p + k + 1 ≤ lim ∧ (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
    2 ^ 31 ≤ psum acc b k ∧
    Locals ls inst f' (p + k) (p + k + 1) (some (b k).toNat) (some (psum acc b k)) ∧
    c = C.fill ⟨s, f', (body2.drop 1).map .plain⟩)

/-- `ExtL1`'s exits, the bound exit's position kept: the bound check fails at `p + k = lim`. -/
def ExtExitB (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (p lim acc : Nat)
    (b : Nat → UInt8) (c : Config) : Prop :=
  (∃ k f', (∀ j < k, b j = 255) ∧ b k ≠ 255 ∧ p + k + 1 ≤ lim ∧ (∀ i ≤ k, psum acc b i < 2 ^ 31) ∧
    Locals ls inst f' (p + k + 1) (p + k + 1) (some (b k).toNat) (some (psum acc b k)) ∧
    c = (ctx8 C).fill ⟨s, f', (body8.drop 4).map .plain⟩) ∨
  (∃ k f', (∀ j < k, b j = 255) ∧ p + k = lim ∧ (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
    Locals ls inst f' (p + k) (p + k + 1)
      (if k = 0 then none else some (b (k - 1)).toNat)
      (if k = 0 then none else some (psum acc b (k - 1))) ∧
    c = C.fill ⟨s, f', (body2.drop 1).map .plain⟩) ∨
  (∃ k f', (∀ j < k, b j = 255) ∧ p + k + 1 ≤ lim ∧ (∀ i, i + 1 ≤ k → psum acc b i < 2 ^ 31) ∧
    2 ^ 31 ≤ psum acc b k ∧
    Locals ls inst f' (p + k) (p + k + 1) (some (b k).toNat) (some (psum acc b k)) ∧
    c = C.fill ⟨s, f', (body2.drop 1).map .plain⟩)

/-- Checkpoint 1's statement L1. -/
def ExtL1 : Prop :=
  ∀ (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (ma : Nat)
    (mem : MemInst) (p lim acc : Nat),
    ls[2]? = some (vI p) → ls[14]? = some (vI lim) → ls[17]? = some (vI acc) →
    inst.mems[0]? = some ma → s.mems[ma]? = some mem →
    p ≤ lim → lim + 1 < 2 ^ 32 → lim ≤ mem.size → acc < 2 ^ 31 →
    Until H (Within (fun m a => m = ma ∧ p ≤ a ∧ a < lim) (fun _ _ => False))
      (ExtExit C s inst ls p lim acc fun j => mem.byte (p + j))
      ((ctx9 C).fill ⟨s, ⟨ls, inst⟩, [.plain extLoop]⟩)

/-- The literal length's extension loop (`ExtL1`'s statement with `ExtExitB`): the engine's
obligation for `SegA`. -/
def ExtL1B : Prop :=
  ∀ (H : HostSem) (C : Context) (s : Store) (inst : ModuleInst) (ls : List Val) (ma : Nat)
    (mem : MemInst) (p lim acc : Nat),
    ls[2]? = some (vI p) → ls[14]? = some (vI lim) → ls[17]? = some (vI acc) →
    inst.mems[0]? = some ma → s.mems[ma]? = some mem →
    p ≤ lim → lim + 1 < 2 ^ 32 → lim ≤ mem.size → acc < 2 ^ 31 →
    Until H (Within (fun m a => m = ma ∧ p ≤ a ∧ a < lim) (fun _ _ => False))
      (ExtExitB C s inst ls p lim acc fun j => mem.byte (p + j))
      ((ctx9 C).fill ⟨s, ⟨ls, inst⟩, [.plain extLoop]⟩)

theorem ExtExitB.exit {C : Context} {s : Store} {inst : ModuleInst} {ls : List Val}
    {p lim acc : Nat} {b : Nat → UInt8} {c : Config}
    (h : ExtExitB C s inst ls p lim acc b c) : ExtExit C s inst ls p lim acc b c := by
  rcases h with h | ⟨k, f, hff, hb, hs, hl, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨k, f, hff, by omega, hs, hl, hc⟩)
  · exact Or.inr (Or.inr h)

end Subjects.Lz4C
