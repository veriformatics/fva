import FVATest.Subjects.Lz4C.Copy

/-!
# Spike statement S5 (contract U20, frozen): the shortcut block, every branch

From the main loop's head, the first statement of every iteration: the token, the shortcut's room
tests, and, when they pass, 16 literal bytes by `memcpy`, the offset, the match tests and 18 match
bytes by three `memcpy`s. Five exits, each a join point of func 2 (`ShortExit`). The locals at the
head are the ones func 2's entry code computes (`0 = src`, `1 = dst`, `3 = op`, `4 = ip`,
`5 … 14` = the end pointers and limits); locals 2 and 15–18 carry nothing between iterations.
Proof-side, not a claim.
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- The main loop's locals for a block of `n` bytes at `src` and room `cap` at `dst`, with the
read position `ip` and the write position `op`. -/
def HeadLocals (ls : List Val) (src dst n cap op ip : Nat) : Prop :=
  ls.length = 19 ∧ ls[0]? = some (vI src) ∧ ls[1]? = some (vI dst) ∧
  ls[3]? = some (vI op) ∧ ls[4]? = some (vI ip) ∧
  ls[5]? = some (vI (dst + cap)) ∧ ls[6]? = some (vI (dst + cap - 32)) ∧
  ls[7]? = some (vI (src + n)) ∧ ls[8]? = some (vI (src + n - 16)) ∧
  ls[9]? = some (vI (dst + cap - 5)) ∧ ls[10]? = some (vI (dst + cap - 7)) ∧
  ls[11]? = some (vI (src + n - 4)) ∧ ls[12]? = some (vI (src + n - 8)) ∧
  ls[13]? = some (vI (dst + cap - 12)) ∧ ls[14]? = some (vI (src + n - 15))

/-- The labels `@6 … @3` around a statement of block `@6`'s body. -/
noncomputable def ctx6 (C : Ref.Context) : Ref.Context :=
  .label 0 [] ((body5.drop 5).map .plain) (ctx5 C)

/-- Where the shortcut block (`@9`, the first statement of block `@8`) leaves to, from the main
loop's head with token `t` at `ip`, `ll = t / 16`, `ml = t % 16`, the offset `off` after the
literals, `op' = op + ll`, `m = op' − off` (as `i32`):
* `ll = 15`: the literal length's extension bytes follow (after `@9`, in `@8`);
* no room for the shortcut: the general literal path (after `@8`, in `@7`), `ip + 1`;
* `ml = 15` or `off < 8`: the match code (after `@7`, in `@6`), 16 literal bytes copied;
* `m` before `dst`: the offset check (after `@6`, in `@5`), 16 literal bytes copied;
* the shortcut: the next head, 16 + 18 bytes copied. -/
def ShortExit (C : Ref.Context) (st : Store) (inst : ModuleInst) (ls : List Val) (ma : Nat)
    (mem : MemInst) (dst cap n src op ip : Nat) (c : Config) : Prop :=
  let t := (mem.byte ip).toNat
  let ll := t / 16
  let ml := t % 16
  let off := (mem.byte (ip + 1 + ll)).toNat + 256 * (mem.byte (ip + 2 + ll)).toNat
  let m : Val := .i32 (BitVec.ofNat 32 (op + ll) - BitVec.ofNat 32 off)
  let short := ((((((ls.set 15 (vI ml)).set 16 (vI t)).set 2 m).set 17 (vI (op + ll))).set 3
    (vI (ip + 1 + ll))).set 18 (vI off)).set 4 (vI (ip + 3 + ll))
  let st16 := st.setMem ma (fwdCopy mem op (ip + 1) 16)
  (ll = 15 ∧ c = (ctx8 C).fill
    ⟨st, ⟨((ls.set 15 (vI (ip + 1))).set 16 (vI t)).set 2 (vI 15), inst⟩,
      (body8.drop 1).map .plain⟩) ∨
  (ll < 15 ∧ ¬ (ip + 1 + 16 < src + n ∧ op + 32 ≤ dst + cap) ∧ c = (ctx7 C).fill
    ⟨st, ⟨(((ls.set 15 (vI (ip + 1))).set 16 (vI t)).set 2 (vI ll)).set 4 (vI (ip + 1)), inst⟩,
      (body7.drop 1).map .plain⟩) ∨
  (ll < 15 ∧ ip + 1 + 16 < src + n ∧ op + 32 ≤ dst + cap ∧ (ml = 15 ∨ off < 8) ∧
    c = (ctx6 C).fill ⟨st16, ⟨short, inst⟩, (body6.drop 1).map .plain⟩) ∨
  (ll < 15 ∧ ip + 1 + 16 < src + n ∧ op + 32 ≤ dst + cap ∧ ml < 15 ∧ 8 ≤ off ∧
    op + ll < dst + off ∧ c = (ctx5 C).fill ⟨st16, ⟨short, inst⟩, (body5.drop 5).map .plain⟩) ∨
  (ll < 15 ∧ ip + 1 + 16 < src + n ∧ op + 32 ≤ dst + cap ∧ ml < 15 ∧ 8 ≤ off ∧
    dst + off ≤ op + ll ∧ c = (ctx4 C).fill
      ⟨st.setMem ma (fwdCopy (fwdCopy mem op (ip + 1) 16) (op + ll) (op + ll - off) 18),
        ⟨(short.set 2 (vI (op + ll - off))).set 3 (vI (op + ll + ml + 4)), inst⟩,
        [.plain mainLoop]⟩)

/-- S5: the shortcut block from the main loop's head, every branch: each execution reaches one
of `ShortExit`'s five exits, reading only the source and destination buffers and writing only the
destination buffer before it. -/
def ShortcutS5 : Prop :=
  ∀ (H : HostSem) (C : Ref.Context) (st : Store) (inst : ModuleInst) (ls : List Val) (a ma : Nat)
    (mem : MemInst) (src dst n cap op ip : Nat),
    HeadLocals ls src dst n cap op ip →
    inst.funcs[3]? = some a → st.funcs[a]? = some (.wasm copyType inst Lifted.func3) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    131072 ≤ src → 131072 ≤ dst → src + n ≤ mem.size → dst + cap ≤ mem.size →
    mem.size < 2 ^ 32 → (src + n ≤ dst ∨ dst + cap ≤ src) → src ≤ ip → ip < src + n →
    dst ≤ op → op ≤ dst + cap →
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (ShortExit C st inst ls ma mem dst cap n src op ip)
      ((ctx4 C).fill ⟨st, ⟨ls, inst⟩, [.plain mainLoop]⟩)

end Subjects.Lz4C
