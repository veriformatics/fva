import FVATest.Subjects.Lz4C.Ext

/-!
# Spike statements S1–S4 (contract U20, frozen): the compiled copies

The compiled `memcpy` (func 3) and `memmove` (func 4) from `bench/subjects/c-memory.c`, each
from its `call` instruction under an arbitrary caller context, and two of `LZ4_decompress_safe`'s
wildcopy loops (`LZ4_wildCopy8`, 8-byte `memcpy` chunks), each from its loop instruction under
the exact labels of func 2. Every statement = total arrival at the configuration after the code
(`Until`), reading and writing only the copied ranges of memory `ma` before it. Proof-side, not
claims: every proof route proves these statements as written.
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- `memcpy` as compiled: bytes `d + i ← s + i` for `i = 0 … n − 1` in ascending order, each read
after every earlier write (a forward overlap repeats bytes). -/
def fwdCopy (mem : MemInst) (d s : Nat) : Nat → MemInst
  | 0 => mem
  | n + 1 => fwdCopy (mem.write d 1 (mem.byte s).toNat) (d + 1) (s + 1) n

/-- `memmove`: `[d, d + n)` takes the bytes `[s, s + n)` held before the call, whatever the
overlap. -/
def move (mem : MemInst) (d s n : Nat) : MemInst :=
  { mem with byte := fun a => if d ≤ a ∧ a < d + n then mem.byte (s + (a - d)) else mem.byte a }

/-- The type of `memcpy` and `memmove`: `(i32, i32, i32) → i32`. -/
def copyType : FuncType := ⟨[.num .i32, .num .i32, .num .i32], [.num .i32]⟩

/-- Byte `x` of memory `m` lies in `[p, p + n)` of memory `ma`. -/
def Span (ma p n : Nat) (m x : Nat) : Prop := m = ma ∧ p ≤ x ∧ x < p + n

/-- A call of function `idx` (code `code`, closed over `inst`) from the caller frame `f`: from
`call idx` with arguments `d s n` on top of the stack `vs`, every execution reaches the
configuration after the call — result `d`, memory `mem'` — reading only `[s, s + n)` and writing
only `[d, d + n)` of memory `ma` before it. -/
def CopyCall (idx : Nat) (code : Func) (sem : MemInst → Nat → Nat → Nat → MemInst) : Prop :=
  ∀ (H : HostSem) (C : Context) (st : Store) (f : Frame) (vs : List Val) (rest : List AInstr)
    (a ma : Nat) (inst : ModuleInst) (mem : MemInst) (d s n : Nat),
    f.inst.funcs[idx]? = some a → st.funcs[a]? = some (.wasm copyType inst code) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    d + n ≤ mem.size → s + n ≤ mem.size → mem.size < 2 ^ 32 →
    Until H (Within (Span ma s n) (Span ma d n))
      (fun c => c = C.fill ⟨st.setMem ma (sem mem d s n), f, vals (vs ++ [vI d]) ++ rest⟩)
      (C.fill ⟨st, f, vals (vs ++ [vI d, vI s, vI n]) ++ [.plain (.call idx)] ++ rest⟩)

/-- S1: the compiled `memcpy` is the ascending byte copy. -/
def MemcpyS1 : Prop := CopyCall 3 Lifted.func3 fwdCopy

/-- S2: the compiled `memmove` is the source-preserving copy. -/
def MemmoveS2 : Prop := CopyCall 4 Lifted.func4 move

/-- The literal wildcopy loop (`LZ4_wildCopy8(op, ip, cpy)`, func 2 `loop @8` in block `@7`). -/
noncomputable def litLoop : Instr := body7.getD 2 .nop

/-- The final match wildcopy loop (`LZ4_wildCopy8(op + 8, match + 8, cpy)`, the last `loop @6`
of the main loop's body; it leaves by `br 1` to the main loop). -/
noncomputable def matchLoop : Instr := body5.getD 38 .nop

/-- The labels `@7 … @3` around a statement of block `@7`'s body; `C` = the rest. -/
noncomputable def ctx7 (C : Ref.Context) : Ref.Context :=
  .label 0 [] ((body6.drop 1).map .plain) <|
  .label 0 [] ((body5.drop 5).map .plain) <|
  .label 0 [mainLoop] ((body4.drop 1).map .plain) <|
  .label 0 [] ((body3.drop 1).map .plain) <|
  .label 0 [] ((body2.drop 1).map .plain) C

/-- The labels `@5 … @3` around a statement of the main loop's body. -/
noncomputable def ctx5 (C : Ref.Context) : Ref.Context :=
  .label 0 [mainLoop] ((body4.drop 1).map .plain) <|
  .label 0 [] ((body3.drop 1).map .plain) <|
  .label 0 [] ((body2.drop 1).map .plain) C

/-- The labels `@4, @3` around a statement of block `@4`'s body (the main loop's position). -/
noncomputable def ctx4 (C : Ref.Context) : Ref.Context :=
  .label 0 [] ((body3.drop 1).map .plain) <|
  .label 0 [] ((body2.drop 1).map .plain) C

/-- Iterations of a do-while wildcopy from `p` up to `e`: the least `k ≥ 1` with `p + 8k ≥ e`. -/
def chunks (p e : Nat) : Nat := max 1 ((e - p + 7) / 8)

/-- A wildcopy loop with write pointer local `dl`, read pointer local `sl`, end local `el`, from
`entry` to `exit` (each given the frame and store): `k = chunks q e` iterations of
`memcpy(q + 8j, m + 8j, 8)`, so memory = `fwdCopy mem q m (8k)`, the pointers end at `q + 8k`,
`m + 8k`, every other local unchanged. -/
def WildLoop (dl sl el : Nat) (entry exit : Store → Frame → Config) : Prop :=
  ∀ (H : HostSem) (st : Store) (inst : ModuleInst) (ls : List Val) (a ma : Nat) (mem : MemInst)
    (q m e : Nat),
    ls[dl]? = some (vI q) → ls[sl]? = some (vI m) → ls[el]? = some (vI e) →
    inst.funcs[3]? = some a → st.funcs[a]? = some (.wasm copyType inst Lifted.func3) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    q ≤ e → q + 8 * chunks q e ≤ mem.size → m + 8 * chunks q e ≤ mem.size →
    mem.size < 2 ^ 32 →
    Until H (Within (Span ma m (8 * chunks q e)) (Span ma q (8 * chunks q e)))
      (fun c => c = exit (st.setMem ma (fwdCopy mem q m (8 * chunks q e)))
        ⟨(ls.set dl (vI (q + 8 * chunks q e))).set sl (vI (m + 8 * chunks q e)), inst⟩)
      (entry st ⟨ls, inst⟩)

/-- S3: the literal wildcopy loop (locals 3 = `op`, 4 = `ip`, 17 = `cpy`), from the loop to the
code after it in block `@7`. -/
def LitWildS3 : Prop :=
  ∀ C : Ref.Context, WildLoop 3 4 17
    (fun st f => (ctx7 C).fill ⟨st, f, (body7.drop 2).map .plain⟩)
    (fun st f => (ctx7 C).fill ⟨st, f, (body7.drop 3).map .plain⟩)

/-- S4: the final match wildcopy loop (locals 17 = write pointer, 2 = `match`, 3 = `cpy`), from the
loop to the main loop's next iteration. -/
def MatchWildS4 : Prop :=
  ∀ C : Ref.Context, WildLoop 17 2 3
    (fun st f => (ctx5 C).fill ⟨st, f, [.plain matchLoop]⟩)
    (fun st f => (ctx4 C).fill ⟨st, f, [.plain mainLoop]⟩)

end Subjects.Lz4C
