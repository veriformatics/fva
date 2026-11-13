import FVATest.Subjects.Lz4C.Short

/-!
# The main loop's segments after the shortcut block (decoder cutpoints, contract U20)

func 2's main loop body splits at its join points: X2 = the general literal path (after block
`@8`, in `@7`), X3 = the match code (after `@7`, in `@6`), X4 = the offset check (after `@6`, in
`@5`). Each segment runs from one join point to the next, to the next loop head, to the success
`return`, or to the error epilogue (after block `@2`, in `@1`: `local 4 ↦ ~local 4 + src`). Every
statement is exact — the post-state's locals and memory as terms of the pre-state — and carries
no decoder invariant: bounds, the decoded prefix and the model relation are derived outside
(`Prefix.lean`). Locals a join point leaves dead are arbitrary. Proof-side, not claims.
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- The function's own label and frame over the caller `caller` (code `rest` after the call,
outer context `outer`). -/
def fnCtx (caller : Frame) (rest : List AInstr) (outer : Ref.Context) : Ref.Context :=
  .label 1 [] [] (.frame 1 caller rest outer)

/-- Inside block `@1`: the code after it is the function's last instruction. -/
noncomputable def ctx1 (F : Ref.Context) : Ref.Context :=
  .label 0 [] ((Lifted.func2.body.drop 3).map .plain) F

/-- Inside block `@2` (the main loop's blocks `@3 … @5` inside it). -/
noncomputable def ctx2 (F : Ref.Context) : Ref.Context :=
  .label 0 [] ((body1.drop 54).map .plain) (ctx1 F)

/-- The constant locals of the main loop: 0 = `src`, 1 = `dst`, 5 … 14 = the end pointers and
limits the entry code computed (19 locals). -/
def ConstLocals (ls : List (Option Val)) (src dst n cap : Nat) : Prop :=
  ls.length = 19 ∧ ls[0]? = some (some (vI src)) ∧ ls[1]? = some (some (vI dst)) ∧
  ls[5]? = some (some (vI (dst + cap))) ∧ ls[6]? = some (some (vI (dst + cap - 32))) ∧
  ls[7]? = some (some (vI (src + n))) ∧ ls[8]? = some (some (vI (src + n - 16))) ∧
  ls[9]? = some (some (vI (dst + cap - 5))) ∧ ls[10]? = some (some (vI (dst + cap - 7))) ∧
  ls[11]? = some (some (vI (src + n - 4))) ∧ ls[12]? = some (some (vI (src + n - 8))) ∧
  ls[13]? = some (some (vI (dst + cap - 12))) ∧ ls[14]? = some (some (vI (src + n - 15)))

/-- The error epilogue's entry with local 4 = `v` and every constant local kept (the epilogue
returns `~v + src`). -/
noncomputable def ErrExit (F : Ref.Context) (st : Store) (inst : ModuleInst) (src dst n cap : Nat)
    (v : Nat) (c : Config) : Prop :=
  ∃ ls', ConstLocals ls' src dst n cap ∧ ls'[4]? = some (some (vI v)) ∧
    c = (ctx1 F).fill ⟨st, ⟨ls', inst⟩, (body1.drop 54).map .plain⟩

/-- The configuration after func 2 returned `r` with store `st` to the caller. -/
def Returned (caller : Frame) (rest : List AInstr) (outer : Ref.Context) (st : Store) (r : Nat)
    (c : Config) : Prop :=
  c = outer.fill ⟨st, caller, vals [vI r] ++ rest⟩

/-- SegB's exits from X2 (literals of length `len` at `q`, output at `op`, `cpy = op + len`):
* the literals end the block (`cpy > oend − 12` or `q + len > iend − 8`, then `q + len = iend`,
  `cpy ≤ oend`): `memmove`, and func 2 returns `cpy − dst`;
* the same test fails otherwise: the error epilogue with local 4 = `q`;
* else the literal wildcopy (`k = chunks op cpy` chunks), then the offset after the literals: X3,
  with local 2 = `cpy − off` (as `i32`), 4 = `q + len + 2`, 15 = `t % 16`, 17 = `cpy`, 18 = `off`
  (3 = `op + 8k`, dead). -/
noncomputable def SegBExit (caller : Frame) (rest : List AInstr) (outer : Ref.Context) (st : Store)
    (inst : ModuleInst) (ls : List (Option Val)) (ma : Nat) (mem : MemInst)
        (src dst n cap op q len t : Nat)
    (c : Config) : Prop :=
  let F := fnCtx caller rest outer
  let cpy := op + len
  let near := dst + cap < cpy + 12 ∨ src + n < q + len + 8
  (near ∧ q + len = src + n ∧ cpy ≤ dst + cap ∧
    Returned caller rest outer (st.setMem ma (move mem op q len)) (cpy - dst) c) ∨
  (near ∧ ¬ (q + len = src + n ∧ cpy ≤ dst + cap) ∧ ErrExit F st inst src dst n cap q c) ∨
  (¬ near ∧ c = (ctx6 (ctx2 F)).fill
    ⟨st.setMem ma (fwdCopy mem op q (8 * chunks op cpy)),
      ⟨(((((ls.set 17 (some (vI cpy))).set 3 (some (vI (op + 8 * chunks op cpy)))).set 15
          (some (vI (t % 16)))).set 4
        (some (vI (q + len + 2)))).set 18
          (some (vI ((mem.byte (q + len)).toNat + 256 * (mem.byte (q + len + 1)).toNat)))).set 2
        (some (.i32 (BitVec.ofNat 32 cpy - BitVec.ofNat 32
          ((mem.byte (q + len)).toNat + 256 * (mem.byte (q + len + 1)).toNat)))), inst⟩,
      (body6.drop 1).map .plain⟩)

/-- SegB: from X2 (the general literal path) with locals 3 = `op`, 4 = `q` (the first literal),
2 = `len`, 16 = the token `t`, every execution reaches one of `SegBExit`'s exits, reading only the
source and destination buffers and writing only the destination buffer before it. -/
def SegB : Prop :=
  ∀ (H : HostSem) (caller : Frame) (rest : List AInstr) (outer : Ref.Context) (st : Store)
    (inst : ModuleInst) (ls : List (Option Val)) (a a4 ma : Nat) (mem : MemInst)
    (src dst n cap op q len t : Nat),
    ConstLocals ls src dst n cap → ls[3]? = some (some (vI op)) → ls[4]? = some (some (vI q)) →
    ls[2]? = some (some (vI len)) → ls[16]? = some (some (vI t)) →
    inst.funcs[3]? = some a → st.funcs[a]? = some (.wasm copyType inst Lifted.func3) →
    inst.funcs[4]? = some a4 → st.funcs[a4]? = some (.wasm copyType inst Lifted.func4) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    131072 ≤ src → 131072 ≤ dst → src + n ≤ mem.size → dst + cap ≤ mem.size →
    mem.size ≤ 2097152 → (src + n ≤ dst ∨ dst + cap ≤ src) → src ≤ q → q ≤ src + n →
    dst ≤ op → op ≤ dst + cap → len < 2 ^ 31 →
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (SegBExit caller rest outer st inst ls ma mem src dst n cap op q len t)
      ((ctx7 (ctx2 (fnCtx caller rest outer))).fill ⟨st, ⟨ls, inst⟩, (body7.drop 1).map .plain⟩)

/-- The extension bytes from position `q` onto `acc`, read from memory as func 2 reads them
(`read_variable_length`): each byte's successor position must be at most `lim`, the sum stays
below 2^31, reading continues while the byte is 255; the sum and the position after the last
byte. -/
def extM (mem : MemInst) (lim : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, q, acc =>
    if q + 1 ≤ lim then
      if acc + (mem.byte q).toNat < 2 ^ 31 then
        if (mem.byte q).toNat = 255 then extM mem lim fuel (q + 1) (acc + (mem.byte q).toNat)
        else some (acc + (mem.byte q).toNat, q + 1)
      else none
    else none

/-- The error exits of a segment: the epilogue with local 4 between `src` and `src + n + 1`. -/
noncomputable def Err (F : Ref.Context) (st : Store) (inst : ModuleInst) (src dst n cap : Nat)
    (c : Config) : Prop :=
  ∃ v, src ≤ v ∧ v ≤ src + n + 1 ∧ ErrExit F st inst src dst n cap v c

/-- X2 (the general literal path) with literals of length `len` at `q`, output at `op`, the token
`t` in local 16 (the other non-constant locals dead). -/
noncomputable def AtX2 (F : Ref.Context) (st : Store) (inst : ModuleInst)
    (src dst n cap op q len t : Nat) (c : Config) : Prop :=
  ∃ ls', ConstLocals ls' src dst n cap ∧ ls'[3]? = some (some (vI op)) ∧ ls'[4]? =
      some (some (vI q)) ∧
    ls'[2]? = some (some (vI len)) ∧ ls'[16]? = some (some (vI t)) ∧
    c = (ctx7 (ctx2 F)).fill ⟨st, ⟨ls', inst⟩, (body7.drop 1).map .plain⟩

/-- SegA: from X1 (the token's literal field is 15: locals 4 = `ip` the token's position,
15 = `ip + 1`, 2 = 15, 16 = `t`, 3 = `op`), the literal length's extension bytes: X2 with length
`15 + acc` at the position after them, or an error exit when `extM` fails. Memory at most
2 MiB: otherwise the length's overflow guards (`len > ~op`, `len > ~ip`) can fire for an `acc`
near `2^31`. -/
def SegA : Prop :=
  ∀ (H : HostSem) (F : Ref.Context) (st : Store) (inst : ModuleInst) (ls : List (Option Val))
      (ma : Nat)
    (mem : MemInst) (src dst n cap op ip t : Nat),
    ConstLocals ls src dst n cap → ls[3]? = some (some (vI op)) → ls[4]? = some (some (vI ip)) →
    ls[15]? = some (some (vI (ip + 1))) → ls[2]? = some (some (vI 15)) → ls[16]? =
        some (some (vI t)) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    131072 ≤ src → 131072 ≤ dst → src + n ≤ mem.size → dst + cap ≤ mem.size →
    mem.size ≤ 2097152 → src ≤ ip → ip < src + n → op < 2 ^ 31 →
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (fun c => (∃ acc q, extM mem (src + n - 15) n (ip + 1) 0 = some (acc, q) ∧
          AtX2 F st inst src dst n cap op q (15 + acc) t c) ∨
        (extM mem (src + n - 15) n (ip + 1) 0 = none ∧ Err F st inst src dst n cap c))
      ((ctx8 (ctx2 F)).fill ⟨st, ⟨ls, inst⟩, (body8.drop 1).map .plain⟩)

/-- X4 (the offset check) with the match length field value `m` (local 15), output `o'` (17),
offset `off` (18), match pointer `op' − off` as `i32` (2), position `j` (4). -/
noncomputable def AtX4 (F : Ref.Context) (st : Store) (inst : ModuleInst)
    (src dst n cap o' off m j : Nat) (c : Config) : Prop :=
  ∃ ls', ConstLocals ls' src dst n cap ∧ ls'[4]? = some (some (vI j)) ∧ ls'[15]? =
      some (some (vI m)) ∧
    ls'[17]? = some (some (vI o')) ∧ ls'[18]? = some (some (vI off)) ∧
    ls'[2]? = some (some (.i32 (BitVec.ofNat 32 o' - BitVec.ofNat 32 off))) ∧
    c = (ctx5 (ctx2 F)).fill ⟨st, ⟨ls', inst⟩, (body5.drop 5).map .plain⟩

/-- SegC: from X3 (the match code: locals 4 = `j` after the offset, 15 = the field `ml0`,
17 = `o'`, 18 = `off`, 2 = `o' − off`), the match length: `ml0` itself below 15, else
`15 + acc` from the extension bytes at `j` (`extM` with limit `iend − 4`); X4, or an error exit
when `extM` fails. -/
def SegC : Prop :=
  ∀ (H : HostSem) (F : Ref.Context) (st : Store) (inst : ModuleInst) (ls : List (Option Val))
      (ma : Nat)
    (mem : MemInst) (src dst n cap o' off ml0 j : Nat),
    ConstLocals ls src dst n cap → ls[4]? = some (some (vI j)) → ls[15]? = some (some (vI ml0)) →
    ls[17]? = some (some (vI o')) → ls[18]? = some (some (vI off)) →
    ls[2]? = some (some (.i32 (BitVec.ofNat 32 o' - BitVec.ofNat 32 off))) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    131072 ≤ src → 131072 ≤ dst → src + n ≤ mem.size → dst + cap ≤ mem.size →
    mem.size ≤ 2097152 → src ≤ j → j ≤ src + n → ml0 < 16 → o' < 2 ^ 31 →
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (fun c => (ml0 < 15 ∧ AtX4 F st inst src dst n cap o' off ml0 j c) ∨
        (ml0 = 15 ∧ ∃ acc j', extM mem (src + n - 4) n j 0 = some (acc, j') ∧
          AtX4 F st inst src dst n cap o' off (15 + acc) j' c) ∨
        (ml0 = 15 ∧ extM mem (src + n - 4) n j 0 = none ∧ Err F st inst src dst n cap c))
      ((ctx6 (ctx2 F)).fill ⟨st, ⟨ls, inst⟩, (body6.drop 1).map .plain⟩)

/-- The 4-byte table entry func 2 reads for an offset `off < 8`: `inc32table` at 65536,
`dec64table` at 65568. -/
def tbl (mem : MemInst) (base off : Nat) : Nat := mem.read (base + 4 * off) 4

/-- The match's first 8 bytes at `o'` from `mp = o' − off` (as `i32`), and the match pointer
after them: offset ≥ 8 → one 8-byte copy, pointer `mp + 8`; below → 4 zero bytes, 4 single bytes
from `mp`, 4 bytes from `mp + inc32[off]`, pointer `mp + inc32[off] − dec64[off]`. -/
def prologue (mem : MemInst) (o' off : Nat) : MemInst × BitVec 32 :=
  let mp := BitVec.ofNat 32 o' - BitVec.ofNat 32 off
  if 7 < off then (fwdCopy mem o' mp.toNat 8, mp + 8)
  else
    let p2 := mp + BitVec.ofNat 32 (tbl mem 65536 off)
    (fwdCopy (fwdCopy (mem.write o' 4 0) o' mp.toNat 4) (o' + 4) p2.toNat 4,
      p2 - BitVec.ofNat 32 (tbl mem 65568 off))

/-- The match from `o' + 8` up to `cpy = o' + m + 4` (`m` = the length field value), pointer
`mp`: far from the end (`cpy ≤ oend − 12`) an 8-byte copy, then, for `m ≥ 13`, the wildcopy from
`o' + 16`; near it the wildcopy from `o' + 8` up to `oend − 7`, then single bytes up to `cpy`. -/
def matchRest (mem : MemInst) (o' m oend : Nat) (mp : BitVec 32) : MemInst :=
  let cpy := o' + m + 4
  if cpy + 12 ≤ oend then
    let m4 := fwdCopy mem (o' + 8) mp.toNat 8
    if m < 13 then m4 else fwdCopy m4 (o' + 16) (mp + 8).toNat (8 * chunks (o' + 16) cpy)
  else
    let lim := oend - 7
    let r : MemInst × Nat × Nat := if o' + 8 < lim then
        (fwdCopy mem (o' + 8) mp.toNat (8 * chunks (o' + 8) lim),
          (mp + BitVec.ofNat 32 (lim - (o' + 8))).toNat, lim)
      else (mem, mp.toNat, o' + 8)
    if r.2.2 < cpy then fwdCopy r.1 r.2.2 r.2.1 (cpy - r.2.2) else r.1

/-- lz4's `inc32table` and `dec64table` (`dec64table`'s negative entries as `i32` bits): the
offset < 8 path reads them at 65536 and 65568. -/
def inc32 : List Nat := [0, 1, 2, 1, 0, 4, 4, 4]
/-- See `inc32`. -/
def dec64 : List Nat := [0, 0, 0, 4294967295, 4294967292, 1, 2, 3]

/-- Memory `mem` holds the two tables. -/
def TablesOK (mem : MemInst) : Prop :=
  ∀ k < 8, tbl mem 65536 k = inc32[k]! ∧ tbl mem 65568 k = dec64[k]!

/-- The decoder's read set: the module's own memory below 131072 (the tables), the source and
the destination buffers. -/
def ReadSet (ma src n dst cap : Nat) (m x : Nat) : Prop :=
  m = ma ∧ (x < 131072 ∨ Span ma src n m x ∨ Span ma dst cap m x)

/-- SegD: from X4 (locals 4 = `j`, 15 = the length field value `m`, 17 = `o'`, 18 = `off`,
2 = `o' − off`), the offset check, the match's first 8 bytes and the rest of it: the next loop
head with `op = o' + m + 4`, `ip = j`; an error exit when the match starts before `dst` (nothing
written) or ends past `oend − 5` (the first 8 bytes written). -/
def SegD : Prop :=
  ∀ (H : HostSem) (F : Ref.Context) (st : Store) (inst : ModuleInst) (ls : List (Option Val))
      (a ma : Nat)
    (mem : MemInst) (src dst n cap o' off m j : Nat),
    ConstLocals ls src dst n cap → ls[4]? = some (some (vI j)) → ls[15]? = some (some (vI m)) →
    ls[17]? = some (some (vI o')) → ls[18]? = some (some (vI off)) →
    ls[2]? = some (some (.i32 (BitVec.ofNat 32 o' - BitVec.ofNat 32 off))) →
    inst.funcs[3]? = some a → st.funcs[a]? = some (.wasm copyType inst Lifted.func3) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    131072 ≤ src → 131072 ≤ dst → src + n ≤ mem.size → dst + cap ≤ mem.size →
    mem.size ≤ 2097152 → (src + n ≤ dst ∨ dst + cap ≤ src) → src ≤ j → j ≤ src + n →
    dst ≤ o' → o' + 8 ≤ dst + cap → off < 65536 → m < 2 ^ 31 → TablesOK mem →
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (fun c => (o' < dst + off ∧ Err F st inst src dst n cap c) ∨
        (dst + off ≤ o' ∧ dst + cap < o' + m + 4 + 5 ∧
          Err F (st.setMem ma (prologue mem o' off).1) inst src dst n cap c) ∨
        (dst + off ≤ o' ∧ o' + m + 4 + 5 ≤ dst + cap ∧ ∃ ls',
          HeadLocals ls' src dst n cap (o' + m + 4) j ∧ c = (ctx4 (ctx2 F)).fill
            ⟨st.setMem ma (matchRest (prologue mem o' off).1 o' m (dst + cap)
              (prologue mem o' off).2), ⟨ls', inst⟩, [.plain mainLoop]⟩))
      ((ctx5 (ctx2 F)).fill ⟨st, ⟨ls, inst⟩, (body5.drop 5).map .plain⟩)

/-- The function context of a top-level invocation (`invokeConfig`): func 2's label and frame
over the embedder's empty frame. -/
def F0 : Ref.Context := fnCtx ⟨[], {}⟩ [] .hole

/-- func 2's defined type: four `i32` parameters, one `i32` result, a one-member group. -/
def decType : DefType := ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩

/-- `−1` as an `i32` value: the decoder's error result before the main loop. -/
def vNeg1 : Val := .i32 (BitVec.ofNat 32 4294967295)

/-- Entry: from the invocation of func 2 on `src dst n cap`, the entry code returns `−1` (null
`src`, negative `cap`, `cap = 0` with `n ≠ 1`, `n = 0`), or `0`/`−1` for the one-byte block when
`cap = 0` (reading `src[0]`), or reaches the main loop's head with `ip = src`, `op = dst`. -/
def Entry : Prop :=
  ∀ (H : HostSem) (st : Store) (inst : ModuleInst) (a ma : Nat) (mem : MemInst)
    (src dst n cap : Nat),
    st.funcs[a]? = some (.wasm decType inst Lifted.func2) →
    inst.mems[0]? = some ma → st.mems[ma]? = some mem →
    32 ≤ dst → 16 ≤ src → dst + cap < 2 ^ 32 → src + n < 2 ^ 32 → (n = 1 → src < mem.size) →
    Until H (Within (Span ma src n) (fun _ _ => False))
      (fun c => ((src = 0 ∨ 2 ^ 31 ≤ cap ∨ (cap = 0 ∧ n ≠ 1) ∨ (cap ≠ 0 ∧ n = 0)) ∧
          c = ⟨st, ⟨[], {}⟩, vals [vNeg1]⟩) ∨
        (src ≠ 0 ∧ cap = 0 ∧ n = 1 ∧ c = ⟨st, ⟨[], {}⟩,
          vals [if mem.byte src = 0 then vI 0 else vNeg1]⟩) ∨
        (src ≠ 0 ∧ cap < 2 ^ 31 ∧ cap ≠ 0 ∧ n ≠ 0 ∧ ∃ ls, HeadLocals ls src dst n cap dst src ∧
          c = (ctx4 (ctx2 F0)).fill ⟨st, ⟨ls, inst⟩, [.plain mainLoop]⟩))
      (invokeConfig st a [vI src, vI dst, vI n, vI cap])

/-- The error epilogue: from its entry with local 4 = `v`, func 2 returns `~v + src`. -/
def ErrRet : Prop :=
  ∀ (H : HostSem) (st : Store) (inst : ModuleInst) (src dst n cap v : Nat) (c : Config),
    ErrExit F0 st inst src dst n cap v c → v < 2 ^ 32 → src < 2 ^ 32 →
    Until H (Within (fun _ _ => False) (fun _ _ => False))
      (fun c' => c' = ⟨st, ⟨[], {}⟩,
        vals [.i32 (~~~(BitVec.ofNat 32 v) + BitVec.ofNat 32 src)]⟩) c

end Subjects.Lz4C
