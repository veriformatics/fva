import FVATest.Subjects.Lz4C.Seg
import FVATest.Subjects.Lz4C.Prefix

/-!
# What the main loop's composition shares (contract U20)

R1's footprint sets, the invariant every cutpoint of one call keeps (`Good`), the main loop's
head, and the frame facts of the decoder's memory changes; the composition itself = `Sim.lean`.
Proof support; outside the review surface.
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- R1's read set: below 131072, from 2097152 on, the source buffer, the destination buffer. -/
def R1R (src n dst cap : Nat) (_ : Nat) (a : Nat) : Prop :=
  a < 131072 ∨ 2097152 ≤ a ∨ (src ≤ a ∧ a < src + n) ∨ (dst ≤ a ∧ a < dst + cap)

/-- R1's write set: below 131072, from 2097152 on, the destination buffer. -/
def R1W (dst cap : Nat) (_ : Nat) (a : Nat) : Prop :=
  a < 131072 ∨ 2097152 ≤ a ∨ (dst ≤ a ∧ a < dst + cap)

theorem Within.mono {R W R' W' : Nat → Nat → Prop} {c : Config} (h : Within R W c)
    (hr : ∀ m a, R m a → R' m a) (hw : ∀ m a, W m a → W' m a) : Within R' W' c :=
  ⟨fun m a h' => hr m a (h.1 m a h'), fun m a h' => hw m a (h.2 m a h')⟩

/-- An `Until` whose footprint lies inside R1's sets. -/
theorem untilR1 {H : HostSem} {R W : Nat → Nat → Prop} {Q : Config → Prop} {c : Config}
    {src n dst cap : Nat} (h : Until H (Within R W) Q c)
    (hr : ∀ m a, R m a → R1R src n dst cap m a) (hw : ∀ m a, W m a → R1W dst cap m a) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) Q c :=
  h.mono (fun _ hc => Within.mono hc hr hw) fun _ hq => hq

theorem setMem_mems {st : Store} {ma : Nat} {mem mem' : MemInst} (h : st.mems[ma]? = some mem) :
    (st.setMem ma mem').mems[ma]? = some mem' := by
  simp only [Store.setMem]
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1

@[simp] theorem setMem_funcs (st : Store) (ma : Nat) (mem : MemInst) :
    (st.setMem ma mem).funcs = st.funcs := rfl

theorem setMem_setMem (st : Store) (ma : Nat) (m1 m2 : MemInst) :
    (st.setMem ma m1).setMem ma m2 = st.setMem ma m2 := by
  simp [Store.setMem]

/-- Two memories that agree below 131072 hold the same tables. -/
theorem TablesOK.of_low {mem mem' : MemInst} (h : TablesOK mem)
    (he : ∀ a < 131072, mem'.byte a = mem.byte a) : TablesOK mem' := by
  intro k hk
  have hr : ∀ base, base + 4 * k + 4 ≤ 131072 → tbl mem' base k = tbl mem base k := by
    intro base hb
    simp only [tbl, MemInst.read]
    rw [he (base + 4 * k) (by omega), he (base + 4 * k + 1) (by omega),
      he (base + 4 * k + 1 + 1) (by omega), he (base + 4 * k + 1 + 1 + 1) (by omega)]
  rw [hr 65536 (by omega), hr 65568 (by omega)]
  exact h k hk

/-- What every cutpoint of one call shares: the store's `memcpy`/`memmove` closures, memory `ma`
(2 MiB) holding the tables, the buffers' bounds and their separation. -/
structure Good (st : Store) (inst : ModuleInst) (ma src dst n cap : Nat) : Prop where
  a3 : ∃ a, inst.funcs[3]? = some a ∧ st.funcs[a]? = some (.wasm copyType inst Lifted.func3)
  a4 : ∃ a, inst.funcs[4]? = some a ∧ st.funcs[a]? = some (.wasm copyType inst Lifted.func4)
  ma0 : inst.mems[0]? = some ma
  mem : ∃ mem, st.mems[ma]? = some mem ∧ mem.size = 2097152 ∧ TablesOK mem
  srcLo : 131072 ≤ src
  dstLo : 131072 ≤ dst
  srcHi : src + n ≤ 2097152
  dstHi : dst + cap ≤ 2097152
  disj : src + n ≤ dst ∨ dst + cap ≤ src

/-- A memory change that keeps the size and every byte below 131072 keeps `Good`. -/
theorem Good.setMem {st : Store} {inst : ModuleInst} {ma src dst n cap : Nat} {mem mem' : MemInst}
    (hg : Good st inst ma src dst n cap) (hm : st.mems[ma]? = some mem)
    (hs : mem'.size = mem.size) (hl : ∀ a < 131072, mem'.byte a = mem.byte a) :
    Good (st.setMem ma mem') inst ma src dst n cap where
  a3 := by simpa using hg.a3
  a4 := by simpa using hg.a4
  ma0 := hg.ma0
  mem := by
    obtain ⟨mem₀, hm₀, hsz, ht⟩ := hg.mem
    obtain rfl : mem₀ = mem := Option.some.inj (hm₀.symm.trans hm)
    exact ⟨mem', setMem_mems hm, hs.trans hsz, ht.of_low hl⟩
  srcLo := hg.srcLo
  dstLo := hg.dstLo
  srcHi := hg.srcHi
  dstHi := hg.dstHi
  disj := hg.disj

/-- The main loop's head for `F0` (a top-level call). -/
noncomputable def head (st : Store) (inst : ModuleInst) (ls : List Val) : Config :=
  (ctx4 (ctx2 F0)).fill ⟨st, ⟨ls, inst⟩, [.plain mainLoop]⟩

theorem prologue_size (mem : MemInst) (o' off : Nat) :
    (prologue mem o' off).1.size = mem.size := by
  unfold prologue; split <;> simp [MemInst.size, MemInst.write]

theorem matchRest_size (mem : MemInst) (o' m oend : Nat) (mp : BitVec 32) :
    (matchRest mem o' m oend mp).size = mem.size := by
  simp only [matchRest]
  split
  · split <;> simp
  · split <;> split <;> simp

theorem write_low (mem : MemInst) (d k v a : Nat) (h : a < d) :
    (mem.write d k v).byte a = mem.byte a := by
  simp only [MemInst.write]; rw [ite_eq_right (by omega)]

theorem prologue_low (mem : MemInst) (o' off a : Nat) (h : a < o') :
    (prologue mem o' off).1.byte a = mem.byte a := by
  unfold prologue
  split
  · exact fwdCopy_outside _ _ _ _ _ (Or.inl h)
  · rw [fwdCopy_outside _ _ _ _ _ (Or.inl (by omega)), fwdCopy_outside _ _ _ _ _ (Or.inl h),
      write_low _ _ _ _ _ h]

theorem matchRest_low (mem : MemInst) (o' m oend a : Nat) (mp : BitVec 32) (h : a < o' + 8) :
    (matchRest mem o' m oend mp).byte a = mem.byte a := by
  simp only [matchRest]
  split
  · split
    · exact fwdCopy_outside _ _ _ _ _ (Or.inl h)
    · rw [fwdCopy_outside _ _ _ _ _ (Or.inl (by omega)), fwdCopy_outside _ _ _ _ _ (Or.inl h)]
  · by_cases hl : o' + 8 < oend - 7
    · simp only [hl, ite_true]
      split
      · rw [fwdCopy_outside _ _ _ _ _ (Or.inl (by omega)), fwdCopy_outside _ _ _ _ _ (Or.inl h)]
      · exact fwdCopy_outside _ _ _ _ _ (Or.inl h)
    · simp only [hl, ite_false]
      split
      · exact fwdCopy_outside _ _ _ _ _ (Or.inl h)
      · rfl

theorem ConstLocals.set {ls : List Val} {src dst n cap i : Nat} (h : ConstLocals ls src dst n cap)
    (hi : i = 2 ∨ i = 3 ∨ i = 4 ∨ 15 ≤ i) (v : Val) : ConstLocals (ls.set i v) src dst n cap := by
  obtain ⟨hl, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨by simp [hl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [List.getElem?_set_ne (by omega)] <;> assumption

/-- An extension-byte read moves forward, stays inside its limit and adds at most 255 per byte. -/
theorem extM_bound {mem : MemInst} {lim : Nat} :
    ∀ {fuel q acc a q' : Nat}, extM mem lim fuel q acc = some (a, q') →
      q < q' ∧ q' ≤ lim ∧ a ≤ acc + 255 * (q' - q) ∧ a < 2 ^ 31
  | 0, _, _, _, _, h => by simp [extM] at h
  | fuel + 1, q, acc, a, q', h => by
    unfold extM at h
    split at h
    · split at h
      · have hb := (mem.byte q).toNat_lt
        split at h
        · obtain ⟨h1, h2, h3, h4⟩ := extM_bound h
          refine ⟨by omega, h2, ?_, h4⟩
          rename_i h255 _ _
          have : q' - q = (q' - (q + 1)) + 1 := by omega
          rw [this, Nat.mul_add]; omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rename_i hq _ _
          omega
      · simp at h
    · simp at h

/-- X3 (the match code) with output `o'`, offset `off`, length field `ml0`, position `j`. -/
noncomputable def AtX3 (F : Ref.Context) (st : Store) (inst : ModuleInst)
    (src dst n cap o' off ml0 j : Nat) (c : Config) : Prop :=
  ∃ ls', ConstLocals ls' src dst n cap ∧ ls'[4]? = some (vI j) ∧ ls'[15]? = some (vI ml0) ∧
    ls'[17]? = some (vI o') ∧ ls'[18]? = some (vI off) ∧
    ls'[2]? = some (.i32 (BitVec.ofNat 32 o' - BitVec.ofNat 32 off)) ∧
    c = (ctx6 (ctx2 F)).fill ⟨st, ⟨ls', inst⟩, (body6.drop 1).map .plain⟩

theorem off_lt (mem : MemInst) (p : Nat) :
    (mem.byte p).toNat + 256 * (mem.byte (p + 1)).toNat < 65536 := by
  have := (mem.byte p).toNat_lt; have := (mem.byte (p + 1)).toNat_lt; omega

theorem HeadLocals.const {ls : List Val} {src dst n cap op ip : Nat}
    (h : HeadLocals ls src dst n cap op ip) : ConstLocals ls src dst n cap := by
  obtain ⟨hl, h0, h1, -, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨hl, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem HeadLocals.of_const {ls : List Val} {src dst n cap op ip : Nat}
    (h : ConstLocals ls src dst n cap) (h3 : ls[3]? = some (vI op)) (h4 : ls[4]? = some (vI ip)) :
    HeadLocals ls src dst n cap op ip := by
  obtain ⟨hl, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨hl, h0, h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end Subjects.Lz4C
