import FVATest.Subjects.Lz4C.Seg
import FVATest.Subjects.Lz4C.Prefix

/-!
# The main loop from its segments (R1's composition, contract U20)

From the cutpoint statements (`Seg.lean`, `Short.lean`), assumed as hypotheses: from a good main
loop head, every execution of func 2 returns one `i32` value, reading and writing only R1's sets.
An iteration ends at a later head (`ip` grows) or in a return; the error exits return through the
epilogue. Proof support; outside the review surface.
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

/-- Where an iteration from a head at `ip0` ends: a good head further on, or func 2 returned one
`i32`. -/
def IterExit (inst : ModuleInst) (ma src dst n cap ip0 : Nat) (c : Config) : Prop :=
  (∃ st' ls' op' ip', Good st' inst ma src dst n cap ∧ HeadLocals ls' src dst n cap op' ip' ∧
    ip0 < ip' ∧ ip' < src + n ∧ dst ≤ op' ∧ op' ≤ dst + cap ∧ c = head st' inst ls') ∨
  ∃ st' v, c = ⟨st', ⟨[], {}⟩, vals [.i32 v]⟩

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

/-- An error exit returns through the epilogue. -/
theorem contErr (hR : ErrRet) {H : HostSem} {st : Store} {inst : ModuleInst}
    {ma src dst n cap ip0 : Nat} {c : Config} (hs : src + n + 1 < 2 ^ 32)
    (hc : Err F0 st inst src dst n cap c) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) (IterExit inst ma src dst n cap ip0) c := by
  obtain ⟨v, -, hv, he⟩ := hc
  exact (untilR1 (hR H st inst src dst n cap v c he (by omega) (by omega)) (fun _ _ h => h.elim)
    (fun _ _ h => h.elim)).mono (fun _ h => h) fun _ h => Or.inr ⟨st, _, h⟩

/-- From X4: SegD, then the epilogue or a later head (`ip0 < j`). -/
theorem contX4 (hD : SegD) (hR : ErrRet) {H : HostSem} {st : Store} {inst : ModuleInst}
    {ma src dst n cap o' off m j ip0 : Nat} {c : Config} (hg : Good st inst ma src dst n cap)
    (hc : AtX4 F0 st inst src dst n cap o' off m j c) (hj : ip0 < j) (hsj : src ≤ j)
    (hjn : j < src + n) (ho : dst ≤ o') (ho8 : o' + 8 ≤ dst + cap) (hoff : off < 65536)
    (hm : m < 2 ^ 31) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) (IterExit inst ma src dst n cap ip0) c := by
  obtain ⟨ls, hcl, h4, h15, h17, h18, h2, rfl⟩ := hc
  obtain ⟨a, ha, hfa⟩ := hg.a3
  obtain ⟨mem, hm0, hsz, ht⟩ := hg.mem
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hd0 := hg.dstLo
  have hu := hD H F0 st inst ls a ma mem src dst n cap o' off m j hcl h4 h15 h17 h18 h2 ha hfa
    hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hg.disj hsj (by omega) ho ho8
    hoff hm ht
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, hx | ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · rintro c' (⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, hroom, ls', hhl, rfl⟩)
    · exact contErr hR (by omega) he
    · exact contErr hR (by omega) he
    · refine Until.done (Or.inl ⟨_, ls', o' + m + 4, j, ?_, hhl, hj, hjn, by omega, by omega, rfl⟩)
      refine hg.setMem hm0 ?_ fun x hx => ?_
      · rw [matchRest_size, prologue_size]
      · rw [matchRest_low _ _ _ _ _ _ (by omega), prologue_low _ _ _ _ (by omega)]

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

/-- From X3: SegC, then X4 or the epilogue. -/
theorem contX3 (hC : SegC) (hD : SegD) (hR : ErrRet) {H : HostSem} {st : Store}
    {inst : ModuleInst} {ma src dst n cap o' off ml0 j ip0 : Nat} {c : Config}
    (hg : Good st inst ma src dst n cap) (hc : AtX3 F0 st inst src dst n cap o' off ml0 j c)
    (hj : ip0 < j) (hsj : src ≤ j) (hjn : j < src + n) (ho : dst ≤ o') (ho8 : o' + 8 ≤ dst + cap)
    (hoff : off < 65536) (hml : ml0 < 16) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) (IterExit inst ma src dst n cap ip0) c := by
  obtain ⟨ls, hcl, h4, h15, h17, h18, h2, rfl⟩ := hc
  obtain ⟨mem, hm0, hsz, ht⟩ := hg.mem
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hu := hC H F0 st inst ls ma mem src dst n cap o' off ml0 j hcl h4 h15 h17 h18 h2 hg.ma0
    hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hsj (by omega) hml (by omega)
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · rintro c' (⟨hl, hx⟩ | ⟨-, acc, j', he, hx⟩ | ⟨-, -, he⟩)
    · exact contX4 hD hR hg hx hj hsj hjn ho ho8 hoff (by omega)
    · obtain ⟨h1, h2, h3, h4⟩ := extM_bound he
      exact contX4 hD hR hg hx (by omega) (by omega) (by omega) ho ho8 hoff (by omega)
    · exact contErr hR (by omega) he

theorem off_lt (mem : MemInst) (p : Nat) :
    (mem.byte p).toNat + 256 * (mem.byte (p + 1)).toNat < 65536 := by
  have := (mem.byte p).toNat_lt; have := (mem.byte (p + 1)).toNat_lt; omega

/-- From X2: SegB, then the return (the last literals), the epilogue, or X3. -/
theorem contX2 (hB : SegB) (hC : SegC) (hD : SegD) (hR : ErrRet) {H : HostSem} {st : Store}
    {inst : ModuleInst} {ma src dst n cap op q len t ip0 : Nat} {c : Config}
    (hg : Good st inst ma src dst n cap) (hc : AtX2 F0 st inst src dst n cap op q len t c)
    (hq : ip0 < q) (hsq : src ≤ q) (hqn : q ≤ src + n) (hop : dst ≤ op) (hopc : op ≤ dst + cap)
    (hlen : len < 2 ^ 31) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) (IterExit inst ma src dst n cap ip0) c := by
  obtain ⟨ls, hcl, h3, h4, h2, h16, rfl⟩ := hc
  obtain ⟨a, ha, hfa⟩ := hg.a3
  obtain ⟨a4, ha4, hfa4⟩ := hg.a4
  obtain ⟨mem, hm0, hsz, ht⟩ := hg.mem
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hd0 := hg.dstLo
  have hu := hB H ⟨[], {}⟩ [] .hole st inst ls a a4 ma mem src dst n cap op q len t hcl h3 h4 h2
    h16 ha hfa ha4 hfa4 hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hg.disj hsq
    hqn hop hopc hlen
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · rintro c' (⟨-, -, -, hr⟩ | ⟨-, -, he⟩ | ⟨hnear, rfl⟩)
    · exact Until.done (Or.inr ⟨_, _, by simpa [Returned, Context.fill] using hr⟩)
    · exact contErr hR (by omega) ⟨q, hsq, by omega, he⟩
    · have hl := hcl.1
      refine contX3 (o' := op + len)
        (off := (mem.byte (q + len)).toNat + 256 * (mem.byte (q + len + 1)).toNat)
        (ml0 := t % 16) (j := q + len + 2) hC hD hR (hg.setMem hm0 (fwdCopy_size _ _ _ _)
        fun x hx => fwdCopy_outside _ _ _ _ _ (Or.inl (by omega))) ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        (by omega) (by omega) (by omega) (by omega) (by omega) (off_lt mem (q + len))
        (Nat.mod_lt _ (by decide))
      · exact ((((((hcl.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega)
          _).set (by omega) _).set (by omega) _)
      all_goals simp [hl]

theorem HeadLocals.const {ls : List Val} {src dst n cap op ip : Nat}
    (h : HeadLocals ls src dst n cap op ip) : ConstLocals ls src dst n cap := by
  obtain ⟨hl, h0, h1, -, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨hl, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem HeadLocals.of_const {ls : List Val} {src dst n cap op ip : Nat}
    (h : ConstLocals ls src dst n cap) (h3 : ls[3]? = some (vI op)) (h4 : ls[4]? = some (vI ip)) :
    HeadLocals ls src dst n cap op ip := by
  obtain ⟨hl, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨hl, h0, h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- One iteration from a good head: a good head further on, or func 2 returned. -/
theorem iter (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD) (hR : ErrRet)
    {H : HostSem} {st : Store} {inst : ModuleInst} {ls : List Val} {ma src dst n cap op ip : Nat}
    (hg : Good st inst ma src dst n cap) (hl : HeadLocals ls src dst n cap op ip)
    (hsip : src ≤ ip) (hipn : ip < src + n) (hop : dst ≤ op) (hopc : op ≤ dst + cap) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) (IterExit inst ma src dst n cap ip)
      (head st inst ls) := by
  obtain ⟨a, ha, hfa⟩ := hg.a3
  obtain ⟨mem, hm0, hsz, ht⟩ := hg.mem
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hd0 := hg.dstLo
  have hcl := hl.const
  have hln := hcl.1
  have hu := hS5 H (ctx2 F0) st inst ls a ma mem src dst n cap op ip hl ha hfa hg.ma0 hm0
    hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hg.disj hsip hipn hop hopc
  have hll16 : (mem.byte ip).toNat / 16 < 16 := by have := (mem.byte ip).toNat_lt; omega
  have hoffb : (mem.byte (ip + 1 + (mem.byte ip).toNat / 16)).toNat +
      256 * (mem.byte (ip + 2 + (mem.byte ip).toNat / 16)).toNat <
      65536 := by
    have := (mem.byte (ip + 1 + (mem.byte ip).toNat / 16)).toNat_lt
    have := (mem.byte (ip + 2 + (mem.byte ip).toNat / 16)).toNat_lt
    omega
  have hgood16 := hg.setMem hm0 (fwdCopy_size 16 mem op (ip + 1))
    fun x hx => fwdCopy_outside _ _ _ _ _ (Or.inl (by omega))
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · rintro c (⟨hll, rfl⟩ | ⟨hll, hsc, rfl⟩ | ⟨hll, hsc1, hsc2, -, rfl⟩ |
      ⟨hll, hsc1, hsc2, hml, -, -, rfl⟩ | ⟨hll, hsc1, hsc2, hml, -, hle, rfl⟩)
    · -- X1: the literal length's extension bytes
      have hA' := hA H F0 st inst (((ls.set 15 (vI (ip + 1))).set 16 (vI (mem.byte ip).toNat)).set 2
        (vI 15)) ma mem src dst n cap op ip (mem.byte ip).toNat
        (((hcl.set (by omega) _).set (by omega) _).set (by omega) _)
        (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]; exact hl.2.2.2.1)
        (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]; exact hl.2.2.2.2.1) (by simp [hln]) (by simp [hln])
        (by simp [hln]) hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hsip hipn
        (by omega)
      refine Until.trans (untilR1 hA' (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
      · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
        · exact Or.inr (Or.inr (Or.inl hx))
        · exact Or.inr (Or.inr (Or.inr hx))
      · exact Or.inr (Or.inr hx.2)
      · rintro c' (⟨acc, q, he, hx⟩ | ⟨-, he⟩)
        · obtain ⟨h1, h2, h3, h4⟩ := extM_bound he
          exact contX2 hB hC hD hR hg hx (by omega) (by omega) (by omega) hop hopc (by omega)
        · exact contErr hR (by omega) he
    · -- X2: no room for the shortcut
      have h3' : ((((ls.set 15 (vI (ip + 1))).set 16 (vI (mem.byte ip).toNat)).set 2
          (vI ((mem.byte ip).toNat / 16))).set 4 (vI (ip + 1)))[3]? = some (vI op) := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hl.2.2.2.1
      exact contX2 (q := ip + 1) (len := (mem.byte ip).toNat / 16) (t := (mem.byte ip).toNat)
        hB hC hD hR hg ⟨_, ((((hcl.set (by omega) _).set (by omega) _).set (by omega)
        _).set (by omega) _), h3', by simp [hln], by simp [hln], by simp [hln], rfl⟩
        (by omega) (by omega) (by omega) hop hopc (by omega)
    · -- X3: the match code with 16 literal bytes copied
      exact contX3 (o' := op + (mem.byte ip).toNat / 16)
        (off := ((mem.byte (ip + 1 + (mem.byte ip).toNat / 16)).toNat +
          256 * (mem.byte (ip + 2 + (mem.byte ip).toNat / 16)).toNat))
        (ml0 := (mem.byte ip).toNat % 16) (j := ip + 3 + (mem.byte ip).toNat / 16)
        hC hD hR hgood16 ⟨_, (((((((hcl.set (by omega) _).set (by omega) _).set
        (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _),
        by simp [hln], by simp [hln], by simp [hln], by simp [hln], by simp [hln], rfl⟩
        (by omega) (by omega) (by omega) (by omega) (by omega) hoffb
        (Nat.mod_lt _ (by decide))
    · -- X4: the match starts before `dst`
      exact contX4 (o' := op + (mem.byte ip).toNat / 16)
        (off := ((mem.byte (ip + 1 + (mem.byte ip).toNat / 16)).toNat +
          256 * (mem.byte (ip + 2 + (mem.byte ip).toNat / 16)).toNat))
        (m := (mem.byte ip).toNat % 16) (j := ip + 3 + (mem.byte ip).toNat / 16)
        hD hR hgood16 ⟨_, (((((((hcl.set (by omega) _).set (by omega) _).set
        (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _),
        by simp [hln], by simp [hln], by simp [hln], by simp [hln], by simp [hln], rfl⟩
        (by omega) (by omega) (by omega) (by omega) (by omega) hoffb (by omega)
    · -- X5: the shortcut, back to the head
      refine Until.done (Or.inl ⟨_, _, op + (mem.byte ip).toNat / 16 + (mem.byte ip).toNat % 16 + 4,
        ip + 3 + (mem.byte ip).toNat / 16, ?_, HeadLocals.of_const ((((((((((hcl.set (by omega)
        _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega)
        _).set (by omega) _).set (by omega) _).set (by omega) _)) (by simp [hln])
        (by simp [hln]), by omega, by omega, by omega, by omega, rfl⟩)
      refine hg.setMem hm0 (by simp) fun x hx => ?_
      rw [fwdCopy_outside _ _ _ _ _ (Or.inl (by omega)),
        fwdCopy_outside _ _ _ _ _ (Or.inl (by omega))]

/-- The main loop from a good head: func 2 returns one `i32`, inside R1's sets. -/
theorem loop (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD) (hR : ErrRet)
    {H : HostSem} {inst : ModuleInst} {ma src dst n cap : Nat} :
    ∀ k (st : Store) (ls : List Val) (op ip : Nat), src + n - ip = k →
      Good st inst ma src dst n cap → HeadLocals ls src dst n cap op ip → src ≤ ip →
      ip < src + n → dst ≤ op → op ≤ dst + cap →
      Until H (Within (R1R src n dst cap) (R1W dst cap))
        (fun c => ∃ st' v, c = ⟨st', ⟨[], {}⟩, vals [.i32 v]⟩) (head st inst ls) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro st ls op ip hk hg hl hsip hipn hop hopc
    refine Until.trans (iter hS5 hA hB hC hD hR hg hl hsip hipn hop hopc) ?_
    rintro c (⟨st', ls', op', ip', hg', hl', hlt, hipn', hop', hopc', rfl⟩ | hr)
    · exact ih _ (by omega) st' ls' op' ip' rfl hg' hl' (by omega) hipn' hop' hopc'
    · exact Until.done hr

end Subjects.Lz4C
