import FVATest.Subjects.Lz4C.Match

/-!
# func 2 ↔ `Model` (R2/R3's composition, contract U20)

From the cutpoint statements, assumed as hypotheses: from a main loop head holding the input at
`src` and the decoded prefix `out` at `dst`, an iteration does what `Model.step` says — the next
head with the model's next prefix, or func 2 returns the model's verdict: the decoded length with
the content held at `dst`, or a negative value. Proof support; outside the review surface.
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- `read_variable_length` from memory = `Model.ext` on the input held at `src`. -/
theorem extM_eq {mem : MemInst} {src L : Nat} {inp : List UInt8} (hin : HoldsAt mem src inp)
    (hL : L ≤ src) : ∀ fuel q acc, extM mem (src + inp.length - L) fuel (src + q) acc =
      (Model.ext inp L fuel q acc).map fun p => (p.1, src + p.2)
  | 0, _, _ => rfl
  | fuel + 1, q, acc => by
    simp only [extM, Model.ext]
    by_cases hq : q + 1 + L ≤ inp.length
    · have hb : (mem.byte (src + q)).toNat = Model.at! inp q := by
        rw [hin q (by omega), Model.at!_lt (by omega)]
        simp [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem (show q < inp.length by omega)]
      rw [ite_eq_left (by omega : src + q + 1 ≤ src + inp.length - L), ite_eq_left hq, hb]
      by_cases ha : acc + Model.at! inp q < 2 ^ 31
      · rw [ite_eq_left ha, ite_eq_left ha]
        by_cases h255 : Model.at! inp q = 255
        · rw [ite_eq_left h255, ite_eq_left h255, show src + q + 1 = src + (q + 1) by omega]
          exact extM_eq hin hL fuel (q + 1) _
        · rw [ite_eq_right h255, ite_eq_right h255]
          simp only [Option.map_some, show src + q + 1 = src + (q + 1) by omega]
      · rw [ite_eq_right ha, ite_eq_right ha]; rfl
    · rw [ite_eq_right (by omega), ite_eq_right hq]; rfl

/-- The input bytes from position `i`, held at `src + i`. -/
theorem HoldsAt.drop {mem : MemInst} {src : Nat} {inp : List UInt8} (h : HoldsAt mem src inp)
    (i k : Nat) : HoldsAt mem (src + i) ((inp.drop i).take k) := by
  intro j hj
  simp only [List.length_take, List.length_drop] at hj
  rw [show src + i + j = src + (i + j) by omega, h (i + j) (by omega)]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop,
    show j < k by omega]

/-- Bytes copied from a held source after a held prefix extend it. -/
theorem HoldsAt.append {mem : MemInst} {dst : Nat} {out lits : List UInt8}
    (h1 : HoldsAt mem dst out) (h2 : HoldsAt mem (dst + out.length) lits) :
    HoldsAt mem dst (out ++ lits) := by
  intro i hi
  simp only [List.length_append] at hi
  by_cases hio : i < out.length
  · rw [h1 i hio]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hio]
  · obtain ⟨j, rfl⟩ : ∃ j, i = out.length + j := ⟨i - out.length, by omega⟩
    rw [show dst + (out.length + j) = dst + out.length + j by omega, h2 j (by omega)]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right]

/-- `memmove` of `len` held bytes to the end of a held prefix appends them. -/
theorem move_holds {mem : MemInst} {dst op q : Nat} {out lits : List UInt8}
    (hh : HoldsAt mem dst out) (hop : op = dst + out.length) (hl : HoldsAt mem q lits) :
    HoldsAt (move mem op q lits.length) dst (out ++ lits) := by
  refine HoldsAt.append (fun i hi => ?_) fun i hi => ?_
  · simp only [move]; rw [ite_eq_right (by omega)]; exact hh i hi
  · simp only [move]; rw [ite_eq_left (by omega), ← hop, Nat.add_sub_cancel_left]; exact hl i hi

/-- A forward copy of `k ≥ len` bytes from a held source that the destination range does not
reach before it is read: the prefix extended by the first `len`. -/
theorem fwdCopy_holds {mem : MemInst} {dst op q k : Nat} {out lits : List UInt8}
    (hh : HoldsAt mem dst out) (hop : op = dst + out.length) (hl : HoldsAt mem q lits)
    (hk : lits.length ≤ k) (hd : op ≤ q ∨ q + k ≤ op) :
    HoldsAt (fwdCopy mem op q k) dst (out ++ lits) := by
  refine HoldsAt.append (fun i hi => ?_) fun i hi => ?_
  · rw [fwdCopy_outside _ _ _ _ _ (Or.inl (by omega))]; exact hh i hi
  · rw [← hop, fwdCopy_byte _ _ _ _ hd i (by omega)]; exact hl i hi

theorem copy_some : ∀ (k : Nat) {out : List UInt8} {off : Nat}, off ≤ out.length →
    ∃ o, Lz4.copy out off k = some o
  | 0, out, _, _ => ⟨out, rfl⟩
  | k + 1, out, off, h => by
    unfold Lz4.copy
    rw [ite_eq_left h]
    exact copy_some k (by simp; omega)

theorem prologue_high (mem : MemInst) (o' off a : Nat) (h : o' + 8 ≤ a) :
    (prologue mem o' off).1.byte a = mem.byte a := by
  unfold prologue
  split
  · exact fwdCopy_outside _ _ _ _ _ (Or.inr (by omega))
  · rw [fwdCopy_outside _ _ _ _ _ (Or.inr (by omega)),
      fwdCopy_outside _ _ _ _ _ (Or.inr (by omega)), write4_zero, ite_eq_right (by omega)]

theorem matchRest_high (mem : MemInst) (o' m oend a : Nat) (mp : BitVec 32)
    (hroom : o' + m + 4 + 5 ≤ oend) (h : oend ≤ a) :
    (matchRest mem o' m oend mp).byte a = mem.byte a := by
  simp only [matchRest]
  split
  · split
    · exact fwdCopy_outside _ _ _ _ _ (Or.inr (by omega))
    · rw [fwdCopy_outside _ _ _ _ _ (Or.inr (by simp only [chunks]; omega)),
        fwdCopy_outside _ _ _ _ _ (Or.inr (by omega))]
  · by_cases hl : o' + 8 < oend - 7
    · simp only [hl, ite_true]
      split
      · rw [fwdCopy_outside _ _ _ _ _ (Or.inr (by omega)),
          fwdCopy_outside _ _ _ _ _ (Or.inr (by simp only [chunks]; omega))]
      · exact fwdCopy_outside _ _ _ _ _ (Or.inr (by simp only [chunks]; omega))
    · simp only [hl, ite_false]
      split
      · exact fwdCopy_outside _ _ _ _ _ (Or.inr (by omega))
      · rfl

/-- The model's verdict `r` returned by func 2: the decoded length with the content held at `dst`
in memory `ma`, or a negative value. -/
def Verdict (ma dst : Nat) (r : Option (List UInt8)) (c : Config) : Prop :=
  ∃ st' v, c = ⟨st', ⟨[], {}⟩, vals [.i32 v]⟩ ∧ match r with
    | some o => v = BitVec.ofNat 32 o.length ∧
        ∃ mem, st'.mems[ma]? = some mem ∧ dst + o.length ≤ mem.size ∧ HoldsAt mem dst o
    | none => v.toInt < 0

/-- A main loop head simulating model state `(i, out)`: good, at `src + i` and
`dst + out.length`, holding the input at `src` and the prefix at `dst`. -/
def SimHead (inst : ModuleInst) (ma src dst cap : Nat) (inp : List UInt8) (i : Nat)
    (out : List UInt8) (c : Config) : Prop :=
  ∃ st ls mem, Good st inst ma src dst inp.length cap ∧
    HeadLocals ls src dst inp.length cap (dst + out.length) (src + i) ∧ st.mems[ma]? = some mem ∧
    HoldsAt mem src inp ∧ HoldsAt mem dst out ∧ i < inp.length ∧ out.length ≤ cap ∧
    c = mainHead st inst ls

/-- Where func 2 goes for the model's outcome of a sequence started at `i0`. -/
def OutExit (inst : ModuleInst) (ma src dst cap : Nat) (inp : List UInt8) (i0 : Nat) :
    Model.Out → Config → Prop
  | .cont i' out', c => i0 < i' ∧ SimHead inst ma src dst cap inp i' out' c
  | .done out', c => Verdict ma dst (some out') c
  | .err, c => Verdict ma dst none c

/-- `Model.copyMatch` once the match length `m` and the next position `i'` are known. -/
def matchOut (cap i' : Nat) (out : List UInt8) (off m : Nat) : Model.Out :=
  if out.length < off then .err
  else if cap < out.length + (m + 4) + 5 then .err
  else match Lz4.copy out off (m + 4) with
    | some out' => .cont i' out'
    | none => .err

theorem copyMatch_lt {inp : List UInt8} {cap j off ml0 : Nat} {out : List UInt8}
    (h : ml0 < 15) : Model.copyMatch inp cap j out off ml0 = matchOut cap j out off ml0 := by
  simp only [Model.copyMatch, ite_eq_right (show ml0 ≠ 15 by omega)]; rfl

theorem copyMatch_ext {inp : List UInt8} {cap j off : Nat} {out : List UInt8} :
    Model.copyMatch inp cap j out off 15 = match Model.ext inp 4 inp.length j 0 with
      | none => .err
      | some (a, q) => matchOut cap q out off (15 + a) := by
  simp only [Model.copyMatch, ite_true]
  cases Model.ext inp 4 inp.length j 0 with
  | none => rfl
  | some p => rfl

/-- An error exit returns a negative value through the epilogue. -/
theorem contErrSim (hR : ErrRet) {H : HostSem} {st : Store} {inst : ModuleInst}
    {ma src dst n cap : Nat} {Q : Config → Prop} {c : Config} (hs : src + n + 1 < 2 ^ 32)
    (hn : n + 1 < 2 ^ 31) (hq : ∀ c, Verdict ma dst none c → Q c)
    (hc : Err F0 st inst src dst n cap c) :
    Until H (Within (R1R src n dst cap) (R1W dst cap)) Q c := by
  obtain ⟨v, hv1, hv, he⟩ := hc
  exact (untilR1 (hR H st inst src dst n cap v c he (by omega) (by omega)) (fun _ _ h => h.elim)
    (fun _ _ h => h.elim)).mono (fun _ h => h) fun c' h =>
      hq c' ⟨st, _, h, errVal_neg hv1 (by omega)⟩

/-- A memory change inside `[lo, hi) ⊆ [dst, dst + cap)` keeps the input held. -/
theorem HoldsAt.of_disj {mem mem' : MemInst} {src dst cap lo hi : Nat} {inp : List UInt8}
    (h : HoldsAt mem src inp) (hd : src + inp.length ≤ dst ∨ dst + cap ≤ src) (hlo : dst ≤ lo)
    (hhi : hi ≤ dst + cap)
    (he : ∀ a, (a < lo ∨ hi ≤ a) → mem'.byte a = mem.byte a) : HoldsAt mem' src inp :=
  h.of_outside fun a ha hb => he a (by omega)

/-- From X4 simulating `out` (the literals appended): SegD, then the model's `matchOut`. -/
theorem contX4Sim (hD : SegD) (hR : ErrRet) {H : HostSem} {st : Store} {inst : ModuleInst}
    {ma src dst cap o' off m j i0 : Nat} {inp out : List UInt8} {mem : MemInst} {c : Config}
    (hg : Good st inst ma src dst inp.length cap)
    (hc : AtX4 F0 st inst src dst inp.length cap o' off m j c) (hm0 : st.mems[ma]? = some mem)
    (hin : HoldsAt mem src inp) (hh : HoldsAt mem dst out) (ho : o' = dst + out.length)
    (hj : i0 < j - src) (hsj : src ≤ j) (hjn : j < src + inp.length) (ho8 : o' + 8 ≤ dst + cap)
    (hoff : off < 65536) (hm : m < 2 ^ 31) :
    Until H (Within (R1R src inp.length dst cap) (R1W dst cap))
      (OutExit inst ma src dst cap inp i0 (matchOut cap (j - src) out off m)) c := by
  obtain ⟨ls, hcl, h4, h15, h17, h18, h2, rfl⟩ := hc
  obtain ⟨a, ha, hfa⟩ := hg.a3
  obtain ⟨mem₀, hm₀, hsz, ht⟩ := hg.mem
  obtain rfl : mem₀ = mem := Option.some.inj (hm₀.symm.trans hm0)
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hd0 := hg.dstLo
  have hs0 := hg.srcLo
  have hu := hD H F0 st inst ls a ma mem₀ src dst inp.length cap o' off m j hcl h4 h15 h17 h18 h2
    ha hfa hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hg.disj hsj (by omega)
    (by omega) ho8 hoff hm ht
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, hx | ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · rintro c' (⟨hlt, he⟩ | ⟨hge, hroom, he⟩ | ⟨hge, hroom, ls', hhl, rfl⟩)
    · refine contErrSim (ma := ma) hR (by omega) (by omega) (fun c h => ?_) he
      simp only [matchOut, ite_eq_left (show out.length < off by omega)]
      exact h
    · refine contErrSim (ma := ma) hR (by omega) (by omega) (fun c h => ?_) he
      simp only [matchOut, ite_eq_right (show ¬ out.length < off by omega),
        ite_eq_left (show cap < out.length + (m + 4) + 5 by omega)]
      exact h
    · obtain ⟨out', hcopy⟩ := copy_some (m + 4) (show off ≤ out.length by omega)
      have hlen := Model.copy_length hcopy
      simp only [matchOut, ite_eq_right (show ¬ out.length < off by omega),
        ite_eq_right (show ¬ cap < out.length + (m + 4) + 5 by omega), hcopy]
      refine Until.done ⟨by omega, _, ls', _, ?_, ?_, setMem_mems hm0, ?_,
        match_holds hh ho (by omega) hoff (by omega) (by omega) ht hcopy, by omega, by omega, rfl⟩
      · refine hg.setMem hm0 ?_ fun x hx => ?_
        · rw [matchRest_size, prologue_size]
        · rw [matchRest_low _ _ _ _ _ _ (by omega), prologue_low _ _ _ _ (by omega)]
      · rw [show dst + out'.length = o' + m + 4 by omega, show src + (j - src) = j by omega]
        exact hhl
      · refine hin.of_disj hg.disj (lo := o') (hi := dst + cap) (by omega) (Nat.le_refl _)
          fun x hx => ?_
        rcases hx with hx | hx
        · rw [matchRest_low _ _ _ _ _ _ (by omega), prologue_low _ _ _ _ hx]
        · rw [matchRest_high _ _ _ _ _ _ hroom hx, prologue_high _ _ _ _ (by omega)]

theorem ext_some {mem : MemInst} {src L j acc j' : Nat} {inp : List UInt8}
    (hin : HoldsAt mem src inp) (hL : L ≤ src) (hsj : src ≤ j)
    (he : extM mem (src + inp.length - L) inp.length j 0 = some (acc, j')) :
    src ≤ j' ∧ Model.ext inp L inp.length (j - src) 0 = some (acc, j' - src) := by
  have h := extM_eq hin hL inp.length (j - src) 0
  rw [show src + (j - src) = j by omega, he] at h
  cases hx : Model.ext inp L inp.length (j - src) 0 with
  | none => rw [hx] at h; simp at h
  | some p =>
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, ?_⟩
    rw [h1, h2, Nat.add_sub_cancel_left]

theorem ext_none {mem : MemInst} {src L j : Nat} {inp : List UInt8}
    (hin : HoldsAt mem src inp) (hL : L ≤ src) (hsj : src ≤ j)
    (he : extM mem (src + inp.length - L) inp.length j 0 = none) :
    Model.ext inp L inp.length (j - src) 0 = none := by
  have h := extM_eq hin hL inp.length (j - src) 0
  rw [show src + (j - src) = j by omega, he] at h
  cases hx : Model.ext inp L inp.length (j - src) 0 with
  | none => rfl
  | some p => rw [hx] at h; simp at h

/-- From X3 simulating `out` (the literals appended): SegC, then the model's `copyMatch` from
position `j − src`. -/
theorem contX3Sim (hC : SegC) (hD : SegD) (hR : ErrRet) {H : HostSem} {st : Store}
    {inst : ModuleInst} {ma src dst cap o' off ml0 j i0 : Nat} {inp out : List UInt8}
    {mem : MemInst} {c : Config} (hg : Good st inst ma src dst inp.length cap)
    (hc : AtX3 F0 st inst src dst inp.length cap o' off ml0 j c) (hm0 : st.mems[ma]? = some mem)
    (hin : HoldsAt mem src inp) (hh : HoldsAt mem dst out) (ho : o' = dst + out.length)
    (hj : i0 < j - src) (hsj : src ≤ j) (hjn : j < src + inp.length) (ho8 : o' + 8 ≤ dst + cap)
    (hoff : off < 65536) (hml : ml0 < 16) :
    Until H (Within (R1R src inp.length dst cap) (R1W dst cap))
      (OutExit inst ma src dst cap inp i0 (Model.copyMatch inp cap (j - src) out off ml0)) c := by
  obtain ⟨ls, hcl, h4, h15, h17, h18, h2, rfl⟩ := hc
  obtain ⟨mem₀, hm₀, hsz, ht⟩ := hg.mem
  obtain rfl : mem₀ = mem := Option.some.inj (hm₀.symm.trans hm0)
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hs0 := hg.srcLo
  have hu := hC H F0 st inst ls ma mem₀ src dst inp.length cap o' off ml0 j hcl h4 h15 h17 h18 h2
    hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hsj (by omega) hml (by omega)
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · rintro c' (⟨hl, hx⟩ | ⟨rfl, acc, j', he, hx⟩ | ⟨rfl, he, herr⟩)
    · rw [copyMatch_lt hl]
      exact contX4Sim hD hR hg hx hm0 hin hh ho hj hsj hjn ho8 hoff (by omega)
    · obtain ⟨h1, h2, h3, h4⟩ := extM_bound he
      obtain ⟨hsj', hext⟩ := ext_some hin (by omega) hsj he
      rw [copyMatch_ext, hext]
      exact contX4Sim hD hR hg hx hm0 hin hh ho (by omega) hsj' (by omega) ho8 hoff (by omega)
    · rw [copyMatch_ext, ext_none hin (by omega) hsj he]
      exact contErrSim (ma := ma) hR (by omega) (by omega) (fun c h => h) herr

theorem at!_eq {mem : MemInst} {src i : Nat} {inp : List UInt8} (hin : HoldsAt mem src inp)
    (hi : i < inp.length) : (mem.byte (src + i)).toNat = Model.at! inp i := by
  rw [hin i hi, Model.at!_lt hi]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- From X2 simulating `out`: SegB, then the model's general literal path from `q − src`. -/
theorem contX2Sim (hB : SegB) (hC : SegC) (hD : SegD) (hR : ErrRet) {H : HostSem} {st : Store}
    {inst : ModuleInst} {ma src dst cap op q len t i0 : Nat} {inp out : List UInt8}
    {mem : MemInst} {c : Config} (hg : Good st inst ma src dst inp.length cap)
    (hc : AtX2 F0 st inst src dst inp.length cap op q len t c) (hm0 : st.mems[ma]? = some mem)
    (hin : HoldsAt mem src inp) (hh : HoldsAt mem dst out) (hop : op = dst + out.length)
    (hq : i0 < q - src) (hsq : src ≤ q) (hqn : q ≤ src + inp.length) (hopc : op ≤ dst + cap)
    (hlen : len < 2 ^ 31) :
    Until H (Within (R1R src inp.length dst cap) (R1W dst cap))
      (OutExit inst ma src dst cap inp i0
        (Model.literal inp cap (q - src) out len (t % 16))) c := by
  obtain ⟨ls, hcl, h3, h4, h2, h16, rfl⟩ := hc
  obtain ⟨a, ha, hfa⟩ := hg.a3
  obtain ⟨a4, ha4, hfa4⟩ := hg.a4
  obtain ⟨mem₀, hm₀, hsz, ht⟩ := hg.mem
  have hmeq : mem₀ = mem := Option.some.inj (hm₀.symm.trans hm0)
  rw [hmeq] at hsz ht
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hd0 := hg.dstLo
  have hs0 := hg.srcLo
  have hu := hB H ⟨[], {}⟩ [] .hole st inst ls a a4 ma mem src dst inp.length cap op q len t hcl h3
    h4 h2 h16 ha hfa ha4 hfa4 hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega)
    hg.disj hsq hqn (by omega) hopc hlen
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · have hlits := hin.drop (q - src) len
    rw [show src + (q - src) = q by omega] at hlits
    rintro c' (⟨hnear, hend, hroom, hr⟩ | ⟨hnear, hnot, he⟩ | ⟨hnear, rfl⟩)
    · -- the last literals: the model's `.done`
      have hll : ((inp.drop (q - src)).take len).length = len := by simp; omega
      simp only [Model.literal, ite_eq_left (show cap < out.length + len + 12 ∨
        inp.length < q - src + len + 8 by omega),
        ite_eq_left (show q - src + len = inp.length ∧ out.length + len ≤ cap by omega)]
      refine Until.done ⟨_, _, by simpa [Returned, Context.fill] using hr, ?_, _,
        setMem_mems hm0, ?_, ?_⟩
      · simp only [List.length_append, hll]; congr 1; omega
      · simp only [List.length_append, hll]
        show dst + (out.length + len) ≤ mem.pages * 65536
        rw [show mem.pages * 65536 = mem.size from rfl]; omega
      · have := move_holds hh hop hlits
        rwa [hll] at this
    · simp only [Model.literal, ite_eq_left (show cap < out.length + len + 12 ∨
        inp.length < q - src + len + 8 by omega),
        ite_eq_right (show ¬ (q - src + len = inp.length ∧ out.length + len ≤ cap) by omega)]
      exact contErrSim (ma := ma) hR (by omega) (by omega) (fun c h => h) ⟨q, hsq, by omega, he⟩
    · have hl := hcl.1
      have hll : ((inp.drop (q - src)).take len).length = len := by simp; omega
      simp only [Model.literal, ite_eq_right (show ¬ (cap < out.length + len + 12 ∨
        inp.length < q - src + len + 8) by omega)]
      have hoff : (mem.byte (q + len)).toNat + 256 * (mem.byte (q + len + 1)).toNat =
          Model.off16 inp (q - src + len) := by
        rw [Model.off16, show q + len = src + (q - src + len) by omega,
          show src + (q - src + len) + 1 = src + (q - src + len + 1) by omega,
          at!_eq hin (by omega), at!_eq hin (by omega)]
      have hmem := fwdCopy_holds (k := 8 * chunks op (op + len)) hh hop hlits
        (by simp only [chunks]; omega) (by
          rcases hg.disj with h | h
          · right; simp only [chunks]; omega
          · left; omega)
      rw [show q - src + len + 2 = q + len + 2 - src by omega]
      refine contX3Sim (o' := op + len) (off := Model.off16 inp (q - src + len))
        (ml0 := t % 16) (j := q + len + 2) (out := out ++ (inp.drop (q - src)).take len) hC hD hR
        (hg.setMem hm0 (fwdCopy_size _ _ _ _)
          fun x hx => fwdCopy_outside _ _ _ _ _ (Or.inl (by omega)))
        ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ (setMem_mems hm0)
        (hin.of_disj hg.disj (lo := op) (hi := dst + cap) (by omega) (Nat.le_refl _)
          fun x hx => fwdCopy_outside _ _ _ _ _ (by
            rcases hx with hx | hx
            · exact Or.inl hx
            · right; simp only [chunks]; omega))
        hmem (by simp only [List.length_append, hll]; omega) (by omega) (by omega) (by omega)
        (by omega) (by rw [← hoff]; exact off_lt mem (q + len)) (Nat.mod_lt _ (by decide))
      · exact ((((((hcl.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega)
          _).set (by omega) _).set (by omega) _)
      all_goals simp [hl, hoff]

/-- One iteration from a head simulating `(i, out)` does what `Model.step` says. -/
theorem iterSim (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD) (hR : ErrRet)
    {H : HostSem} {inst : ModuleInst} {ma src dst cap i : Nat} {inp out : List UInt8} {c : Config}
    (hc : SimHead inst ma src dst cap inp i out c) :
    Until H (Within (R1R src inp.length dst cap) (R1W dst cap))
      (OutExit inst ma src dst cap inp i (Model.step inp cap i out)) c := by
  obtain ⟨st, ls, mem, hg, hl, hm0, hin, hh, hi, hcap, rfl⟩ := hc
  obtain ⟨a, ha, hfa⟩ := hg.a3
  obtain ⟨mem₀, hm₀, hsz, ht⟩ := hg.mem
  have hmeq : mem₀ = mem := Option.some.inj (hm₀.symm.trans hm0)
  rw [hmeq] at hsz ht
  have hb := hg.srcHi
  have hb' := hg.dstHi
  have hd0 := hg.dstLo
  have hs0 := hg.srcLo
  have hcl := hl.const
  have hln := hcl.1
  have hu := hS5 H (ctx2 F0) st inst ls a ma mem src dst inp.length cap (dst + out.length) (src + i)
    hl ha hfa hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) hg.disj (by omega)
    (by omega) (by omega) (by omega)
  have ht0 : (mem.byte (src + i)).toNat = Model.at! inp i := at!_eq hin hi
  have hll16 : (mem.byte (src + i)).toNat / 16 < 16 := by
    have := (mem.byte (src + i)).toNat_lt; omega
  have hgood16 := hg.setMem hm0 (fwdCopy_size 16 mem (dst + out.length) (src + i + 1))
    fun x hx => fwdCopy_outside _ _ _ _ _ (Or.inl (by omega))
  simp only [Model.step, ← ht0]
  refine Until.trans (untilR1 hu (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
  · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr hx.2)
  · -- the 16 literal bytes the shortcut copies, as the model's literals
    have hshort : ∀ ll, ll < 15 → src + i + 1 + 16 < src + inp.length →
        dst + out.length + 32 ≤ dst + cap →
        HoldsAt (fwdCopy mem (dst + out.length) (src + i + 1) 16) dst
          (out ++ (inp.drop (i + 1)).take ll) ∧ ((inp.drop (i + 1)).take ll).length = ll ∧
        HoldsAt (fwdCopy mem (dst + out.length) (src + i + 1) 16) src inp := by
      intro ll hll hr1 hr2
      have hlits := hin.drop (i + 1) ll
      rw [show src + (i + 1) = src + i + 1 by omega] at hlits
      refine ⟨fwdCopy_holds hh rfl hlits (by simp; omega) (by
          rcases hg.disj with h | h
          · right; omega
          · left; omega), by simp; omega, ?_⟩
      exact hin.of_disj hg.disj (lo := dst + out.length) (hi := dst + cap) (by omega)
        (Nat.le_refl _) fun x hx => fwdCopy_outside _ _ _ _ _ (by omega)
    have hoffeq : (mem.byte (src + i + 1 + (mem.byte (src + i)).toNat / 16)).toNat +
        256 * (mem.byte (src + i + 2 + (mem.byte (src + i)).toNat / 16)).toNat =
        Model.off16 inp (i + 1 + (mem.byte (src + i)).toNat / 16) ∨
        ¬ (src + i + 1 + 16 < src + inp.length) := by
      by_cases hr : src + i + 1 + 16 < src + inp.length
      · left
        rw [Model.off16, show src + i + 1 + (mem.byte (src + i)).toNat / 16 =
            src + (i + 1 + (mem.byte (src + i)).toNat / 16) by omega,
          show src + i + 2 + (mem.byte (src + i)).toNat / 16 =
            src + (i + 1 + (mem.byte (src + i)).toNat / 16 + 1) by omega,
          at!_eq (i := i + 1 + (mem.byte (src + i)).toNat / 16) hin (by omega),
          at!_eq (i := i + 1 + (mem.byte (src + i)).toNat / 16 + 1) hin (by omega)]
      · exact Or.inr hr
    have hoffb : (mem.byte (src + i + 1 + (mem.byte (src + i)).toNat / 16)).toNat +
        256 * (mem.byte (src + i + 2 + (mem.byte (src + i)).toNat / 16)).toNat < 65536 := by
      have := (mem.byte (src + i + 1 + (mem.byte (src + i)).toNat / 16)).toNat_lt
      have := (mem.byte (src + i + 2 + (mem.byte (src + i)).toNat / 16)).toNat_lt
      omega
    rintro c (⟨hll, rfl⟩ | ⟨hll, hsc, rfl⟩ | ⟨hll, hsc1, hsc2, hmo, rfl⟩ |
      ⟨hll, hsc1, hsc2, hml, hoff8, hlt, rfl⟩ | ⟨hll, hsc1, hsc2, hml, hoff8, hle, rfl⟩)
    · -- X1: the literal length's extension bytes, then the general literal path
      rw [ite_eq_left hll]
      have hA' := hA H F0 st inst (((ls.set 15 (some (vI (src + i + 1)))).set 16
        (some (vI (mem.byte (src + i)).toNat))).set 2 (some (vI 15))) ma mem src dst inp.length cap
        (dst + out.length) (src + i) (mem.byte (src + i)).toNat
        (((hcl.set (by omega) _).set (by omega) _).set (by omega) _)
        (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]; exact hl.2.2.2.1)
        (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega)]; exact hl.2.2.2.2.1) (by simp [hln]) (by simp [hln])
        (by simp [hln]) hg.ma0 hm0 hg.srcLo hg.dstLo (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      refine Until.trans (untilR1 hA' (fun _ x hx => ?_) (fun _ x hx => ?_)) ?_
      · obtain ⟨-, ⟨-, hx⟩ | ⟨-, hx⟩⟩ := hx
        · exact Or.inr (Or.inr (Or.inl hx))
        · exact Or.inr (Or.inr (Or.inr hx))
      · exact Or.inr (Or.inr hx.2)
      · rintro c' (⟨acc, q, he, hx⟩ | ⟨he, herr⟩)
        · obtain ⟨h1, h2, h3, h4⟩ := extM_bound he
          obtain ⟨hsq, hext⟩ := ext_some hin (by omega) (by omega) he
          rw [show src + i + 1 - src = i + 1 by omega] at hext
          rw [hext]
          exact contX2Sim hB hC hD hR hg hx hm0 hin hh rfl (by omega) hsq (by omega) (by omega)
            (by omega)
        · rw [show i + 1 = src + i + 1 - src by omega, ext_none hin (by omega) (by omega) he]
          exact contErrSim (ma := ma) hR (by omega) (by omega) (fun c h => h) herr
    · -- X2: no room for the shortcut, the general literal path
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have h3' :
          ((((ls.set 15 (some (vI (src + i + 1)))).set 16
          (some (vI (mem.byte (src + i)).toNat))).set 2
          (some (vI ((mem.byte (src + i)).toNat / 16)))).set 4 (some (vI (src + i + 1))))[3]? =
          some (some (vI (dst + out.length))) := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hl.2.2.2.1
      have hx := contX2Sim (H := H) (q := src + i + 1) (len := (mem.byte (src + i)).toNat / 16)
        (t := (mem.byte (src + i)).toNat) (i0 := i) hB hC hD hR hg ⟨_, ((((hcl.set (by omega)
        _).set (by omega) _).set (by omega) _).set (by omega) _), h3', by simp [hln],
        by simp [hln], by simp [hln], rfl⟩ hm0 hin hh rfl (by omega) (by omega) (by omega)
        (by omega) (by omega)
      rwa [show src + i + 1 - src = i + 1 by omega] at hx
    · -- X3: the match code with 16 literal bytes copied
      obtain ⟨hlh, hlen, hinh⟩ := hshort _ hll hsc1 hsc2
      rcases hoffeq with hoffeq | hoffeq
      · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ← hoffeq,
          ite_eq_right (by omega)]
        rw [show i + 1 + (mem.byte (src + i)).toNat / 16 + 2 =
          src + i + 3 + (mem.byte (src + i)).toNat / 16 - src by omega]
        refine contX3Sim (o' := dst + out.length + (mem.byte (src + i)).toNat / 16)
          hC hD hR hgood16 ⟨_, (((((((hcl.set (by omega) _).set (by omega) _).set
          (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _),
          by simp [hln], by simp [hln], by simp [hln], by simp [hln], by simp [hln], rfl⟩
          (setMem_mems hm0) hinh hlh (by simp [hlen]; omega) (by omega) (by omega) (by omega)
          (by omega) hoffb (Nat.mod_lt _ (by decide))
      · exact absurd hsc1 hoffeq
    · -- X4: the match starts before `dst`
      obtain ⟨hlh, hlen, hinh⟩ := hshort _ hll hsc1 hsc2
      rcases hoffeq with hoffeq | hoffeq
      · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ← hoffeq,
          ite_eq_left ⟨by omega, by omega⟩, ite_eq_right (by omega)]
        have hmo : matchOut cap (src + i + 3 + (mem.byte (src + i)).toNat / 16 - src)
            (out ++ (inp.drop (i + 1)).take ((mem.byte (src + i)).toNat / 16))
            ((mem.byte (src + i + 1 + (mem.byte (src + i)).toNat / 16)).toNat +
              256 * (mem.byte (src + i + 2 + (mem.byte (src + i)).toNat / 16)).toNat)
            ((mem.byte (src + i)).toNat % 16) = .err := by
          simp only [matchOut, List.length_append, hlen]
          rw [ite_eq_left (by omega)]
        rw [← hmo]
        refine contX4Sim (o' := dst + out.length + (mem.byte (src + i)).toNat / 16) hD hR hgood16
          ⟨_, (((((((hcl.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega)
          _).set (by omega) _).set (by omega) _).set (by omega) _), by simp [hln],
          by simp [hln], by simp [hln], by simp [hln], by simp [hln], rfl⟩
          (setMem_mems hm0) hinh hlh (by simp [hlen]; omega) (by omega) (by omega) (by omega)
          (by omega) hoffb (by omega)
      · exact absurd hsc1 hoffeq
    · -- X5: the shortcut, back to the head
      obtain ⟨hlh, hlen, hinh⟩ := hshort _ hll hsc1 hsc2
      rcases hoffeq with hoffeq | hoffeq
      · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ← hoffeq,
          ite_eq_left ⟨by omega, by omega⟩, ite_eq_left (by omega)]
        obtain ⟨out', hcopy⟩ := copy_some ((mem.byte (src + i)).toNat % 16 + 4)
          (out := out ++ (inp.drop (i + 1)).take ((mem.byte (src + i)).toNat / 16))
          (off := (mem.byte (src + i + 1 + (mem.byte (src + i)).toNat / 16)).toNat +
            256 * (mem.byte (src + i + 2 + (mem.byte (src + i)).toNat / 16)).toNat)
          (show _ ≤ _ by simp [hlen]; omega)
        have hol := Model.copy_length hcopy
        simp only [List.length_append, hlen] at hol
        rw [hcopy]
        have hlits := hin.drop (i + 1) ((mem.byte (src + i)).toNat / 16)
        rw [show src + (i + 1) = src + i + 1 by omega] at hlits
        have hheld := shortcut_holds hh rfl (by rcases hg.disj with h | h <;> omega) hlits
          (by simp; omega) (by omega) (by omega) hcopy
        rw [hlen] at hheld
        refine Until.done ⟨by omega, _, _, _, ?_, ?_, setMem_mems hm0, ?_, hheld, by omega,
          by omega, rfl⟩
        · refine hg.setMem hm0 (by simp) fun x hx => ?_
          rw [fwdCopy_outside _ _ _ _ _ (Or.inl (by omega)),
            fwdCopy_outside _ _ _ _ _ (Or.inl (by omega))]
        · rw [show dst + out'.length = dst + out.length + (mem.byte (src + i)).toNat / 16 +
            (mem.byte (src + i)).toNat % 16 + 4 by omega,
            show src + (i + 1 + (mem.byte (src + i)).toNat / 16 + 2) =
            src + i + 3 + (mem.byte (src + i)).toNat / 16 by omega]
          exact HeadLocals.of_const ((((((((((hcl.set (by omega) _).set (by omega) _).set
            (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _).set (by omega)
            _).set (by omega) _).set (by omega) _)) (by simp [hln]) (by simp [hln])
        · exact hin.of_disj hg.disj (lo := dst + out.length) (hi := dst + cap) (by omega)
            (Nat.le_refl _) fun x hx => by
              rw [fwdCopy_outside _ _ _ _ _ (by omega), fwdCopy_outside _ _ _ _ _ (by omega)]
      · exact absurd hsc1 hoffeq

/-- The main loop from a head simulating `(i, out)`, with fuel for every sequence left: func 2
returns `Model.loop`'s verdict. -/
theorem loopSim (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD) (hR : ErrRet)
    {H : HostSem} {inst : ModuleInst} {ma src dst cap : Nat} {inp : List UInt8} :
    ∀ k i (out : List UInt8) (c : Config) fuel, inp.length - i = k → k ≤ fuel →
      SimHead inst ma src dst cap inp i out c →
      Until H (Within (R1R src inp.length dst cap) (R1W dst cap))
        (Verdict ma dst (Model.loop inp cap fuel i out)) c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i out c fuel hk hf hc
    have hi : i < inp.length := by obtain ⟨_, _, _, _, _, _, _, _, hi, _⟩ := hc; exact hi
    cases fuel with
    | zero => omega
    | succ f =>
      refine Until.trans (iterSim hS5 hA hB hC hD hR hc) fun c' hx => ?_
      simp only [Model.loop]
      cases hr : Model.step inp cap i out with
      | cont i' out' =>
        rw [hr] at hx
        obtain ⟨hlt, hsh⟩ := hx
        have hi' : i' < inp.length := by obtain ⟨_, _, _, _, _, _, _, _, hi', _⟩ := hsh; exact hi'
        exact ih (inp.length - i') (by omega) i' out' c' f rfl (by omega) hsh
      | done out' => rw [hr] at hx; exact Until.done hx
      | err => rw [hr] at hx; exact Until.done hx

end Subjects.Lz4C
