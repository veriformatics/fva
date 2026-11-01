import FVATest.Subjects.Lz4C.Loop
import FVATest.Subjects.Lz4C.ExtDirect
import FVATest.Subjects.Lz4C.Cut.ErrRet

/-! `SegA` (`Seg.lean`) by stepping around checkpoint 1's loop lemma `ExtL1` (`ExtDirect.ext_l1`):
the two bound checks, the first extension byte, the loop for the rest, the length's overflow
guards; `extM` = what `ExtL1`'s exits read (proof support; outside the review surface). -/

namespace Subjects.Lz4C.Cut

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.Lz4C

/-- The first bound check (`ip + 1 < iend − 15`). -/
def g1 : List Instr := [.localGet 15, .localGet 14, .irelop .w32 (.lt .u), .brIf 0, .localGet 15,
  .localSet 4, .br 7]

/-- The second bound check (`ip + 2 ≤ iend − 15`, implied by the first). -/
def g2 : List Instr := [.localGet 4, .iconst .w32 2, .ibinop .w32 .add, .localTee 2, .localGet 14,
  .irelop .w32 (.le .u), .brIf 0, .localGet 2, .localSet 4, .br 7]

/-- The first extension byte: done unless it is 255. -/
def b10 : List Instr := [.localGet 15, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .localTee 17,
  .iconst .w32 255, .irelop .w32 .eq, .brIf 0, .localGet 2, .localSet 4, .br 1]

/-- The extension block: the first byte, then the loop from `acc = 255`. -/
noncomputable def ext3 : List Instr :=
  [.block .empty b10, .iconst .w32 255, .localSet 17, extLoop]

/-- After the extension block: `len = acc + 15` and its two overflow guards. -/
def tailA : List Instr := [.localGet 17, .iconst .w32 15, .ibinop .w32 .add, .localTee 2,
  .localGet 3, .iconst .w32 4294967295, .ibinop .w32 .xor, .irelop .w32 (.gt .u), .brIf 6,
  .localGet 2, .localGet 4, .iconst .w32 4294967295, .ibinop .w32 .xor, .irelop .w32 (.gt .u),
  .brIf 6]

theorem body8_drop1 : body8.drop 1 = .block .empty g1 :: .block .empty g2 :: .block .empty ext3 ::
    body8.drop 4 := by kernel_rfl
theorem body8_drop4 : body8.drop 4 = tailA := by kernel_rfl
theorem body2_drop1 :
    body2.drop 1 = [.localGet 2, .iconst .w32 1, .ibinop .w32 .add, .localSet 4] := by kernel_rfl

theorem psum_zero (acc : Nat) (b : Nat → UInt8) : psum acc b 0 = acc + (b 0).toNat := by
  simp [psum]

/-- One period of the sum: the first byte, then the bytes from `p + 1`. -/
theorem psum_shift (acc : Nat) (mem : MemInst) (p i : Nat) :
    psum acc (fun j => mem.byte (p + j)) (i + 1) =
      psum (acc + (mem.byte p).toNat) (fun j => mem.byte (p + 1 + j)) i := by
  unfold psum
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def, Nat.add_zero]
  have hf : (fun x => (mem.byte (p + Nat.succ x)).toNat) = fun j => (mem.byte (p + 1 + j)).toNat :=
    funext fun j => by rw [show p + Nat.succ j = p + 1 + j by omega]
  rw [hf]
  omega

theorem psum_first {mem : MemInst} {p acc : Nat} :
    psum acc (fun j => mem.byte (p + j)) 0 = acc + (mem.byte p).toNat := by
  rw [psum_zero, Nat.add_zero]

theorem shift_ff {mem : MemInst} {p k : Nat} (hff : ∀ j < k + 1, mem.byte (p + j) = 255) :
    ∀ j < k, mem.byte (p + 1 + j) = 255 :=
  fun j hj => by rw [show p + 1 + j = p + (j + 1) by omega]; exact hff (j + 1) (by omega)

theorem byte255 {mem : MemInst} {p k : Nat} (hff : ∀ j < k + 1, mem.byte (p + j) = 255) :
    (mem.byte p).toNat = 255 := by
  have := hff 0 (by omega); rw [Nat.add_zero] at this; rw [this]; rfl

/-- `ExtL1`'s normal exit after `k + 1` reads: `extM` returns the sum and the position after. -/
theorem extM_normal {mem : MemInst} {lim : Nat} : ∀ (k p acc fuel : Nat), k + 1 ≤ fuel →
    (∀ j < k, mem.byte (p + j) = 255) → mem.byte (p + k) ≠ 255 → p + k + 1 ≤ lim →
    (∀ i ≤ k, psum acc (fun j => mem.byte (p + j)) i < 2 ^ 31) →
    extM mem lim fuel p acc = some (psum acc (fun j => mem.byte (p + j)) k, p + k + 1)
  | _, _, _, 0, hf, _, _, _, _ => absurd hf (by omega)
  | 0, p, acc, fuel + 1, _, _, hk, hl, hs => by
    have h0 := hs 0 (Nat.le_refl _)
    rw [psum_first] at h0 ⊢
    rw [Nat.add_zero] at hk
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega), ite_eq_left h0]
    rw [ite_eq_right fun h => hk (UInt8.toNat_inj.mp (by rw [h]; rfl))]
  | k + 1, p, acc, fuel + 1, hf, hff, hk, hl, hs => by
    have h0 := hs 0 (Nat.zero_le _)
    rw [psum_first] at h0
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega), ite_eq_left h0,
      ite_eq_left (byte255 hff)]
    have ih := extM_normal (lim := lim) k (p + 1) (acc + (mem.byte p).toNat) fuel (by omega)
      (shift_ff hff)
      (by rw [show p + 1 + k = p + (k + 1) by omega]; exact hk) (by omega)
      (fun i hi => by rw [← psum_shift]; exact hs (i + 1) (by omega))
    rw [ih, psum_shift, show p + 1 + k + 1 = p + (k + 1) + 1 by omega]

/-- `ExtL1`'s bound exit: `extM` fails (at any fuel). -/
theorem extM_bound_exit {mem : MemInst} {lim : Nat} : ∀ (k p acc fuel : Nat),
    (∀ j < k, mem.byte (p + j) = 255) → lim < p + k + 1 →
    (∀ i, i + 1 ≤ k → psum acc (fun j => mem.byte (p + j)) i < 2 ^ 31) →
    extM mem lim fuel p acc = none
  | _, _, _, 0, _, _, _ => rfl
  | 0, p, acc, fuel + 1, _, hl, _ => by
    simp only [extM, ite_eq_right (show ¬ p + 1 ≤ lim by omega)]
  | k + 1, p, acc, fuel + 1, hff, hl, hs => by
    by_cases hp : p + 1 ≤ lim
    · have h0 := hs 0 (by omega)
      rw [psum_first] at h0
      simp only [extM, ite_eq_left hp, ite_eq_left h0, ite_eq_left (byte255 hff)]
      exact extM_bound_exit k (p + 1) _ fuel (shift_ff hff) (by omega)
        (fun i hi => by rw [← psum_shift]; exact hs (i + 1) (by omega))
    · simp only [extM, ite_eq_right hp]

/-- `ExtL1`'s overflow exit: `extM` fails (at any fuel). -/
theorem extM_overflow_exit {mem : MemInst} {lim : Nat} : ∀ (k p acc fuel : Nat),
    (∀ j < k, mem.byte (p + j) = 255) → p + k + 1 ≤ lim →
    (∀ i, i + 1 ≤ k → psum acc (fun j => mem.byte (p + j)) i < 2 ^ 31) →
    2 ^ 31 ≤ psum acc (fun j => mem.byte (p + j)) k → extM mem lim fuel p acc = none
  | _, _, _, 0, _, _, _, _ => rfl
  | 0, p, acc, fuel + 1, _, hl, _, ho => by
    rw [psum_first] at ho
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega),
      ite_eq_right (show ¬ acc + (mem.byte p).toNat < 2 ^ 31 by omega)]
  | k + 1, p, acc, fuel + 1, hff, hl, hs, ho => by
    have h0 := hs 0 (by omega)
    rw [psum_first] at h0
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega), ite_eq_left h0,
      ite_eq_left (byte255 hff)]
    exact extM_overflow_exit k (p + 1) _ fuel (shift_ff hff) (by omega)
      (fun i hi => by rw [← psum_shift]; exact hs (i + 1) (by omega))
      (by rw [← psum_shift]; exact ho)

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

theorem igtU_not {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a + b < 2 ^ 32) :
    igtU (BitVec.ofNat 32 a) (~~~BitVec.ofNat 32 b) = 0 := by
  simp only [igtU, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, gt_iff_lt]
  rw [show decide (2 ^ 32 - 1 - b < a) = false by simp; omega]; rfl

/-- After the extension bytes (local 17 = `acc`, 4 = `q`): `len = acc + 15`, both overflow
guards pass, block `@8` ends at X2. -/
theorem tail_X2 {H : HostSem} {F : Context} {st : Store} {inst : ModuleInst} {ls : List Val}
    {R W : Nat → Nat → Prop} {src dst n cap op q t acc : Nat}
    (hcl : ConstLocals ls src dst n cap) (h3 : ls[3]? = some (vI op)) (h4 : ls[4]? = some (vI q))
    (h16 : ls[16]? = some (vI t)) (h17 : ls[17]? = some (vI acc))
    (hb1 : acc + 15 + op < 2 ^ 32) (hb2 : acc + 15 + q < 2 ^ 32) :
    Until H (Within R W) (AtX2 F st inst src dst n cap op q (15 + acc) t)
      ((ctx8 (ctx2 F)).fill ⟨st, ⟨ls, inst⟩, (body8.drop 4).map .plain⟩) := by
  have hln := hcl.1
  have hg1 := igtU_not (a := acc + 15) (b := op) (by omega) (by omega) hb1
  have hg2 := igtU_not (a := acc + 15) (b := q) (by omega) (by omega) hb2
  rw [body8_drop4]
  repeat (wasm_cstepu [tailA, h3, h4, h17, iadd_ofNat, ixor, xor_neg1, hg1, hg2, zero_eq,
            show 2 < ls.length by omega,
            getElem?_set_of_ne (show (2 : Nat) ≠ 3 by decide),
            getElem?_set_of_ne (show (2 : Nat) ≠ 4 by decide),
            List.getElem?_set_self (show 2 < ls.length by omega)]
          · wasm_within [tailA])
  rw [show ctx8 (ctx2 F) = .label 0 [] ((body7.drop 1).map .plain) (ctx7 (ctx2 F)) from rfl,
    Context.fill.eq_2]
  wasm_cstepu []
  · wasm_within []
  refine Until.done ⟨_, hcl.set (by omega) _, ?_, ?_, ?_, ?_, rfl⟩
  · rw [getElem?_set_of_ne (by decide)]; exact h3
  · rw [getElem?_set_of_ne (by decide)]; exact h4
  · rw [List.getElem?_set_self (by omega), Nat.add_comm]
  · rw [getElem?_set_of_ne (by decide)]; exact h16

/-- The error tail after block `@3` (local 2 = `w`): `local 4 ← w + 1`, block `@2` ends at the
epilogue. -/
theorem tail_err {H : HostSem} {F : Context} {st : Store} {inst : ModuleInst} {ls : List Val}
    {R W : Nat → Nat → Prop} {src dst n cap w : Nat}
    (hcl : ConstLocals ls src dst n cap) (h2 : ls[2]? = some (vI w))
    (hlo : src ≤ w + 1) (hhi : w + 1 ≤ src + n + 1) :
    Until H (Within R W) (Err F st inst src dst n cap)
      ((ctx2 F).fill ⟨st, ⟨ls, inst⟩, (body2.drop 1).map .plain⟩) := by
  have hln := hcl.1
  rw [body2_drop1]
  repeat (wasm_cstepu [h2, iadd_ofNat, show 4 < ls.length by omega]
          · wasm_within [])
  rw [show ctx2 F = .label 0 [] ((body1.drop 54).map .plain) (ctx1 F) from rfl,
    Context.fill.eq_2]
  wasm_cstepu []
  · wasm_within []
  exact Until.done ⟨w + 1, hlo, hhi, _, hcl.set (by omega) _,
    List.getElem?_set_self (by omega), rfl⟩

theorem iltU_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    iltU (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (a < b)) := by
  simp only [iltU, ofNat_toNat ha, ofNat_toNat hb]

theorem ileU_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ileU (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (a ≤ b)) := by
  simp only [ileU, ofNat_toNat ha, ofNat_toNat hb]

theorem bool_dec_true {p : Prop} [Decidable p] (h : p) : bool (decide p) = 1 := by
  simp [h, bool_true]

theorem bool_dec_false {p : Prop} [Decidable p] (h : ¬ p) : bool (decide p) = 0 := by
  simp [h, bool_false]

/-- The frame after a loop exit, as locals of `inst`. -/
theorem frame_eta {f : Frame} {inst : ModuleInst} (h : f.inst = inst) : f = ⟨f.locals, inst⟩ := by
  cases f; cases h; rfl

/-- `Locals` keeps the constant locals (none of them is 2, 4, 15, 17). -/
theorem Locals.const {ls : List Val} {inst : ModuleInst} {f' : Frame} {l2 l4 : Nat}
    {l15 l17 : Option Nat} {src dst n cap : Nat} (hl : Locals ls inst f' l2 l4 l15 l17)
    (hc : ConstLocals ls src dst n cap) : ConstLocals f'.locals src dst n cap := by
  obtain ⟨-, hlen, hoth, -⟩ := hl
  obtain ⟨hln, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hc
  refine ⟨hlen.trans hln, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hoth _ (by decide) (by decide) (by decide) (by decide)] <;> assumption

/-- Each byte adds at most 255. -/
theorem psum_le (acc : Nat) (b : Nat → UInt8) : ∀ k, psum acc b k ≤ acc + 255 * (k + 1)
  | 0 => by have := (b 0).toNat_lt; rw [psum_zero]; omega
  | k + 1 => by
    have ih := psum_le acc b k
    have hs : psum acc b (k + 1) = psum acc b k + (b (k + 1)).toNat := by
      simp only [psum, List.range_succ, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil]
      omega
    have := (b (k + 1)).toNat_lt
    omega

/-- `SegA` from the loop lemma `ExtL1B`. -/
theorem segA_of (hL : ExtL1B) : SegA := by
  intro H F st inst ls ma mem src dst n cap op ip t hcl h3 h4 h15 h2 h16 hm hmem hs hd hsn hdc
    hsz hip1 hip2 hop
  have hcl' := hcl
  obtain ⟨hln, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hcl'
  have hlt := iltU_ofNat (a := ip + 1) (b := src + n - 15) (by omega) (by omega)
  rw [body8_drop1]
  by_cases hb1 : ip + 1 < src + n - 15
  swap
  · -- no room for the extension bytes: `local 4 ← ip + 1`, the epilogue
    repeat (wasm_cstepu [g1, h15, h14, hlt, bool_dec_false hb1, zero_eq,
              show 4 < ls.length by omega]
            · wasm_within [g1])
    simp only [ctx8, ctx2, Context.fill]
    wasm_cstepu []
    · wasm_within []
    have hnone : extM mem (src + n - 15) n (ip + 1) 0 = none := by
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [hn']; simp only [extM, ite_eq_right (show ¬ ip + 1 + 1 ≤ src + (n' + 1) - 15 by omega)]
    exact Until.done (Or.inr ⟨hnone, ip + 1, by omega, by omega, _, hcl.set (by omega) _,
      List.getElem?_set_self (by omega), rfl⟩)
  have hle := ileU_ofNat (a := ip + 2) (b := src + n - 15) (by omega) (by omega)
  have hsrc1 : (BitVec.ofNat 32 (ip + 1)).toNat = ip + 1 := ofNat_toNat (by omega)
  have hblt : decide (mem.size < ip + 1 + 1) = false := by simp; omega
  have heq := ieq_ofNat (a := (mem.byte (ip + 1)).toNat) (b := 255)
    (by have := (mem.byte (ip + 1)).toNat_lt; omega) (by omega)
  -- the bound checks, the first extension byte read
  repeat (wasm_cstepu [g1, g2, ext3, b10, h4, h15, h14, hlt, hle, iadd_ofNat,
            bool_dec_true hb1, bool_dec_true (show ip + 2 ≤ src + n - 15 by omega), one_ne,
            getElem?_set_of_ne (show (2 : Nat) ≠ 14 by decide),
            getElem?_set_of_ne (show (2 : Nat) ≠ 15 by decide), show 2 < ls.length by omega]
          · wasm_within [g1, g2, ext3, b10])
  wasm_cstepu [hm, hmem, hsrc1, hblt, read_one, PackSize.bits, packedVal, Nat.add_zero]
  · wasm_within [hm, hmem, hsrc1, hblt, PackSize.bits, Nat.add_zero]
    exact ⟨fun x h₁ h₂ => ⟨trivial, Or.inl ⟨rfl, by omega, by omega⟩⟩, by simp⟩
  have hb0 := (mem.byte (ip + 1)).toNat_lt
  have hlen2 : (ls.set 2 (vI (ip + 2))).length = 19 := by simp [hln]
  by_cases h255 : (mem.byte (ip + 1)).toNat = 255
  swap
  · -- the first byte ends the extension: `acc = b0`, `q = ip + 2`
    have hne : ((mem.byte (ip + 1)).toNat == 255) = false := by simp [h255]
    repeat (wasm_cstepu [heq, hne, bool_false, zero_eq, show 17 < 19 by omega, hlen2,
              getElem?_set_of_ne (show (17 : Nat) ≠ 2 by decide),
              List.getElem?_set_self (show 2 < ls.length by omega),
              show 4 < ((ls.set 2 (vI (ip + 2))).set 17
                (.i32 (BitVec.ofNat 32 (mem.byte (ip + 1)).toNat))).length by simp [hln]]
            · wasm_within [])
    have hsome :
        extM mem (src + n - 15) n (ip + 1) 0 = some ((mem.byte (ip + 1)).toNat, ip + 2) := by
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [hn']
      simp only [extM, ite_eq_left (show ip + 1 + 1 ≤ src + (n' + 1) - 15 by omega),
        Nat.zero_add, ite_eq_left (show (mem.byte (ip + 1)).toNat < 2 ^ 31 by omega),
        ite_eq_right h255]
    refine Until.mono (tail_X2 (acc := (mem.byte (ip + 1)).toNat) (q := ip + 2) (op := op) (t := t)
      ((((hcl.set (by omega) _).set (by omega) _).set (by omega) _)) ?_ ?_ ?_ ?_ (by omega)
      (by omega)) (fun _ h => h) fun c hc => Or.inl ⟨_, _, hsome, hc⟩
    · rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
        getElem?_set_of_ne (by decide)]; exact h3
    · rw [List.getElem?_set_self (by simp [hln])]
    · rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
        getElem?_set_of_ne (by decide)]; exact h16
    · rw [getElem?_set_of_ne (by decide), List.getElem?_set_self (by simp [hln])]
  -- the first byte is 255: `acc = 255`, the loop from `ip + 2`
  have hyes : ((mem.byte (ip + 1)).toNat == 255) = true := by simp [h255]
  repeat (wasm_cstepu [heq, hyes, bool_true, one_ne, List.length_set, hln]
          · wasm_within [])
  have hls := (((hcl.set (i := 2) (by omega) (vI (ip + 2))).set (i := 17) (by omega)
    (.i32 (BitVec.ofNat 32 (mem.byte (ip + 1)).toNat))).set (i := 17) (by omega) (vI 255))
  change Until H _ _ ((ctx9 (ctx2 F)).fill ⟨st, ⟨((ls.set 2 (vI (ip + 2))).set 17
    (.i32 (BitVec.ofNat 32 (mem.byte (ip + 1)).toNat))).set 17 (vI 255), inst⟩, [.plain extLoop]⟩)
  have hloop := hL H (ctx2 F) st inst (((ls.set 2 (vI (ip + 2))).set 17
    (.i32 (BitVec.ofNat 32 (mem.byte (ip + 1)).toNat))).set 17 (vI 255)) ma mem (ip + 2)
    (src + n - 15) 255
    (by rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
      List.getElem?_set_self (by omega)])
    (by rw [getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
      getElem?_set_of_ne (by decide)]; exact h14)
    (by rw [List.getElem?_set_self (by simp [hln])]) hm hmem (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hstep : extM mem (src + n - 15) n (ip + 1) 0 = extM mem (src + n - 15) n' (ip + 2) 255 := by
    have h : ∀ L fuel, ip + 2 ≤ L →
        extM mem L (fuel + 1) (ip + 1) 0 = extM mem L fuel (ip + 2) 255 := by
      intro L fuel hl
      simp only [extM, ite_eq_left (show ip + 1 + 1 ≤ L by omega), Nat.zero_add,
        ite_eq_left (show (mem.byte (ip + 1)).toNat < 2 ^ 31 by omega), ite_eq_left h255]
      rw [h255]
    have h' := h (src + n - 15) n' (by omega)
    rw [← hn'] at h'
    exact h'
  refine Until.trans (Until.mono hloop (fun c hc => Within.mono hc
    (fun m a ha => ⟨ha.1, Or.inl ⟨ha.1, by omega, by omega⟩⟩) fun _ _ h => h.elim)
    fun _ h => h) ?_
  rintro c (⟨k, f', hff, hk, hkl, hsums, hlc, rfl⟩ | ⟨k, f', hff, hkl, hsums, hlc, rfl⟩ |
    ⟨k, f', hff, hkl, hsums, hov, hlc, rfl⟩)
  · -- normal exit after k + 1 more bytes
    rw [frame_eta hlc.1]
    have hcf := Locals.const hlc hls
    obtain ⟨-, -, hoth, hl2, hl4, -, hl17⟩ := hlc
    have hsome := extM_normal (lim := src + n - 15) k (ip + 2) 255 n' (by omega) hff hk hkl hsums
    have hpl := psum_le 255 (fun j => mem.byte (ip + 2 + j)) k
    refine Until.mono (tail_X2 (acc := psum 255 (fun j => mem.byte (ip + 2 + j)) k)
      (q := ip + 2 + k + 1) (op := op) (t := t) hcf ?_ hl4 ?_ ?_ (by omega)
      (by omega)) (fun _ h => h) fun c hc => Or.inl ⟨_, _, by rw [hstep, hsome], hc⟩
    · rw [hoth 3 (by decide) (by decide) (by decide) (by decide), getElem?_set_of_ne (by decide),
        getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide)]; exact h3
    · rw [hoth 16 (by decide) (by decide) (by decide) (by decide),
        getElem?_set_of_ne (by decide), getElem?_set_of_ne (by decide),
        getElem?_set_of_ne (by decide)]; exact h16
    · rw [hl17]; rfl
  · -- the bound check fails at the limit
    rw [frame_eta hlc.1]
    have hcf := Locals.const hlc hls
    obtain ⟨-, -, -, hl2, -⟩ := hlc
    refine Until.mono (tail_err (w := ip + 2 + k) hcf hl2 (by omega) (by omega))
      (fun _ h => h) fun c hc => Or.inr ⟨?_, hc⟩
    rw [hstep]
    exact extM_bound_exit k (ip + 2) 255 n' hff (by omega) hsums
  · -- the sum overflows
    rw [frame_eta hlc.1]
    have hcf := Locals.const hlc hls
    obtain ⟨-, -, -, hl2, -⟩ := hlc
    refine Until.mono (tail_err (w := ip + 2 + k) hcf hl2 (by omega) (by omega))
      (fun _ h => h) fun c hc => Or.inr ⟨?_, hc⟩
    rw [hstep]
    exact extM_overflow_exit k (ip + 2) 255 n' hff hkl hsums hov

end Subjects.Lz4C.Cut
