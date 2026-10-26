import FVATest.Subjects.EdgerCpm.BodyContext
import FVATest.Subjects.EdgerCpm.BodyHeap
import FVATest.Subjects.EdgerCpm.BodyFrame
import FVATest.Subjects.EdgerCpm.BodyCode

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

noncomputable def rowOuter : List Instr := blockCode (Lifted.func133.body.getD 7 .nop)
noncomputable def rowVector : List Instr := blockCode (rowOuter.getD 0 .nop)
noncomputable def copyLoop : Instr := rowVector.getD 10 .nop

noncomputable def copyHead (l : Layout) (inst : ModuleInst) (m j : Nat) (b prev : BitVec 32)
    (_caller : Frame) (tail : List AInstr) : List AInstr :=
  .frame 0 ⟨[.i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 m), .i32 b,
    .i32 (.ofNat 32 j), .i32 prev, .i32 0], inst⟩
    [.label 0 [] [.label 0 []
      (.label 0 [] ((copyLoop :: rowVector.drop 11).map .plain) ::
        (rowOuter.drop 1).map .plain)]] :: tail

theorem copy_step (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (caller : Frame) (tail : List AInstr) (l : Layout)
    (m j : Nat) (b prev : BitVec 32) (mem : MemInst) (v : BitVec 64)
    (hj : j < m) (hm32 : m < 2 ^ 32) (hl32 : l.lib < 2 ^ 32)
    (hd32 : l.d + 8 * j < 2 ^ 32) (hb32 : b.toNat + 8 * j < 2 ^ 32)
    (hm : inst.mems[0]? = some 0) (hmem : s.mems[0]? = some mem)
    (hl : l.lib + 4 ≤ mem.size) (hd : l.d + 8 * j + 8 ≤ mem.size)
    (hb : b.toNat + 8 * j + 8 ≤ mem.size)
    (hptr : mem.read l.lib 4 = (BitVec.ofNat 32 l.d).toNat)
    (hval : mem.read (l.d + 8 * j) 8 = v.toNat)
    (hk : Must H Q (C.fill ⟨put s mem (b.toNat + 8 * j) 8 v.toNat, caller,
      copyHead l inst m (j + 1) b (.ofNat 32 (8 * j)) caller tail⟩)) :
    Must H Q (C.fill ⟨s, caller, copyHead l inst m j b prev caller tail⟩) := by
  have j32 : j < 2 ^ 32 := lt_trans hj hm32
  have hjnat : (BitVec.ofNat 32 j).toNat = j := Nat.mod_eq_of_lt j32
  have hmnat : (BitVec.ofNat 32 m).toNat = m := Nat.mod_eq_of_lt hm32
  have hlnat : (BitVec.ofNat 32 l.lib).toNat = l.lib := Nat.mod_eq_of_lt hl32
  have hdnat : (BitVec.ofNat 32 l.d).toNat = l.d := Nat.mod_eq_of_lt (by omega)
  have h8nat : (BitVec.ofNat 32 (8 * j)).toNat = 8 * j := Nat.mod_eq_of_lt (by omega)
  have heq : ieq (.ofNat 32 m) (.ofNat 32 j) = 0 := by
    simp [ieq, Num.bool, hmnat, hjnat, show m ≠ j by omega]
  have hsh : ishl (.ofNat 32 j) (.ofNat 32 3) = BitVec.ofNat 32 (8 * j) := by
    simp [ishl, hjnat, Nat.mul_comm]
  have hab : iadd b (.ofNat 32 (8 * j)) = BitVec.ofNat 32 (b.toNat + 8 * j) := by
    simp only [iadd, h8nat]
  have had : iadd (.ofNat 32 l.d) (.ofNat 32 (8 * j)) =
      BitVec.ofNat 32 (l.d + 8 * j) := by simp only [iadd, h8nat, hdnat]
  have hbb : (BitVec.ofNat 32 (b.toNat + 8 * j)).toNat = b.toNat + 8 * j :=
    Nat.mod_eq_of_lt hb32
  have hdd : (BitVec.ofNat 32 (l.d + 8 * j)).toNat = l.d + 8 * j :=
    Nat.mod_eq_of_lt hd32
  have hinc : iadd (.ofNat 32 j) (.ofNat 32 1) = BitVec.ofNat 32 (j + 1) := by
    simp only [iadd, hjnat, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
  have hbl : ¬ mem.size < l.lib + 4 := by omega
  have hbd : ¬ mem.size < l.d + 8 * j + 8 := by omega
  have hbb' : ¬ mem.size < b.toNat + 8 * j + 8 := by omega
  unfold copyHead
  iterate 21 wasm_cstep [copyLoop, rowVector, rowOuter, blockCode, Lifted.func133, List.getD,
    List.drop_succ_cons, List.drop_zero, hm, hmem, heq, hsh, hab, had, hinc, hlnat,
    hbb, hdd, hbl, hbd, hbb', hptr, hval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Val.numBits, Nat.add_zero]
  exact hk

theorem copy_exit (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (caller : Frame) (tail : List AInstr) (l : Layout)
    (m : Nat) (b prev : BitVec 32)
    (hk : Must H Q (C.fill ⟨s, caller, tail⟩)) :
    Must H Q (C.fill ⟨s, caller, copyHead l inst m m b prev caller tail⟩) := by
  have heq : ieq (BitVec.ofNat 32 m) (.ofNat 32 m) = 1 := by simp [ieq, Num.bool]
  have hone : (1 : BitVec 32) ≠ 0 := by decide
  unfold copyHead
  iterate 8 wasm_cstep [copyLoop, rowVector, rowOuter, blockCode, Lifted.func133, List.getD,
    List.drop_succ_cons, List.drop_zero, heq, hone]
  exact hk

theorem copy_start (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (caller : Frame) (tail : List AInstr) (l : Layout)
    (m a : Nat) (b row : BitVec 32) (mem : MemInst) (hm0 : 0 < m) (hm31 : m < 2 ^ 31)
    (hl32 : l.lib < 2 ^ 32) (hm : inst.mems[0]? = some 0)
    (hmem : s.mems[0]? = some mem)
    (hf : s.funcs[a]? = some (.wasm ⟨[.num .i32, .num .i32, .num .i32], []⟩
      inst Lifted.func133))
    (hbl : l.lib + 32 ≤ mem.size)
    (hs : mem.read (l.lib + 28) 4 = 0)
    (hn : mem.read (l.lib + 12) 4 = (BitVec.ofNat 32 m).toNat)
    (ht : mem.read (l.lib + 16) 4 = 2)
    (hk : Must H Q (C.fill ⟨s, caller, copyHead l inst m 0 b (.ofNat 32 m) caller tail⟩)) :
    Must H Q (C.fill ⟨s, caller,
      vals [.i32 (.ofNat 32 l.lib), .i32 row, .i32 b] ++ [.invoke a] ++ tail⟩) := by
  have hmnat : (BitVec.ofNat 32 m).toNat = m := Nat.mod_eq_of_lt (by omega)
  have hlnat : (BitVec.ofNat 32 l.lib).toNat = l.lib := Nat.mod_eq_of_lt hl32
  have hgt : igtS (BitVec.ofNat 32 m) (BitVec.ofNat 32 0) = 1 := by
    have hm31' : m < 2147483648 := hm31
    simp [igtS, signed, Num.bool, hmnat, hm31', hm0]
  have hzero : ((0#32 : BitVec 32) = 0) = True := by decide
  have hone : (1 : BitVec 32) ≠ 0 := by decide
  have hb28 : ¬ mem.size < l.lib + 28 + 4 := by omega
  have hb12 : ¬ mem.size < l.lib + 12 + 4 := by omega
  have hb16 : ¬ mem.size < l.lib + 16 + 4 := by omega
  have htwo : (BitVec.ofNat 32 2).toNat = 2 := rfl
  iterate 26 wasm_cstep [hf, hm, hmem, Lifted.func133, hlnat, hb28, hb12, hb16,
    hs, hn, ht, hgt, hzero, hone, htwo, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact hk

theorem holds_size {s : Store} {mem : MemInst} {p : Nat} {bs : List UInt8}
    (hm : s.mems[0]? = some mem) (h : Holds s p bs) : p + bs.length ≤ mem.size := by
  obtain ⟨m, hm', hb, -⟩ := h
  have he : m = mem := Option.some.inj (hm'.symm.trans hm)
  simpa only [he] using hb

def outsideBuffer (b : BitVec 32) (m a : Nat) : Prop := a < b.toNat ∨ b.toNat + 8 * m ≤ a

def Copied (s : Store) (x : Input) (b : BitVec 32) (j : Nat) : Prop :=
  ∀ i < j, Holds s (b.toNat + 8 * i) (le64 (x.libSize i))

theorem copy_loop (C : Context) (H : HostSem) (Q : Outcome → Prop) (inst : ModuleInst)
    (caller : Frame) (tail : List AInstr) (x : Input) (l : Layout) (b : BitVec 32)
    (s₀ : Store) (mem₀ : MemInst) (hm32 : x.m < 2 ^ 32)
    (hl32 : l.lib + 32 ≤ 2 ^ 32) (hd32 : l.d + 8 * x.m ≤ 2 ^ 32)
    (hb32 : b.toNat + 8 * x.m ≤ 2 ^ 32) (hm : inst.mems[0]? = some 0)
    (hmem₀ : s₀.mems[0]? = some mem₀) (hbmem : b.toNat + 8 * x.m ≤ mem₀.size)
    (hlib : LibData s₀ x l)
    (hsep : ∀ a, l.kept x a → outsideBuffer b x.m a)
    (hk : ∀ s, Changed s₀ s (outsideBuffer b x.m) → Copied s x b x.m →
      Must H Q (C.fill ⟨s, caller, tail⟩)) :
    ∀ k j s prev, j + k = x.m → Changed s₀ s (outsideBuffer b x.m) → Copied s x b j →
      Must H Q (C.fill ⟨s, caller, copyHead l inst x.m j b prev caller tail⟩) := by
  intro k
  induction k with
  | zero =>
    intro j s prev hj hchange hcopied
    have hj' : j = x.m := by omega
    subst j
    exact copy_exit C H Q s inst caller tail l x.m b prev (hk s hchange hcopied)
  | succ k ih =>
    intro j s prev hj hchange hcopied
    have hjm : j < x.m := by omega
    obtain ⟨before, mem, hbefore, hmem, hs, hpages, hmax, hbytes⟩ := hchange
    have hchange : Changed s₀ s (outsideBuffer b x.m) :=
      ⟨before, mem, hbefore, hmem, hs, hpages, hmax, hbytes⟩
    have hlib' := lib_same (same_mono (changed_same hchange) hsep) hlib
    have hsize := changed_size hchange hmem₀ hmem
    have hlmem : l.lib + 4 ≤ mem.size := by
      simpa [le32] using holds_size hmem hlib'.1
    have hdmem : l.d + 8 * j + 8 ≤ mem.size := by
      simpa [le64, Binary.leBytes] using holds_size hmem (hlib'.2.2.2 j hjm)
    have hbmem' : b.toNat + 8 * j + 8 ≤ mem.size := by omega
    apply copy_step C H Q s inst caller tail l x.m j b prev mem (x.libSize j)
      hjm hm32 (by omega) (by omega) (by omega) hm hmem hlmem hdmem hbmem'
      (read32 hmem hlib'.1) (read64 hmem (hlib'.2.2.2 j hjm))
    apply ih (j + 1) (put s mem (b.toNat + 8 * j) 8 (x.libSize j).toNat)
      (.ofNat 32 (8 * j)) (by omega)
    · apply changed_put hchange hmem
      intro a ha hz
      unfold outsideBuffer at ha
      omega
    · intro i hi
      by_cases hij : i = j
      · subst i
        exact holds_put64 hmem hbmem'
      · have hij' : i < j := by omega
        apply holds_same (same_put hmem (P := fun a =>
          b.toNat + 8 * i ≤ a ∧ a < b.toNat + 8 * i + 8) (by
            intro a ha hz
            omega)) (hcopied i hij')
        intro a ha hb
        simpa [le64, Binary.leBytes] using And.intro ha hb

theorem get_row_type2 (C : Context) (H : HostSem) (Q : Outcome → Prop) (s : Store)
    (inst : ModuleInst) (caller : Frame) (tail : List AInstr) (x : Input) (l : Layout)
    (a : Nat) (b row : BitVec 32) (mem : MemInst) (hm0 : 0 < x.m) (hm31 : x.m < 2 ^ 31)
    (hl32 : l.lib + 32 ≤ 2 ^ 32) (hd32 : l.d + 8 * x.m ≤ 2 ^ 32)
    (hb32 : b.toNat + 8 * x.m ≤ 2 ^ 32) (hm : inst.mems[0]? = some 0)
    (hmem : s.mems[0]? = some mem) (hbmem : b.toNat + 8 * x.m ≤ mem.size)
    (hf : s.funcs[a]? = some (.wasm ⟨[.num .i32, .num .i32, .num .i32], []⟩
      inst Lifted.func133))
    (hlib : LibData s x l) (hsep : ∀ a, l.kept x a → outsideBuffer b x.m a)
    (hk : ∀ s', Changed s s' (outsideBuffer b x.m) → Copied s' x b x.m →
      Must H Q (C.fill ⟨s', caller, tail⟩)) :
    Must H Q (C.fill ⟨s, caller,
      vals [.i32 (.ofNat 32 l.lib), .i32 row, .i32 b] ++ [.invoke a] ++ tail⟩) := by
  have hb : l.lib + 32 ≤ mem.size := by
    simpa [le32, Nat.add_assoc] using holds_size hmem hlib.2.2.1
  have htag : Holds s (l.lib + 16) (le32 2) := by
    simpa [le32, Nat.add_assoc] using holds_right hlib.2.1
  apply copy_start C H Q s inst caller tail l x.m a b row mem hm0 hm31 (by omega)
    hm hmem hf hb
    (by simpa using read32 hmem hlib.2.2.1) (read32 hmem (holds_left hlib.2.1))
    (by simpa using read32 hmem htag)
  exact copy_loop C H Q inst caller tail x l b s mem (by omega) hl32 hd32 hb32 hm hmem
    hbmem hlib hsep hk x.m 0 s (.ofNat 32 x.m) (by omega) (changed_refl hmem)
    (fun _ hi => by omega)

end Subjects.EdgerCpm.Body
