import FVATest.Subjects.EdgerCpm.BodyHeap
import FVATest.Subjects.EdgerCpm.BodyCode
import FVATest.Subjects.EdgerCpm.BodyCleanup

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

noncomputable def firstAlloc (x : Input) (l : Layout) (inst : ModuleInst) (a12 : Nat) :
    List AInstr :=
  [.frame 0 (prefixFrame x l inst) [.label 0 []
    (vals [.i32 1, .i32 4] ++ [.invoke a12] ++ (Lifted.func86.body.drop 13).map .plain)]]

theorem entry_firstAlloc (x : Input) (l : Layout) (s : Store) (inst : ModuleInst)
    (a160 a12 : Nat) (nth : BitVec 32) (H : HostSem) (Q : Outcome → Prop)
    (hf : s.funcs[a160]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], []⟩ inst Lifted.func86))
    (hi : inst.funcs[12]? = some a12) (hm : inst.mems[0]? = some 0)
    (hd : Data s x l) (hy : l.y + 16 ≤ 2 ^ 32)
    (hk : Must H Q ⟨s, ⟨[], {}⟩, firstAlloc x l inst a12⟩) :
    Must H Q (invokeConfig s a160
      [.i32 (.ofNat 32 l.y), .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c), .i32 nth]) := by
  obtain ⟨mem, hmem, hbound, -⟩ := hd.1
  have hb : l.y + 16 ≤ mem.size := by simpa [le32, Nat.add_assoc] using hbound
  have hn := read32 hmem (holds_left hd.1)
  have hcol : Holds s (l.y + 12) (le32 (.ofNat 32 x.m)) := by
    simpa [le32, Nat.add_assoc] using holds_right hd.1
  have hcolread := read32 hmem hcol
  have hp : (BitVec.ofNat 32 l.y).toNat = l.y := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : l.y < 2 ^ 32)]
  have hb12 : ¬ mem.size < l.y + 12 + 4 := by omega
  have hb8 : ¬ mem.size < l.y + 8 + 4 := by omega
  unfold invokeConfig
  iterate 10 wasm_step1 [hf, hi, hm, hmem, hp, hb12, hb8, hn, hcolread,
    BitVec.ofNat_toNat, Lifted.func86]
  exact hk

noncomputable def afterFirst (x : Input) (l : Layout) (inst : ModuleInst) (t : BitVec 32) :
    List AInstr :=
  [.frame 0 (prefixFrame x l inst) [.label 0 []
    ((Val.i32 t).instr :: (Lifted.func86.body.drop 13).map .plain)]]

theorem firstAlloc_returns (x : Input) (l : Layout) (s : Store) (inst : ModuleInst)
    (a12 alloc free : Nat) (H : HostSem) (Q : Outcome → Prop) (heap : Nat → Prop)
    (blocks : Store → List (Nat × Nat)) (ready : Nat → Store → Prop)
    (hD : Domain x) (hA : Allocator H alloc free heap (8 * x.m) blocks ready)
    (hr : ready 2 s)
    (hf : s.funcs[a12]? = some (.host ⟨[.num .i32, .num .i32], [.num .i32]⟩ alloc))
    (hk : ∀ s' t, Allocated heap blocks ready 1 4 s s' t →
      Must H Q ⟨s', ⟨[], {}⟩, afterFirst x l inst t⟩) :
    Must H Q ⟨s, ⟨[], {}⟩, firstAlloc x l inst a12⟩ := by
  have hc : (1 : BitVec 32).toNat * (4 : BitVec 32).toNat ≤ 8 * x.m := by
    have := hD.2.1
    change 4 ≤ 8 * x.m
    omega
  apply must_alloc hA hr (n := 1) (sz := 4) (by decide) hc hf
  · simp [firstAlloc, seqFocus, atFocus, HostAt, toVal_instr, toVal_frame, toVal_label,
      toVal_invoke, vals]
  · intro s' t ht
    simpa only [firstAlloc, afterFirst, seqPlug, atPlug, toVal_frame, toVal_label,
      toVal_instr, seqPlug_vals, List.reverse_cons, List.reverse_nil, List.singleton_append,
      List.nil_append, List.cons_append, toVal_invoke, List.drop_succ_cons, List.drop_zero,
      List.map_cons, List.map_nil, List.append_nil, vals] using hk s' t ht

noncomputable def allocationContext (x : Input) (l : Layout) (inst : ModuleInst)
    (t : BitVec 32) (code : List AInstr) : List AInstr :=
  [.frame 0 (tableFrame x l inst t) [.label 0 []
    (.label 0 [outerLoop] [.label 0 [] code] :: (Lifted.func86.body.drop 15).map .plain)]]

noncomputable def secondAlloc (x : Input) (l : Layout) (inst : ModuleInst)
    (t : BitVec 32) (a12 : Nat) : List AInstr :=
  allocationContext x l inst t
    (vals [.i32 t, .i32 (.ofNat 32 x.m), .i32 8] ++ [.invoke a12] ++
      (outerCode.drop 12).map .plain)

theorem afterFirst_secondAlloc (x : Input) (l : Layout) (s : Store) (inst : ModuleInst)
    (t : BitVec 32) (a12 : Nat) (H : HostSem) (Q : Outcome → Prop)
    (hi : inst.funcs[12]? = some a12)
    (hk : Must H Q ⟨s, ⟨[], {}⟩, secondAlloc x l inst t a12⟩) :
    Must H Q ⟨s, ⟨[], {}⟩, afterFirst x l inst t⟩ := by
  have heq : ieq (0 : BitVec 32) (BitVec.ofNat 32 1) = 0 := by decide
  have hsh : ishl (0 : BitVec 32) (BitVec.ofNat 32 2) = 0 := by decide
  have hadd : iadd t (0 : BitVec 32) = t := by simp [iadd_eq]
  unfold afterFirst prefixFrame
  iterate 14 wasm_step1 [hi, Lifted.func86, List.drop_succ_cons, List.drop_zero,
    heq, hsh, hadd]
  exact hk

noncomputable def afterSecond (x : Input) (l : Layout) (inst : ModuleInst)
    (t b : BitVec 32) : List AInstr :=
  allocationContext x l inst t
    (vals [.i32 t, .i32 b] ++ (outerCode.drop 12).map .plain)

theorem secondAlloc_returns (x : Input) (l : Layout) (s : Store) (inst : ModuleInst)
    (t : BitVec 32) (a12 alloc free : Nat) (H : HostSem) (Q : Outcome → Prop)
    (heap : Nat → Prop) (blocks : Store → List (Nat × Nat)) (ready : Nat → Store → Prop)
    (hD : Domain x) (hA : Allocator H alloc free heap (8 * x.m) blocks ready)
    (hr : ready 1 s)
    (hf : s.funcs[a12]? = some (.host ⟨[.num .i32, .num .i32], [.num .i32]⟩ alloc))
    (hk : ∀ s' b, Allocated heap blocks ready 0 (8 * x.m) s s' b →
      Must H Q ⟨s', ⟨[], {}⟩, afterSecond x l inst t b⟩) :
    Must H Q ⟨s, ⟨[], {}⟩, secondAlloc x l inst t a12⟩ := by
  have hm : (BitVec.ofNat 32 x.m).toNat = x.m := by
    have := hD.2.2
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.m < 2 ^ 32)]
  have hz : 0 < (BitVec.ofNat 32 x.m).toNat * (8 : BitVec 32).toNat := by
    have := hD.2.1
    simp only [hm, show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  have hc : (BitVec.ofNat 32 x.m).toNat * (8 : BitVec 32).toNat = 8 * x.m := by
    simp only [hm, show (8 : BitVec 32).toNat = 8 from rfl, Nat.mul_comm]
  apply must_alloc hA hr hz (le_of_eq hc) hf
  · simp [secondAlloc, allocationContext, seqFocus, atFocus, HostAt, toVal_instr,
      toVal_frame, toVal_label, toVal_invoke, vals]
  · intro s' b hb
    rw [hc] at hb
    simpa only [secondAlloc, afterSecond, allocationContext, seqPlug, atPlug, toVal_frame,
      toVal_label, toVal_instr, seqPlug_vals, List.reverse_cons, List.reverse_nil,
      List.singleton_append, List.nil_append, List.cons_append, toVal_invoke,
      List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil, List.append_nil,
      vals] using hk s' b hb

theorem afterSecond_stored (x : Input) (l : Layout) (s : Store) (inst : ModuleInst)
    (mem : MemInst) (t b : BitVec 32) (H : HostSem) (Q : Outcome → Prop)
    (hm : inst.mems[0]? = some 0) (hmem : s.mems[0]? = some mem)
    (hb : t.toNat + 4 ≤ mem.size)
    (hk : Must H Q ⟨{ s with mems := s.mems.set 0 (mem.write t.toNat 4 b.toNat) },
      ⟨[], {}⟩, allocatedHead x l inst t⟩) :
    Must H Q ⟨s, ⟨[], {}⟩, afterSecond x l inst t b⟩ := by
  have hbound : ¬ mem.size < t.toNat + 4 := by omega
  have hadd : iadd (0 : BitVec 32) (BitVec.ofNat 32 1) = 1 := by decide
  unfold afterSecond allocationContext tableFrame prefixFrame
  iterate 5 wasm_step1 [hm, hmem, hbound, Lifted.func86, outerCode, outerLoop, blockCode,
    loopCode,
    List.getD, List.drop_succ_cons, List.drop_zero, Val.numBits, Nat.add_zero, hadd]
  exact hk

theorem allocation_prefix (x : Input) (l : Layout) (s : Store) (inst : ModuleInst)
    (alloc free : Nat) (H : HostSem) (Q : Outcome → Prop) (nth : BitVec 32)
    (heap : Nat → Prop) (blocks : Store → List (Nat × Nat)) (ready : Nat → Store → Prop)
    (hD : Domain x) (hd : Data s x l) (hlink : Linked s inst alloc free)
    (hA : Allocator H alloc free heap (8 * x.m) blocks ready) (hr : ready 2 s)
    (hsep : ∀ a, l.kept x a ∨ l.counts x a → ¬ heap a ∨ InBlocks (blocks s) a)
    (hy : l.y + 16 ≤ 2 ^ 32)
    (hk : ∀ s' t b, Linked s' inst alloc free →
      Scratch heap blocks ready (blocks s) x.m t b s' → Data s' x l →
      Holds s' t.toNat (le32 b) → SameOn s s' (fun a => l.kept x a ∨ l.counts x a) →
      Must H Q ⟨s', ⟨[], {}⟩, allocatedHead x l inst t⟩) :
    CallMust H s inst "calc_cpm_raw"
      [.i32 (.ofNat 32 l.y), .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c), .i32 nth] Q := by
  obtain ⟨hm, a160, a207, a12, a13, hi207, hi12, hi13, hex, f160, f207, f12, f13⟩ := hlink
  have hlink : Linked s inst alloc free :=
    ⟨hm, a160, a207, a12, a13, hi207, hi12, hi13, hex, f160, f207, f12, f13⟩
  rw [cpm_type] at f160
  refine ⟨a160, hex, ⟨_, f160, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  apply entry_firstAlloc x l s inst a160 a12 nth H Q f160 hi12 hm hd hy
  apply firstAlloc_returns x l s inst a12 alloc free H Q heap blocks ready hD hA hr f12
  intro s₁ t ht
  apply afterFirst_secondAlloc x l s₁ inst t a12 H Q hi12
  have f12' : s₁.funcs[a12]? = some (.host ⟨[.num .i32, .num .i32], [.num .i32]⟩ alloc) := by
    obtain ⟨fi, hfi, rfl⟩ := ht.ext.1 a12 _ f12
    exact hfi
  apply secondAlloc_returns x l s₁ inst t a12 alloc free H Q heap blocks ready hD hA
    ht.next f12'
  intro s₂ b hb
  have hs := scratch_allocated hD.2.1 ht hb
  obtain ⟨mem, hmem, hts, hbs⟩ := hs.room
  apply afterSecond_stored x l s₂ inst mem t b H Q hm hmem hts
  have same₁ := same_mono ht.same hsep
  have sep₁ : ∀ a, l.kept x a ∨ l.counts x a → ¬ heap a ∨ InBlocks (blocks s₁) a := by
    intro a ha
    exact (hsep a ha).imp_right (inBlocks_mono ht.old)
  have same₂ := same_trans same₁ (same_mono hb.same sep₁)
  have same₃ : SameOn s₂ (put s₂ mem t.toNat 4 b.toNat)
      (fun a => l.kept x a ∨ l.counts x a) := by
    apply same_put hmem
    intro a ha hz
    obtain ⟨hheap, hfresh⟩ := ht.fresh a hz.1 hz.2
    exact (hsep a ha).elim (fun hn => hn hheap) hfresh
  have hs' := scratch_put hA hs hmem (p := t.toNat) (k := 4) (v := b.toNat) (by
    intro a ha hz
    right
    exact ⟨(t.toNat, 4), hs.table, ha, hz⟩)
  exact hk (put s₂ mem t.toNat 4 b.toNat) t b
    (linked_put (linked_extends (linked_extends hlink ht.ext) hb.ext)) hs'
    (data_same (same_trans same₂ same₃) hd) (holds_put32 hmem hts)
    (same_trans same₂ same₃)

end Subjects.EdgerCpm.Body

namespace Subjects.EdgerCpm

open FVA.Wasm FVA.Wasm.Exec

theorem body_returns (x : Input) (H : HostSem) (l : Layout) (s : Store) (inst : ModuleInst)
    (alloc free : Nat) (heap : Nat → Prop) (blocks : Store → List (Nat × Nat))
    (ready : Nat → Store → Prop) (hD : Domain x) (hdata : Data s x l)
    (hlink : Linked s inst alloc free) (hA : Allocator H alloc free heap (8 * x.m) blocks ready)
    (hr : ready 2 s) (hsep : ∀ a, l.kept x a ∨ l.counts x a → ¬ heap a ∨ InBlocks (blocks s) a)
    (hkc : ∀ a, l.kept x a → ¬ l.counts x a) (hy : l.y + 16 ≤ 2 ^ 32) (hl : l.lib + 32 ≤ 2 ^ 32)
    (hd : l.d + 8 * x.m ≤ 2 ^ 32) (hc : l.c + 8 * x.n * x.m ≤ 2 ^ 32) (nth : BitVec 32) :
    CallReturns H s inst "calc_cpm_raw"
      [.i32 (.ofNat 32 l.y), .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c), .i32 nth]
      fun s' vs => vs = [] ∧
        (∀ i < x.n, ∀ j < x.m, ∃ out, Holds s' (l.cell x i j) (le64 out) ∧
          CpmElem (x.count i j) (x.libSize j) out) ∧
        SameOn s s' (l.kept x) := by
  let W : Body.World :=
    { x := x, l := l, initial := s, inst := inst, H := H, alloc := alloc, free := free,
      heap := heap, blocks := blocks, ready := ready, domain := hD, allocator := hA,
      callerSafe := hsep, separated := hkc, yBound := hy, libBound := hl, dataBound := hd,
      countsBound := hc }
  change CallMust H s inst "calc_cpm_raw" _ (Body.post W)
  apply Body.allocation_prefix x l s inst alloc free H (Body.post W) nth heap blocks ready
    hD hdata hlink hA hr hsep hy
  intro s' t b hlinked hscratch hdata' htable hsame
  have hstate : Body.LoopState W t b 0 s' :=
    ⟨hlinked, hscratch, Body.data_lib hdata', htable, Body.cells_initial hdata',
      Body.same_mono hsame (fun a ha => Or.inl ha)⟩
  apply Body.row_start H (Body.post W) s' inst x l t hD.1 hD.2.1 W.n31 W.m31
  exact Body.row_loop W t b Body.bodyContext ((Body.processCode.drop 17).map .plain) (Body.post W)
    (fun sf j p last hs => Body.cleanup_returns W t b sf j p last hs)
    x.n 0 s' 1 0 0 (by simp [W]) hstate

end Subjects.EdgerCpm
