import FVATest.Subjects.EdgerCpm.Spec
import FVATest.Subjects.EdgerCpm.MemWrite
import FVA.Proof.Lib.Mem
import FVA.Proof.Lib.Arith
import FVA.Proof.Exec.Choice
import Mathlib.Tactic.IntervalCases

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem holds_left {s : Store} {p : Nat} {a b : List UInt8}
    (h : Holds s p (a ++ b)) : Holds s p a := by
  obtain ⟨mem, hm, hb, hv⟩ := h
  refine ⟨mem, hm, by simpa using (Nat.le_trans (by simp) hb), ?_⟩
  intro i hi
  rw [hv i (by simp; omega), List.getElem!_eq_getElem?_getD,
    List.getElem?_append_left hi, ← List.getElem!_eq_getElem?_getD]

theorem holds_right {s : Store} {p : Nat} {a b : List UInt8}
    (h : Holds s p (a ++ b)) : Holds s (p + a.length) b := by
  obtain ⟨mem, hm, hb, hv⟩ := h
  refine ⟨mem, hm, by simpa [List.length_append, Nat.add_assoc] using hb, ?_⟩
  intro i hi
  rw [Nat.add_assoc, hv (a.length + i) (by simp; omega),
    List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

theorem read32 {s : Store} {mem : MemInst} {p : Nat} {v : BitVec 32}
    (hm : s.mems[0]? = some mem) (h : Holds s p (le32 v)) : mem.read p 4 = v.toNat := by
  obtain ⟨m, hm', -, hv⟩ := h
  have he : m = mem := Option.some.inj (hm'.symm.trans hm)
  subst m
  have hr := mem.read_of_bytes (ea := p) (k := 4) (v := v.toNat) (by
    intro i hi
    rw [hv i (by simpa [le32] using hi)]
    simp [le32, List.getElem!_eq_getElem?_getD, List.getElem?_range hi])
  simpa only [show 256 ^ 4 = 2 ^ 32 by decide, Nat.mod_eq_of_lt v.isLt] using hr

theorem read64 {s : Store} {mem : MemInst} {p : Nat} {v : BitVec 64}
    (hm : s.mems[0]? = some mem) (h : Holds s p (le64 v)) : mem.read p 8 = v.toNat := by
  obtain ⟨m, hm', -, hv⟩ := h
  have he : m = mem := Option.some.inj (hm'.symm.trans hm)
  subst m
  have hr := mem.read_of_bytes (ea := p) (k := 8) (v := v.toNat) (by
    intro i hi
    rw [hv i (by simpa [le64, Binary.leBytes] using hi)]
    interval_cases i <;> simp only [le64, Binary.leBytes, List.getElem!_cons_zero,
      List.getElem!_cons_succ, Nat.div_div_eq_div_mul, Nat.reduceMul, Nat.reducePow,
      Nat.pow_zero, Nat.div_one] <;> apply UInt8.toNat_inj.mp <;> simp)
  simpa only [show 256 ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt v.isLt] using hr

theorem cpm_type : Lifted.module.types.getD Lifted.func86.type ⟨[], []⟩ =
    ⟨[.num .i32, .num .i32, .num .i32, .num .i32], []⟩ := rfl

theorem row_type : Lifted.module.types.getD Lifted.func133.type ⟨[], []⟩ =
    ⟨[.num .i32, .num .i32, .num .i32], []⟩ := rfl

structure Allocated (heap : Nat → Prop) (blocks : Store → List (Nat × Nat))
    (ready : Nat → Store → Prop) (k z : Nat) (s s' : Store) (p : BitVec 32) : Prop where
  ext : Store.Extends s s'
  next : ready k s'
  bound : p.toNat + z ≤ 2 ^ 32
  fresh : ∀ a, p.toNat ≤ a → a < p.toNat + z → heap a ∧ ¬ InBlocks (blocks s) a
  zero : Holds s' p.toNat (List.replicate z 0)
  member : (p.toNat, z) ∈ blocks s'
  old : ∀ b ∈ blocks s, b ∈ blocks s'
  same : SameOn s s' fun a => ¬ heap a ∨ InBlocks (blocks s) a

theorem alloc_result {H : HostSem} {alloc free cap k : Nat} {heap : Nat → Prop}
    {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    (hA : Allocator H alloc free heap cap blocks ready) {s : Store} {n sz : BitVec 32}
    (hr : ready (k + 1) s) (hz : 0 < n.toNat * sz.toNat) (hc : n.toNat * sz.toNat ≤ cap) :
    (∃ s' p, H alloc s [.i32 n, .i32 sz] (.returned s' [.i32 p])) ∧
    ∀ o, H alloc s [.i32 n, .i32 sz] o → ∃ s' p,
      o = .returned s' [.i32 p] ∧ Allocated heap blocks ready k (n.toNat * sz.toNat) s s' p := by
  obtain ⟨hex, hall⟩ := hA.alloc k s n sz hr hz hc
  have hp : ∀ o, H alloc s [.i32 n, .i32 sz] o → ∃ s' p,
      o = .returned s' [.i32 p] ∧ Allocated heap blocks ready k (n.toNat * sz.toNat) s s' p := by
    intro o ho
    obtain ⟨s', p, he, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hall o ho
    exact ⟨s', p, he, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩
  refine ⟨?_, hp⟩
  obtain ⟨o, ho⟩ := hex
  obtain ⟨s', p, rfl, -⟩ := hp o ho
  exact ⟨s', p, ho⟩

theorem must_alloc {H : HostSem} {Q : Outcome → Prop} {alloc free cap k a : Nat}
    {heap : Nat → Prop} {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    {s : Store} {f : Frame} {es : List AInstr} {n sz : BitVec 32}
    (hA : Allocator H alloc free heap cap blocks ready) (hr : ready (k + 1) s)
    (hz : 0 < n.toNat * sz.toNat) (hc : n.toNat * sz.toNat ≤ cap)
    (hf : s.funcs[a]? = some (.host ⟨[.num .i32, .num .i32], [.num .i32]⟩ alloc))
    (hfocus : seqFocus (HostAt a 2 [.i32 n, .i32 sz]) [] es)
    (hk : ∀ s' p, Allocated heap blocks ready k (n.toNat * sz.toNat) s s' p →
      Must H Q ⟨s', f, seqPlug 2 (vals [.i32 p]) [] es⟩) : Must H Q ⟨s, f, es⟩ := by
  obtain ⟨hex, hall⟩ := alloc_result hA hr hz hc
  apply must_host_focus hf hfocus
  · obtain ⟨s', p, hp⟩ := hex
    exact ⟨s', [.i32 p], hp⟩
  · intro o ho
    obtain ⟨s', p, he, -⟩ := hall o ho
    exact ⟨s', [.i32 p], he⟩
  · intro s' res ho
    obtain ⟨s'', p, he, hp⟩ := hall _ ho
    cases he
    exact hk _ p hp

end Subjects.EdgerCpm.Body
