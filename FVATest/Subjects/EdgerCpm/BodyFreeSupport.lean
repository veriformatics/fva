import FVATest.Subjects.EdgerCpm.BodyRows

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

structure Freed (heap : Nat → Prop) (blocks : Store → List (Nat × Nat))
    (ready : Nat → Store → Prop) (k : Nat) (s s' : Store) (p : BitVec 32) : Prop where
  ext : Store.Extends s s'
  next : ready k s'
  old : ∀ b ∈ blocks s, b.1 ≠ p.toNat → b ∈ blocks s'
  same : SameOn s s' fun a => ¬ heap a ∨ InBlocks ((blocks s).filter (·.1 ≠ p.toNat)) a

theorem free_result {H : HostSem} {alloc free cap k z : Nat} {heap : Nat → Prop}
    {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    (hA : Allocator H alloc free heap cap blocks ready) {s : Store} {p : BitVec 32}
    (hr : ready k s) (hp : (p.toNat, z) ∈ blocks s) :
    (∃ s', H free s [.i32 p] (.returned s' [])) ∧
    ∀ o, H free s [.i32 p] o → ∃ s', o = .returned s' [] ∧ Freed heap blocks ready k s s' p := by
  obtain ⟨hex, hall⟩ := hA.free k s p z hr hp
  have hh : ∀ o, H free s [.i32 p] o →
      ∃ s', o = .returned s' [] ∧ Freed heap blocks ready k s s' p := by
    intro o ho
    obtain ⟨s', he, h₁, h₂, h₃, h₄⟩ := hall o ho
    exact ⟨s', he, ⟨h₁, h₂, h₃, h₄⟩⟩
  refine ⟨?_, hh⟩
  obtain ⟨o, ho⟩ := hex
  obtain ⟨s', rfl, -⟩ := hh o ho
  exact ⟨s', ho⟩

theorem must_free {H : HostSem} {Q : Outcome → Prop} {alloc free cap k a z : Nat}
    {heap : Nat → Prop} {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    {s : Store} {f : Frame} {es : List AInstr} {p : BitVec 32}
    (hA : Allocator H alloc free heap cap blocks ready) (hr : ready k s)
    (hp : (p.toNat, z) ∈ blocks s)
    (hf : s.funcs[a]? = some (.host ⟨[.num .i32], []⟩ free))
    (hfocus : seqFocus (HostAt a 1 [.i32 p]) [] es)
    (hk : ∀ s', Freed heap blocks ready k s s' p →
      Must H Q ⟨s', f, seqPlug 1 [] [] es⟩) : Must H Q ⟨s, f, es⟩ := by
  obtain ⟨hex, hall⟩ := free_result hA hr hp
  apply must_host_focus hf hfocus
  · obtain ⟨s', hs'⟩ := hex
    exact ⟨s', [], hs'⟩
  · intro o ho
    obtain ⟨s', he, -⟩ := hall o ho
    exact ⟨s', [], he⟩
  · intro s' res ho
    obtain ⟨s'', he, hh⟩ := hall _ ho
    cases he
    exact hk _ hh

theorem private_start_ne {initial : List (Nat × Nat)} {p : Nat} {q : Nat × Nat}
    (hp : ¬ InBlocks initial p) (hq : q ∈ initial) (hz : 0 < q.2) : q.1 ≠ p := by
  intro he
  apply hp
  exact ⟨q, hq, by omega, by omega⟩

def PositiveOld (initial : List (Nat × Nat)) (bs : List (Nat × Nat)) : Prop :=
  ∀ q ∈ initial, 0 < q.2 → q ∈ bs

theorem Freed.positive {heap : Nat → Prop} {blocks : Store → List (Nat × Nat)}
    {ready : Nat → Store → Prop} {k : Nat} {s s' : Store} {p : BitVec 32}
    {initial : List (Nat × Nat)} (h : Freed heap blocks ready k s s' p)
    (hold : PositiveOld initial (blocks s)) (hp : ¬ InBlocks initial p.toNat) :
    PositiveOld initial (blocks s') := by
  intro q hq hz
  exact h.old q (hold q hq hz) (private_start_ne hp hq hz)

theorem Freed.caller {heap : Nat → Prop} {blocks : Store → List (Nat × Nat)}
    {ready : Nat → Store → Prop} {k : Nat} {s s' : Store} {p : BitVec 32}
    {initial : List (Nat × Nat)} {P : Nat → Prop} (h : Freed heap blocks ready k s s' p)
    (hold : PositiveOld initial (blocks s)) (hp : ¬ InBlocks initial p.toNat)
    (hP : ∀ a, P a → ¬ heap a ∨ InBlocks initial a) : SameOn s s' P := by
  apply same_mono h.same
  intro a ha
  rcases hP a ha with hn | ⟨q, hq, hl, hh⟩
  · exact Or.inl hn
  · have hz : 0 < q.2 := by omega
    right
    refine ⟨q, ?_, hl, hh⟩
    simp only [List.mem_filter, decide_eq_true_iff]
    exact ⟨hold q hq hz, private_start_ne hp hq hz⟩

def post (W : World) : Outcome → Prop
  | .returned s vs => vs = [] ∧
    (∀ i < W.x.n, ∀ j < W.x.m, ∃ out, Holds s (W.l.cell W.x i j) (le64 out) ∧
      CpmElem (W.x.count i j) (W.x.libSize j) out) ∧ SameOn W.initial s (W.l.kept W.x)
  | .trapped _ => False

end Subjects.EdgerCpm.Body
