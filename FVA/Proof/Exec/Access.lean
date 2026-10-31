import FVA.Impl.Exec.Access
import FVA.Spec.Exec.Access
import FVA.Proof.Exec.Det

/-!
# The access checker computes the spec's footprint relations

`access c` covers byte `a` of memory `ma` as a read exactly when `Reads c ma a` (`reads_iff`),
as a write exactly when `Writes c ma a` (`writes_iff`).
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- `x` is a read (`write = false`) or write of memory `ma` covering byte `a`. -/
def Access.Covers (x : Access) (write : Bool) (ma a : Nat) : Prop :=
  x.write = write ∧ x.mem = ma ∧ x.start ≤ a ∧ a < x.start + x.len

theorem rangeAccess_eq_some {s : Store} {f : Frame} {w : Bool} {ea n : Nat} {x : Access} :
    rangeAccess s f w ea n = some x ↔
      ∃ ma mem, f.inst.mems[0]? = some ma ∧ s.mems[ma]? = some mem ∧ ea + n ≤ mem.size ∧
        x = ⟨w, ma, ea, n⟩ := by
  unfold rangeAccess
  cases h : mem0 s f with
  | none =>
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro ma mem hm hmem
    simp [mem0_eq_some.mpr ⟨hm, hmem⟩] at h
  | some p =>
    obtain ⟨ma, mem⟩ := p
    obtain ⟨hm, hmem⟩ := mem0_eq_some.mp h
    by_cases hb : mem.size < ea + n
    · simp only [Nat.blt_eq.mpr hb, Bool.cond_true, reduceCtorEq, false_iff, not_exists, not_and]
      intro ma' mem' hm' hmem' hle
      rw [hm] at hm'; cases hm'; rw [hmem] at hmem'; cases hmem'; omega
    · have : Nat.blt mem.size (ea + n) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hb
      simp only [this, Bool.cond_false, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨ma, mem, hm, hmem, by omega, rfl⟩
      · rintro ⟨ma', mem', hm', hmem', -, rfl⟩
        rw [hm] at hm'; cases hm'; rfl

theorem seqAccess_vals (s : Store) (f : Frame) (stk vs : List Val) (es : List AInstr) :
    seqAccess s f stk (vals vs ++ es) = seqAccess s f (vs.reverse ++ stk) es := by
  induction vs generalizing stk with
  | nil => rfl
  | cons v vs ih =>
    rw [vals, List.map_cons, List.cons_append, seqAccess, toVal_instr]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (v :: stk)

theorem seqAccess_append {s : Store} {f : Frame} {stk : List Val} {es : List AInstr} {x : Access}
    (h : seqAccess s f stk es = some x) (rest : List AInstr) :
    seqAccess s f stk (es ++ rest) = some x := by
  induction es generalizing stk with
  | nil => simp [seqAccess] at h
  | cons e es ih =>
    rw [List.cons_append, seqAccess]
    rw [seqAccess] at h
    cases hv : toVal e with
    | some v => rw [hv] at h; exact ih h
    | none => rw [hv] at h; exact h

/-- A redex `es` with access `x` keeps it under values before it and instructions after it. -/
theorem seqAccess_seq {s : Store} {f : Frame} {es : List AInstr} {x : Access}
    (h : ∀ stk, seqAccess s f stk es = some x) (vs : List Val) (rest : List AInstr)
    (stk : List Val) :
    seqAccess s f stk (vals vs ++ es ++ rest) = some x := by
  rw [List.append_assoc, seqAccess_vals]
  exact seqAccess_append (h _) rest

private theorem toVal_plain_mem {i : Instr}
    (hi : (∃ t m, i = .load t m) ∨ (∃ w p sx m, i = .loadPacked w p sx m) ∨
      (∃ t m, i = .store t m) ∨ (∃ w p m, i = .storePacked w p m)) :
    toVal (.plain i) = none := by
  rcases hi with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

theorem seqAccess_of_reads {c : Config} {ma a : Nat} (h : Reads c ma a) :
    ∃ x, (∀ stk, seqAccess c.store c.frame stk c.instrs = some x) ∧ x.Covers false ma a := by
  induction h with
  | @load s f t m ma mem a i hm hmem hb hlo hhi =>
    refine ⟨⟨false, ma, i.toNat + m.offset, t.bytes⟩, fun stk => ?_, rfl, rfl, hlo, hhi⟩
    simp only [seqAccess, toVal_instr, toVal_plain_mem (.inl ⟨t, m, rfl⟩), atAccess, instrAccess]
    exact rangeAccess_eq_some.mpr ⟨ma, mem, hm, hmem, hb, rfl⟩
  | @loadPacked s f w p sx m ma mem a i hm hmem hb hlo hhi =>
    refine ⟨⟨false, ma, i.toNat + m.offset, p.bits / 8⟩, fun stk => ?_, rfl, rfl, hlo, hhi⟩
    simp only [seqAccess, toVal_instr, toVal_plain_mem (.inr (.inl ⟨w, p, sx, m, rfl⟩)), atAccess,
      instrAccess]
    exact rangeAccess_eq_some.mpr ⟨ma, mem, hm, hmem, hb, rfl⟩
  | seq _ ih =>
    obtain ⟨x, hx, hc⟩ := ih
    exact ⟨x, seqAccess_seq hx _ _, hc⟩
  | label _ ih =>
    obtain ⟨x, hx, hc⟩ := ih
    exact ⟨x, fun stk => by simp only [seqAccess, atAccess]; exact hx [], hc⟩
  | frame _ ih =>
    obtain ⟨x, hx, hc⟩ := ih
    exact ⟨x, fun stk => by simp only [seqAccess, atAccess]; exact hx [], hc⟩

theorem seqAccess_of_writes {c : Config} {ma a : Nat} (h : Writes c ma a) :
    ∃ x, (∀ stk, seqAccess c.store c.frame stk c.instrs = some x) ∧ x.Covers true ma a := by
  induction h with
  | @store s f t m ma mem a c i v hm hmem hc hb hlo hhi =>
    refine ⟨⟨true, ma, i.toNat + m.offset, t.bytes⟩, fun stk => ?_, rfl, rfl, hlo, hhi⟩
    simp only [seqAccess, toVal_instr, toVal_plain_mem (.inr (.inr (.inl ⟨t, m, rfl⟩))), atAccess,
      instrAccess, hc]
    exact rangeAccess_eq_some.mpr ⟨ma, mem, hm, hmem, hb, rfl⟩
  | @storePacked s f w p m ma mem a c i v hm hmem hc hb hlo hhi =>
    refine ⟨⟨true, ma, i.toNat + m.offset, p.bits / 8⟩, fun stk => ?_, rfl, rfl, hlo, hhi⟩
    simp only [seqAccess, toVal_instr, toVal_plain_mem (.inr (.inr (.inr ⟨w, p, m, rfl⟩))),
      atAccess, instrAccess, hc]
    exact rangeAccess_eq_some.mpr ⟨ma, mem, hm, hmem, hb, rfl⟩
  | seq _ ih =>
    obtain ⟨x, hx, hc⟩ := ih
    exact ⟨x, seqAccess_seq hx _ _, hc⟩
  | label _ ih =>
    obtain ⟨x, hx, hc⟩ := ih
    exact ⟨x, fun stk => by simp only [seqAccess, atAccess]; exact hx [], hc⟩
  | frame _ ih =>
    obtain ⟨x, hx, hc⟩ := ih
    exact ⟨x, fun stk => by simp only [seqAccess, atAccess]; exact hx [], hc⟩

/-- The footprint relation an access of kind `write` names. -/
def Touches : Bool → Config → Nat → Nat → Prop
  | false => Reads
  | true => Writes

theorem touches_of_instrAccess {s : Store} {f : Frame} {i : Instr} {vs : List Val} {x : Access}
    (h : instrAccess s f i vs = some x) (rest : List AInstr) {a : Nat}
    (hlo : x.start ≤ a) (hhi : a < x.start + x.len) :
    Touches x.write ⟨s, f, vals vs.reverse ++ .plain i :: rest⟩ x.mem a := by
  have hseq {es : List AInstr} {stk : List Val}
      (he : vals vs.reverse ++ .plain i :: rest = vals stk.reverse ++ es ++ rest)
      (hr : Touches x.write ⟨s, f, es⟩ x.mem a) :
      Touches x.write ⟨s, f, vals vs.reverse ++ .plain i :: rest⟩ x.mem a := by
    rw [he]; revert hr; cases x.write <;> intro hr
    · exact Reads.seq hr
    · exact Writes.seq hr
  cases i <;> try simp only [instrAccess] at h
  all_goals try exact absurd h (by simp)
  case load t m =>
    rcases vs with _ | ⟨_ | _ | _ | _ | _, stk⟩ <;> simp only at h <;>
      try exact absurd h (by simp)
    rename_i ib
    obtain ⟨ma, mem, hm, hmem, hb, rfl⟩ := rangeAccess_eq_some.mp h
    refine hseq (stk := stk) (es := [(Val.i32 ib).instr, .plain (.load t m)]) ?_ ?_
    · simp [vals]
    · exact Reads.load hm hmem hb hlo hhi
  case loadPacked w p sx m =>
    rcases vs with _ | ⟨_ | _ | _ | _ | _, stk⟩ <;> simp only at h <;>
      try exact absurd h (by simp)
    rename_i ib
    obtain ⟨ma, mem, hm, hmem, hb, rfl⟩ := rangeAccess_eq_some.mp h
    refine hseq (stk := stk) (es := [(Val.i32 ib).instr, .plain (.loadPacked w p sx m)]) ?_ ?_
    · simp [vals]
    · exact Reads.loadPacked hm hmem hb hlo hhi
  case store t m =>
    rcases vs with _ | ⟨v, _ | ⟨_ | _ | _ | _ | _, stk⟩⟩ <;> simp only at h <;>
      try exact absurd h (by simp)
    rename_i ib
    cases hc : v.numBits t with
    | none => simp [hc] at h
    | some c =>
      simp only [hc] at h
      obtain ⟨ma, mem, hm, hmem, hb, rfl⟩ := rangeAccess_eq_some.mp h
      refine hseq (stk := stk) (es := [(Val.i32 ib).instr, v.instr, .plain (.store t m)]) ?_ ?_
      · simp [vals]
      · exact Writes.store hm hmem hc hb hlo hhi
  case storePacked w p m =>
    rcases vs with _ | ⟨v, _ | ⟨_ | _ | _ | _ | _, stk⟩⟩ <;> simp only at h <;>
      try exact absurd h (by simp)
    rename_i ib
    cases hc : v.intBits w with
    | none => simp [hc] at h
    | some c =>
      simp only [hc] at h
      obtain ⟨ma, mem, hm, hmem, hb, rfl⟩ := rangeAccess_eq_some.mp h
      refine hseq (stk := stk)
        (es := [(Val.i32 ib).instr, v.instr, .plain (.storePacked w p m)]) ?_ ?_
      · simp [vals]
      · exact Writes.storePacked hm hmem hc hb hlo hhi

theorem touches_of_seqAccess (n : Nat) : ∀ {f : Frame} {vs : List Val} {es : List AInstr}
    {x : Access} {s : Store} {a : Nat}, seqSize es ≤ n → seqAccess s f vs es = some x →
    x.start ≤ a → a < x.start + x.len → Touches x.write ⟨s, f, vals vs.reverse ++ es⟩ x.mem a := by
  induction n with
  | zero =>
    intro f vs es x s a hn h
    rw [Nat.le_zero, seqSize_zero] at hn
    subst hn
    simp [seqAccess] at h
  | succ n ih =>
    intro f vs es x s a hn h hlo hhi
    cases es with
    | nil => simp [seqAccess] at h
    | cons e rest =>
      have hsz : seqSize (e :: rest) = adminSize e + seqSize rest := rfl
      have hpos := adminSize_pos e
      rw [seqAccess] at h
      cases hv : toVal e with
      | some v =>
        rw [hv] at h
        have := ih (by omega) h hlo hhi
        rw [eq_instr_of_toVal hv]
        simpa only [List.reverse_cons, vals, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append] using this
      | none =>
        rw [hv] at h
        cases e with
        | label k cont body =>
          simp only [atAccess] at h
          have hb := ih (vs := []) (by simp only [adminSize] at hsz; omega) h hlo hhi
          simp only [List.reverse_nil, vals, List.map_nil, List.nil_append] at hb
          have he : vals vs.reverse ++ AInstr.label k cont body :: rest =
              vals vs.reverse ++ [.label k cont body] ++ rest := by simp
          rw [he]
          revert hb; cases x.write <;> intro hb
          · exact Reads.seq (Reads.label hb)
          · exact Writes.seq (Writes.label hb)
        | frame k fi body =>
          simp only [atAccess] at h
          have hb := ih (vs := []) (f := fi) (by simp only [adminSize] at hsz; omega) h hlo hhi
          simp only [List.reverse_nil, vals, List.map_nil, List.nil_append] at hb
          have he : vals vs.reverse ++ AInstr.frame k fi body :: rest =
              vals vs.reverse ++ [.frame k fi body] ++ rest := by simp
          rw [he]
          revert hb; cases x.write <;> intro hb
          · exact Reads.seq (Reads.frame hb)
          · exact Writes.seq (Writes.frame hb)
        | plain i =>
          simp only [atAccess] at h
          exact touches_of_instrAccess h rest hlo hhi
        | _ => simp [atAccess] at h

theorem reads_iff {c : Config} {ma a : Nat} :
    Reads c ma a ↔ ∃ x, access c = some x ∧ x.Covers false ma a := by
  constructor
  · intro h
    obtain ⟨x, hx, hc⟩ := seqAccess_of_reads h
    exact ⟨x, hx [], hc⟩
  · rintro ⟨x, hx, hw, rfl, hlo, hhi⟩
    have := touches_of_seqAccess _ (vs := []) le_rfl hx hlo hhi
    simpa [Touches, hw] using this

theorem writes_iff {c : Config} {ma a : Nat} :
    Writes c ma a ↔ ∃ x, access c = some x ∧ x.Covers true ma a := by
  constructor
  · intro h
    obtain ⟨x, hx, hc⟩ := seqAccess_of_writes h
    exact ⟨x, hx [], hc⟩
  · rintro ⟨x, hx, hw, rfl, hlo, hhi⟩
    have := touches_of_seqAccess _ (vs := []) le_rfl hx hlo hhi
    simpa [Touches, hw] using this

end FVA.Wasm.Exec.Ref
