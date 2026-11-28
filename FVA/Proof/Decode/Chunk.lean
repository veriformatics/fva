import FVA.Proof.Decode.Module
import FVA.Lifted

/-!
# Chunked `decode_eq` assembly (U29c, `docs/contracts/U29c-bustools.md`; proof tooling)

A module whose code payload exceeds `fva lift`'s threshold gets `decode_eq` from small facts the
kernel checks one declaration each: per chunk of code entries `many code c chunk m = .ok es 0 0`,
the header + each slot's step, the code section's `sub`, `finish`. These lemmas stitch them by
directed applications: a successful parse of a fully consumed packed prefix extends to the longer
input (`closed_append`, from `Parses.sound`/`complete`), so `many code` never runs on a large
suffix. Theorems alone: this module enters every chunked subject's spec closure through `Lifted`.
-/

namespace FVA.Wasm.Decode.Chunk

open FVA.Wasm FVA.Wasm.Binary FVA.Wasm.Decode

/-- A closed, successful parse extends to a longer packed input, given exact widths. -/
theorem closed_append {α : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) {a : α} {lo hi m n : Nat} (hlo : lo < 256 ^ m)
    (hhi : hi < 256 ^ n) (h : p lo m = .ok a 0 0) :
    p (lo + 256 ^ m * hi) (m + n) = .ok a hi n := by
  have hc : p (pack (leBytes m lo)) (leBytes m lo).length = .ok a 0 0 := by
    simpa only [pack_leBytes hlo, leBytes_length] using h
  obtain ⟨pre, rest, he, hr, _, hn⟩ := hp.sound hc
  have hnil : rest = [] := List.eq_nil_of_length_eq_zero hn.symm
  rw [hnil, List.append_nil] at he
  have hr' : R a (leBytes m lo) := he.symm ▸ hr
  simpa only [pack_append, pack_leBytes hlo, pack_leBytes hhi, List.length_append,
    leBytes_length] using hp.complete (leBytes n hi) hr'

/-- `many` over `a + b` items = `a` items, then `b` more (failures propagate). -/
theorem many_split {α : Type} (p : Nat → Nat → Res α) (a b v n : Nat) :
    many p (a + b) v n = (many p a v n).bind fun xs v n =>
      (many p b v n).bind fun ys v n => .ok (xs ++ ys) v n := by
  induction a generalizing v n with
  | zero =>
    simp only [Nat.zero_add, many, Res.bind_ok, List.nil_append]
    cases many p b v n <;> rfl
  | succ a ih =>
    simp only [Nat.succ_add, many.eq_2]
    cases p v n <;> simp only [Res.bind]
    case ok x v₁ n₁ =>
      rw [ih]
      cases many p a v₁ n₁ <;> simp only [Res.bind]
      case ok xs v₂ n₂ => cases many p b v₂ n₂ <;> rfl

/-- `v` fits in `k` bytes, stated as a shift (a kernel evaluates `v >>> 8k` without `256 ^ k`). -/
theorem lt_of_shiftRight {v k : Nat} (h : v >>> (8 * k) = 0) : v < 256 ^ k := by
  rw [Nat.shiftRight_eq_div_pow] at h
  rw [show (256 : Nat) ^ k = 2 ^ (8 * k) by rw [Nat.pow_mul]]
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp h

/-- Two chunks of code entries, each decoded on its own numeral, decode as one. Shifts, not
`256 ^ m * hi`: con-ron's memory for a product grows with the product of the operand sizes (a 30
KB numeral times `256 ^ 29852`: 642 MB; bustools' packed code section: past 25 GB), a shift's
with the result (85 MB). -/
theorem two_chunks {lo hi m n a b : Nat} {xs ys : List (List (Nat × ValType) × Expr)}
    (hlo : lo >>> (8 * m) = 0) (hhi : hi >>> (8 * n) = 0)
    (hx : many code a lo m = .ok xs 0 0) (hy : many code b hi n = .ok ys 0 0) :
    many code (a + b) (lo + hi <<< (8 * m)) (m + n) = .ok (xs ++ ys) 0 0 := by
  rw [show hi <<< (8 * m) = 256 ^ m * hi by rw [Nat.shiftLeft_eq, Nat.pow_mul, Nat.mul_comm],
    many_split, closed_append (many_parses code_parses a) (lt_of_shiftRight hlo)
      (lt_of_shiftRight hhi) hx, Res.bind_ok, hy, Res.bind_ok]

/-- The code vector from its count and its entries. -/
theorem vec_of_count {c v n v' n' : Nat} {entries : List (List (Nat × ValType) × Expr)}
    (hc : u32 v n = .ok c v' n') (hle : c ≤ n')
    (h : many code c v' n' = .ok entries 0 0) : vec code v n = .ok entries 0 0 := by
  simp only [vec, hc, Res.bind_ok, blt_false.mpr hle, Bool.cond_false, h]

/-- The code section from its entry vector. -/
theorem code_section {a : Acc} {v n : Nat} {cs : List (List (Nat × ValType) × Expr)}
    (h : vec code v n = .ok cs 0 0) : sectionInto 10 a v n = .ok { a with codes := cs } 0 0 := by
  simp only [sectionInto, h]; rfl

/-- A section's `sub` window from its decoded content. -/
theorem sub_of_leNat {α : Type} {p : Nat → Nat → Res α} {x y n v r : Nat} {a : α}
    (h : leNat x v n = .ok y r (n - x)) (hp : p y x = .ok a 0 0) :
    sub x p v n = .ok a r (n - x) := by
  cases hb : Nat.blt n x
  · simp only [leNat, hb, Bool.cond_false, Res.ok.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    simp only [sub, hb, Bool.cond_false, hp, Nat.sub_eq]
  · simp [leNat, hb] at h

/-- A slot present in the input: its section read, the rest of the slots after it. -/
theorem slot_take {id : Nat} {ids : List Nat} {a a' : Acc} {v n v' n' w r x s y t : Nat}
    (hc : customs n v n = .ok () v' n')
    (hpeek : (!Nat.beq n' 0 && Nat.beq (Nat.land v' 255) id) = true)
    (hb : byte v' n' = .ok id w r) (hu : u32 w r = .ok s x y)
    (hs : sub s (sectionInto id a) x y = .ok a' t (y - s)) :
    slots (id :: ids) a v n = slots ids a' t (y - s) := by
  rw [slots_cons, hc, Res.bind_ok, hpeek]
  simp only [Bool.cond_true, hb, Res.bind_ok, hu, hs]

/-- A slot absent from the input: the rest of the slots after its customs. -/
theorem slot_skip {id : Nat} {ids : List Nat} {a : Acc} {v n v' n' : Nat}
    (hc : customs n v n = .ok () v' n')
    (hpeek : (!Nat.beq n' 0 && Nat.beq (Nat.land v' 255) id) = false) :
    slots (id :: ids) a v n = slots ids a v' n' := by
  rw [slots_cons, hc, Res.bind_ok, hpeek]; rfl

/-- `decode` from its header, slot and `finish` facts. -/
theorem decode_of_steps {bytes len v₁ n₁ v₂ n₂ tail : Nat} {a : Acc} {m : Module}
    (hMagic : leNat 4 bytes len = .ok 0x6d736100 v₁ n₁)
    (hVersion : leNat 4 v₁ n₁ = .ok 1 v₂ n₂)
    (hSlots : slots slotIds {} v₂ n₂ = .ok a tail 0)
    (hFinish : finish a 0 = .ok m 0 0) : decode bytes len = .ok m := by
  simp only [decode, hMagic, Res.bind_ok, hVersion, hSlots, hFinish]
  rfl

end FVA.Wasm.Decode.Chunk
