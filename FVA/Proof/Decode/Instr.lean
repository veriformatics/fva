import FVA.Proof.Decode.Reader
import FVA.Spec.Binary.Module

/-!
# Instruction decoding is sound and complete

Value, reference and block types, `memarg`, `vec`, the opcode tables, every non-structured
instruction (`instr`), and instruction sequences (`seq`, `expr`) against `FVA.Wasm.Binary`.
The decoder's opcode families equal the spec tables by `rfl` (`numOp_table`, …), so the
dispatch tree is checked once against the reviewed listing.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm FVA.Wasm.Binary

/-! ## Vectors -/

theorem Seq.length_le {α : Type} {R : α → List UInt8 → Prop} (hne : ∀ a bs, R a bs → bs ≠ [])
    {xs : List α} {bs : List UInt8} (h : Seq R xs bs) : xs.length ≤ bs.length := by
  induction h with
  | nil => simp
  | cons ha _ ih =>
    have := List.length_pos_iff.2 (hne _ _ ha)
    simp only [List.length_cons, List.length_append]
    omega

/-- `vec p` parses `vec(R)` when every `R`-encoding is non-empty. -/
theorem vec_parses {α : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) (hne : ∀ a bs, R a bs → bs ≠ []) : Parses (vec p) (Vec R) := by
  constructor
  · intro bs xs v n h
    obtain ⟨c, v', n', hc, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b₁, rest₁, rfl, hu, rfl, rfl⟩ := u32_parses.sound hc
    cases hb : Nat.blt rest₁.length c
    · simp only [hb, Bool.cond_false] at hk
      obtain ⟨b₂, rest, rfl, ⟨hl, hs⟩, rfl, rfl⟩ := (many_parses hp c).sound hk
      exact ⟨b₁ ++ b₂, rest, by simp, ⟨b₁, b₂, hl ▸ hu, hs, rfl⟩, rfl, rfl⟩
    · simp [hb] at hk
  · rintro xs _ rest ⟨b₁, b₂, hu, hs, rfl⟩
    have hle := Seq.length_le hne hs
    have hb : Nat.blt (b₂ ++ rest).length xs.length = false := blt_false.2 (by simp; omega)
    simp only [vec, List.append_assoc]
    rw [u32_parses.complete (b₂ ++ rest) hu, Res.bind_ok]
    simp only [hb, Bool.cond_false]
    exact (many_parses hp xs.length).complete rest ⟨rfl, hs⟩

/-- Returning a value consumes nothing. -/
theorem pure_parses {α : Type} (a : α) :
    Parses (fun v n => .ok a v n) (fun b bs => b = a ∧ bs = []) :=
  ⟨fun {bs _ _ _} h => by
    simp only [Res.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨[], bs, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩,
   fun rest ⟨h₁, h₂⟩ => by subst h₁; subst h₂; rfl⟩

/-! ## Types and immediates -/

/-- Parsing then wrapping the value: the wrapped success splits the input like the parser's. -/
theorem Parses.map_sound {α β : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) {f : α → β} {bs : List UInt8} {b : β} {v n : Nat}
    (h : (p (pack bs) bs.length).bind (fun x v n => .ok (f x) v n) = .ok b v n) :
    ∃ x imm rest, bs = imm ++ rest ∧ R x imm ∧ b = f x ∧ v = pack rest ∧ n = rest.length := by
  obtain ⟨x, v', n', hx, hk⟩ := Res.bind_eq_ok.1 h
  simp only [Res.ok.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  obtain ⟨imm, rest, rfl, hR, rfl, rfl⟩ := hp.sound hx
  exact ⟨x, imm, rest, rfl, hR, rfl, rfl, rfl⟩

/-- An `sN` encoding (`N > 0`) has at most `⌈N/7⌉` bytes. -/
theorem _root_.FVA.Wasm.Binary.SLeb.length_le {N : Nat} {i : Int} {bs : List UInt8}
    (h : SLeb N i bs) : 7 * bs.length < N + 7 ∨ N = 0 := by
  induction h with
  | pos => simp; omega
  | neg => simp; omega
  | more _ _ _ _ ih => simp; omega

theorem _root_.FVA.Wasm.Binary.SLeb.ne_nil {N : Nat} {i : Int} {bs : List UInt8}
    (h : SLeb N i bs) : bs ≠ [] := by
  cases h <;> simp

/-- The first byte of an `sN` encoding: last and non-negative, last and negative, or not last. -/
theorem _root_.FVA.Wasm.Binary.SLeb.head_cases {N : Nat} {i : Int} {b : UInt8}
    {rest : List UInt8} (h : SLeb N i (b :: rest)) :
    (b.toNat < 64 ∧ i = b.toNat) ∨ (64 ≤ b.toNat ∧ b.toNat < 128 ∧ i < 0) ∨ 128 ≤ b.toNat := by
  cases h with
  | pos _ h6 _ => exact .inl ⟨by simpa using h6, rfl⟩
  | neg _ h6 h7 _ => exact .inr (.inl ⟨by simpa using h6, by simpa using h7, by simp at h7; omega⟩)
  | more _ h7 _ _ => exact .inr (.inr (by simpa using h7))

/-- An `sN` value lies in `[−2^(N−1), 2^(N−1))`. -/
theorem _root_.FVA.Wasm.Binary.SLeb.range {N : Nat} {i : Int} {bs : List UInt8} (h : SLeb N i bs)
    (hN : 0 < N) : -(2 : Int) ^ (N - 1) ≤ i ∧ i < 2 ^ (N - 1) := by
  induction h with
  | @pos N' b _ hb =>
    have : ((2 ^ (N' - 1) : Nat) : Int) = (2 : Int) ^ (N' - 1) := by push_cast; rfl
    have : (0 : Int) < 2 ^ (N' - 1) := Int.pow_pos (by decide)
    constructor <;> omega
  | @neg N' b _ h7 hb =>
    have : (0 : Int) < 2 ^ (N' - 1) := Int.pow_pos (by decide)
    have : (b.toNat : Int) < 2 ^ 7 := by exact_mod_cast h7
    constructor <;> omega
  | @more N' m rest b h7 hN' hm ih =>
    have ih := ih (by omega)
    have hb := b.toNat_lt
    have hP : (2 : Int) ^ (N' - 1) = 128 * 2 ^ (N' - 7 - 1) := by
      rw [show N' - 1 = (N' - 7 - 1) + 7 by omega, Int.pow_add, show (2 : Int) ^ 7 = 128 by decide,
        Int.mul_comm]
    have h7' : (2 ^ 7 : Int) ≤ b.toNat := by exact_mod_cast h7
    have hb' : (b.toNat : Int) < 256 := by omega
    rw [hP]
    simp only [show (2 : Int) ^ 7 = 128 by decide] at h7' ⊢
    constructor <;> omega

/-- A non-negative `s33` (a type index): `sleb 5 33`, then the `< 2^32` check. -/
theorem s33_sound {bs : List UInt8} {x : Nat} {v n : Nat}
    (hs : sleb 5 33 (pack bs) bs.length = .ok x v n) (hx : Nat.blt x (2 ^ 32) = true) :
    ∃ pre rest, bs = pre ++ rest ∧ SLeb 33 (x : Int) pre ∧ v = pack rest ∧ n = rest.length := by
  obtain ⟨pre, rest, hpre, ⟨i, hi, rfl, -⟩, rfl, rfl⟩ := (sleb_parses 5 33).sound hs
  have hr := hi.range (by decide)
  have hlt := blt_true.1 hx
  have hi0 : 0 ≤ i := by
    rcases Int.lt_or_le i 0 with hneg | hpos
    · have : i % 2 ^ 33 = i + 2 ^ 33 := by
        rw [← Int.add_emod_right, Int.emod_eq_of_lt (by simp at hr; omega) (by omega)]
      rw [this] at hlt; simp at hr hlt; omega
    · exact hpos
  refine ⟨pre, rest, hpre, ?_, rfl, rfl⟩
  rwa [Int.emod_eq_of_lt hi0 (by simp at hr; omega), Int.toNat_of_nonneg hi0]

theorem s33_complete {x : Nat} {pre : List UInt8} (h : SLeb 33 (x : Int) pre)
    (rest : List UInt8) :
    sleb 5 33 (pack (pre ++ rest)) (pre ++ rest).length = .ok x (pack rest) rest.length ∧
      Nat.blt x (2 ^ 32) = true := by
  have hr := h.range (by decide)
  have hx : ((x : Int) % 2 ^ 33).toNat = x := by
    rw [Int.emod_eq_of_lt (by omega) (by simp at hr; omega)]; simp
  exact ⟨(sleb_parses 5 33).complete rest ⟨x, h, hx.symm, by have := h.length_le; omega⟩,
    blt_true.2 (by simp at hr; omega)⟩

/-- The first byte of a non-negative `s33` is below `0x40` or at least `0x80`. -/
theorem s33_head {x : Nat} {b : UInt8} {pre : List UInt8} (h : SLeb 33 (x : Int) (b :: pre)) :
    b.toNat < 0x40 ∨ 0x80 ≤ b.toNat := by
  rcases h.head_cases with ⟨_, _⟩ | ⟨_, _, hneg⟩ | _
  · omega
  · omega
  · omega

theorem numTypeOf_some {k : Nat} {t : NumType} (h : numTypeOf k = some t) :
    NumTypeB t [k.toUInt8] := by
  simp only [numTypeOf, Bool.cond_eq_ite, Nat.beq_eq] at h
  repeat' split at h
  all_goals (cases h <;> subst_vars <;> rfl)

theorem numTypeOf_none {k : Nat} (h : k < 0x7C ∨ 0x7F < k) : numTypeOf k = none := by
  simp only [numTypeOf, Bool.cond_eq_ite, Nat.beq_eq]
  repeat' split
  all_goals first | rfl | omega

theorem numTypeB_byte {t : NumType} {bs : List UInt8} (h : NumTypeB t bs) :
    ∃ b : UInt8, bs = [b] ∧ numTypeOf b.toNat = some t ∧ 0x7C ≤ b.toNat ∧ b.toNat ≤ 0x7F := by
  cases t <;> (simp only [NumTypeB] at h; subst h; exact ⟨_, rfl, rfl, by decide, by decide⟩)

theorem absHeapOf_some {k : Nat} {a : AbsHeapType} (h : absHeapOf k = some a) :
    (k.toUInt8, a) ∈ absHeapOps := by
  simp only [absHeapOf, Bool.cond_eq_ite, Nat.beq_eq] at h
  repeat' split at h
  all_goals (cases h <;> subst_vars <;> decide)

theorem absHeapOf_none {k : Nat} (h : k < 0x69 ∨ 0x70 < k) : absHeapOf k = none := by
  simp only [absHeapOf, Bool.cond_eq_ite, Nat.beq_eq]
  repeat' split
  all_goals first | rfl | omega

theorem absHeapExcluded_none {k : Nat} (h : k < 0x6A ∨ 0x74 < k) : absHeapExcluded k = none := by
  simp only [absHeapExcluded, Bool.cond_eq_ite, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq,
    Nat.beq_eq]
  repeat' split
  all_goals first | rfl | omega

/-- A P′ abstract heap type's byte is decoded as that type and is no excluded one. -/
theorem absHeapOps_byte {b : UInt8} {a : AbsHeapType} (h : (b, a) ∈ absHeapOps) :
    absHeapOf b.toNat = some a ∧ 0x69 ≤ b.toNat ∧ b.toNat ≤ 0x70 := by
  simp only [absHeapOps, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, by decide, by decide⟩

theorem heapType_parses : Parses heapType HeapTypeB := by
  constructor
  · intro bs ht v n h
    cases bs with
    | nil => simp [heapType] at h
    | cons b bs =>
      simp only [heapType, List.length_cons, land_pack_cons, shiftRight_pack_cons] at h
      split at h
      · rename_i a ha
        simp only [Res.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[b], bs, rfl, ⟨b, by simpa using absHeapOf_some ha, rfl⟩, rfl, rfl⟩
      · split at h
        · simp at h
        · obtain ⟨x, v', n', hs, hk⟩ := Res.bind_eq_ok.1 h
          cases hx : Nat.blt x (2 ^ 32)
          · simp [hx] at hk
          · simp only [hx, Bool.cond_true, Res.ok.injEq] at hk
            obtain ⟨rfl, rfl, rfl⟩ := hk
            obtain ⟨pre, rest, hpre, hS, rfl, rfl⟩ :=
              s33_sound (bs := b :: bs) (by simpa using hs) hx
            exact ⟨pre, rest, hpre, hS, rfl, rfl⟩
  · intro ht pre rest h
    cases ht with
    | abs a =>
      obtain ⟨b, hm, rfl⟩ := h
      obtain ⟨hb, -, -⟩ := absHeapOps_byte hm
      simp only [heapType, List.cons_append, List.nil_append, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, hb]
    | idx x =>
      have h' : SLeb 33 (x : Int) pre := h
      cases pre with
      | nil => exact absurd rfl h'.ne_nil
      | cons b pre =>
        have hb := s33_head h'
        obtain ⟨hs, hx⟩ := s33_complete h' rest
        simp only [heapType, List.cons_append, List.length_cons, land_pack_cons,
          absHeapOf_none (show b.toNat < 0x69 ∨ 0x70 < b.toNat by omega),
          absHeapExcluded_none (show b.toNat < 0x6A ∨ 0x74 < b.toNat by omega)]
        simp only [List.cons_append, List.length_cons] at hs
        rw [hs, Res.bind_ok, hx]; rfl
    | def_ _ | rec_ _ => exact h.elim

theorem refType_parses : Parses refType RefTypeB := by
  constructor
  · intro bs t v n h
    obtain ⟨_, v', n', hb, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, rest, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hb
    cases h1 : Nat.beq b.toNat 0x63
    · simp only [h1, Bool.cond_false] at hk
      cases h2 : Nat.beq b.toNat 0x64
      · simp only [h2, Bool.cond_false] at hk
        split at hk
        · rename_i a ha
          simp only [Res.ok.injEq] at hk
          obtain ⟨rfl, rfl, rfl⟩ := hk
          exact ⟨[b], rest, rfl, .short (by simpa using absHeapOf_some ha), rfl, rfl⟩
        · split at hk <;> simp at hk
      · simp only [h2, Bool.cond_true] at hk
        obtain ⟨ht, imm, rest', rfl, hH, rfl, rfl, rfl⟩ := heapType_parses.map_sound hk
        obtain rfl : b = 0x64 := UInt8.toNat_inj.1 (beq_true.1 h2)
        exact ⟨0x64 :: imm, rest', rfl, .nonNull hH, rfl, rfl⟩
    · simp only [h1, Bool.cond_true] at hk
      obtain ⟨ht, imm, rest', rfl, hH, rfl, rfl, rfl⟩ := heapType_parses.map_sound hk
      obtain rfl : b = 0x63 := UInt8.toNat_inj.1 (beq_true.1 h1)
      exact ⟨0x63 :: imm, rest', rfl, .null hH, rfl, rfl⟩
  · intro t pre rest h
    cases h with
    | @null ht b hH =>
      simp only [refType, List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok, show Nat.beq (UInt8.toNat 0x63) 0x63 = true from rfl,
        Bool.cond_true]
      rw [heapType_parses.complete rest hH, Res.bind_ok]
    | @nonNull ht b hH =>
      simp only [refType, List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok, show Nat.beq (UInt8.toNat 0x64) 0x63 = false from rfl,
        show Nat.beq (UInt8.toNat 0x64) 0x64 = true from rfl, Bool.cond_false, Bool.cond_true]
      rw [heapType_parses.complete rest hH, Res.bind_ok]
    | @short a b hm =>
      obtain ⟨hb, h1, h2⟩ := absHeapOps_byte hm
      simp only [refType, List.cons_append, List.nil_append, byte, List.length_cons,
        land_pack_cons, shiftRight_pack_cons, Res.bind_ok,
        beq_false.2 (show b.toNat ≠ 0x63 by omega), beq_false.2 (show b.toNat ≠ 0x64 by omega),
        Bool.cond_false, hb]

/-- The first byte of a reference type: `0x63`, `0x64` or a P′ abstract heap type's. -/
theorem refTypeB_head {t : RefType} {bs : List UInt8} (h : RefTypeB t bs) :
    ∃ b rest, bs = b :: rest ∧ 0x63 ≤ b.toNat ∧ b.toNat ≤ 0x70 ∧
      (Nat.beq b.toNat 0x63 || Nat.beq b.toNat 0x64 || (absHeapOf b.toNat).isSome) = true := by
  cases h with
  | null => exact ⟨0x63, _, rfl, by decide, by decide, rfl⟩
  | nonNull => exact ⟨0x64, _, rfl, by decide, by decide, rfl⟩
  | @short a b hm =>
    obtain ⟨hb, h1, h2⟩ := absHeapOps_byte hm
    exact ⟨b, [], rfl, by omega, h2, by simp [hb]⟩

theorem valType_parses : Parses valType ValTypeB := by
  constructor
  · intro bs t v n h
    cases bs with
    | nil => simp [valType] at h
    | cons b bs =>
      simp only [valType, List.length_cons, land_pack_cons, shiftRight_pack_cons] at h
      split at h
      · rename_i t' ht
        simp only [Res.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[b], bs, rfl, by simpa [ValTypeB] using numTypeOf_some ht, rfl, rfl⟩
      · simp only [Bool.cond_eq_ite] at h
        split at h
        · simp at h
        · split at h
          · obtain ⟨t, imm, rest, hbs, hR, rfl, rfl, rfl⟩ :=
              refType_parses.map_sound (bs := b :: bs) (by simpa using h)
            exact ⟨imm, rest, hbs, hR, rfl, rfl⟩
          · simp at h
  · intro t pre rest h
    cases t with
    | num t =>
      obtain ⟨b, rfl, ht, -⟩ := numTypeB_byte h
      simp only [valType, List.cons_append, List.nil_append, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, ht]
    | ref t =>
      have h' : RefTypeB t pre := h
      obtain ⟨b, pre', rfl, h1, h2, hs⟩ := refTypeB_head h'
      have hc := refType_parses.complete rest h'
      simp only [List.cons_append, List.length_cons] at hc
      have hstart : (Nat.beq b.toNat 0x63 || Nat.beq b.toNat 0x64 || (absHeapOf b.toNat).isSome ||
          (absHeapExcluded b.toNat).isSome) = true := by
        simp only [Bool.or_eq_true] at hs ⊢
        rcases hs with (h | h) | h <;> simp [h]
      simp only [valType, List.cons_append, List.length_cons, land_pack_cons,
        numTypeOf_none (show b.toNat < 0x7C ∨ 0x7F < b.toNat by omega),
        beq_false.2 (show b.toNat ≠ 0x7B by omega), Bool.cond_false, hstart, Bool.cond_true]
      rw [hc, Res.bind_ok]

theorem valTypeStart_false {k : Nat} (h : k < 0x63 ∨ 0x7F < k) : valTypeStart k = false := by
  simp only [valTypeStart, numTypeOf_none (show k < 0x7C ∨ 0x7F < k by omega),
    absHeapOf_none (show k < 0x69 ∨ 0x70 < k by omega),
    absHeapExcluded_none (show k < 0x6A ∨ 0x74 < k by omega), Option.isSome_none,
    Bool.or_false, Bool.false_or, Bool.or_eq_false_iff, beq_false]
  omega

/-- The first byte of a value type starts one (`valTypeStart`) and is not `0x40`. -/
theorem valTypeB_head {t : ValType} {bs : List UInt8} (h : ValTypeB t bs) :
    ∃ b rest, bs = b :: rest ∧ valTypeStart b.toNat = true ∧ b.toNat ≠ 0x40 := by
  cases t with
  | num t =>
    obtain ⟨b, rfl, ht, h1, h2⟩ := numTypeB_byte h
    exact ⟨b, [], rfl, by simp [valTypeStart, ht], by omega⟩
  | ref t =>
    obtain ⟨b, rest, rfl, h1, h2, hs⟩ := refTypeB_head (show RefTypeB t bs from h)
    refine ⟨b, rest, rfl, ?_, by omega⟩
    simp only [Bool.or_eq_true] at hs
    simp only [valTypeStart, Bool.or_eq_true]
    rcases hs with (h | h) | h <;> simp [h]

theorem ValTypeB.ne_nil {t : ValType} {bs : List UInt8} (h : ValTypeB t bs) : bs ≠ [] := by
  obtain ⟨b, rest, rfl, -⟩ := valTypeB_head h; simp

theorem blockType_parses : Parses blockType BlockTypeB := by
  constructor
  · intro bs bt v n h
    cases bs with
    | nil => simp [blockType] at h
    | cons b bs =>
      simp only [blockType, List.length_cons, land_pack_cons, shiftRight_pack_cons] at h
      cases h1 : Nat.beq b.toNat 0x40
      · simp only [h1, Bool.cond_false] at h
        cases h2 : valTypeStart b.toNat
        · simp only [h2, Bool.cond_false] at h
          obtain ⟨x, v', n', hs, hk⟩ := Res.bind_eq_ok.1 h
          cases hx : Nat.blt x (2 ^ 32)
          · simp [hx] at hk
          · simp only [hx, Bool.cond_true, Res.ok.injEq] at hk
            obtain ⟨rfl, rfl, rfl⟩ := hk
            obtain ⟨pre, rest, hpre, hS, rfl, rfl⟩ :=
              s33_sound (bs := b :: bs) (by simpa using hs) hx
            exact ⟨pre, rest, hpre, hS, rfl, rfl⟩
        · simp only [h2, Bool.cond_true] at h
          obtain ⟨t, imm, rest, hbs, hR, rfl, rfl, rfl⟩ :=
            valType_parses.map_sound (bs := b :: bs) (by simpa using h)
          exact ⟨imm, rest, hbs, hR, rfl, rfl⟩
      · simp only [h1, Bool.cond_true, Res.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain rfl : b = 0x40 := UInt8.toNat_inj.1 (beq_true.1 h1)
        exact ⟨[0x40], bs, rfl, rfl, rfl, rfl⟩
  · intro bt pre rest h
    cases bt with
    | empty =>
      simp only [BlockTypeB] at h; subst h
      simp only [blockType, List.cons_append, List.nil_append, List.length_cons,
        land_pack_cons, shiftRight_pack_cons]; rfl
    | val t =>
      have h' : ValTypeB t pre := h
      obtain ⟨b, pre', rfl, hs, h40⟩ := valTypeB_head h'
      have hc := valType_parses.complete rest h'
      simp only [List.cons_append, List.length_cons] at hc
      simp only [blockType, List.cons_append, List.length_cons, land_pack_cons,
        beq_false.2 h40, hs, Bool.cond_false, Bool.cond_true]
      rw [hc, Res.bind_ok]
    | idx x =>
      have h' : SLeb 33 (x : Int) pre := h
      cases pre with
      | nil => exact absurd rfl h'.ne_nil
      | cons b pre =>
        have hb := s33_head h'
        obtain ⟨hs, hx⟩ := s33_complete h' rest
        simp only [List.cons_append, List.length_cons] at hs
        simp only [blockType, List.cons_append, List.length_cons, land_pack_cons,
          beq_false.2 (show b.toNat ≠ 0x40 by omega),
          valTypeStart_false (show b.toNat < 0x63 ∨ 0x7F < b.toNat by omega), Bool.cond_false]
        rw [hs, Res.bind_ok, hx]; rfl

theorem memIdx0_parses : Parses memIdx0 (fun _ bs => ULeb 32 0 bs) := by
  constructor
  · intro bs u v n h
    obtain ⟨x, v', n', hx, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨pre, rest, rfl, hu, rfl, rfl⟩ := u32_parses.sound hx
    cases h0 : Nat.beq x 0
    · simp [h0] at hk
    · simp only [h0, Bool.cond_true, Res.ok.injEq] at hk
      obtain ⟨-, rfl, rfl⟩ := hk
      obtain rfl : x = 0 := beq_true.1 h0
      exact ⟨pre, rest, rfl, hu, rfl, rfl⟩
  · intro u pre rest h
    simp only [memIdx0]
    rw [u32_parses.complete rest h, Res.bind_ok]; rfl

theorem memArg_parses : Parses memArg MemArgB := by
  constructor
  · intro bs m v n h
    obtain ⟨f, v₁, n₁, hf, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b₁, r₁, rfl, hu, rfl, rfl⟩ := u32_parses.sound hf
    cases h1 : Nat.blt f 64
    · simp only [h1, Bool.cond_false] at hk
      cases h2 : Nat.blt f 128
      · simp [h2] at hk
      · simp only [h2, Bool.cond_true] at hk
        obtain ⟨_, v₂, n₂, h₂, hk⟩ := Res.bind_eq_ok.1 hk
        obtain ⟨b₀, r₂, rfl, h0, rfl, rfl⟩ := memIdx0_parses.sound h₂
        obtain ⟨o, b₂, rest, rfl, ho, rfl, rfl, rfl⟩ := u64_parses.map_sound hk
        have := blt_false.1 h1
        have := blt_true.1 h2
        refine ⟨b₁ ++ b₀ ++ b₂, rest, by simp, ⟨by simp; omega,
          .inr ⟨b₁, b₀, b₂, ?_, h0, ho, rfl⟩⟩, rfl, rfl⟩
        simpa [show f - 64 + 2 ^ 6 = f by omega] using hu
    · simp only [h1, Bool.cond_true] at hk
      obtain ⟨o, b₂, rest, rfl, ho, rfl, rfl, rfl⟩ := u64_parses.map_sound hk
      exact ⟨b₁ ++ b₂, rest, by simp, ⟨by simpa using blt_true.1 h1,
        .inl ⟨b₁, b₂, hu, ho, rfl⟩⟩, rfl, rfl⟩
  · rintro m pre rest ⟨ha, ⟨b₁, b₂, hu, ho, rfl⟩ | ⟨b₁, b₀, b₂, hu, h0, ho, rfl⟩⟩
    · simp only [memArg, List.append_assoc]
      rw [u32_parses.complete _ hu, Res.bind_ok, blt_true.2 ha, Bool.cond_true,
        u64_parses.complete rest ho, Res.bind_ok]
    · simp only [memArg, List.append_assoc]
      rw [u32_parses.complete _ hu, Res.bind_ok, blt_false.2 (by omega), Bool.cond_false,
        blt_true.2 (by omega), Bool.cond_true, memIdx0_parses.complete (a := ()) _ h0, Res.bind_ok,
        u64_parses.complete rest ho, Res.bind_ok]
      simp

theorem catchClause_parses : Parses catchClause CatchB := by
  constructor
  · intro bs c v n h
    obtain ⟨_, v', n', hb, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, rest, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hb
    simp only [Bool.cond_eq_ite, Nat.beq_eq] at hk
    split at hk
    · rename_i hb0
      obtain ⟨x, v₂, n₂, h₂, h₃⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨b₁, r₁, rfl, hx, rfl, rfl⟩ := u32_parses.sound h₂
      obtain ⟨l, b₂, r, rfl, hl, rfl, rfl, rfl⟩ := u32_parses.map_sound h₃
      obtain rfl : b = 0 := UInt8.toNat_inj.1 hb0
      exact ⟨0 :: (b₁ ++ b₂), r, by simp, ⟨b₁, b₂, hx, hl, rfl⟩, rfl, rfl⟩
    · split at hk
      · rename_i _ hb1
        obtain ⟨x, v₂, n₂, h₂, h₃⟩ := Res.bind_eq_ok.1 hk
        obtain ⟨b₁, r₁, rfl, hx, rfl, rfl⟩ := u32_parses.sound h₂
        obtain ⟨l, b₂, r, rfl, hl, rfl, rfl, rfl⟩ := u32_parses.map_sound h₃
        obtain rfl : b = 1 := UInt8.toNat_inj.1 hb1
        exact ⟨1 :: (b₁ ++ b₂), r, by simp, ⟨b₁, b₂, hx, hl, rfl⟩, rfl, rfl⟩
      · split at hk
        · rename_i _ _ hb2
          obtain ⟨l, b₂, r, rfl, hl, rfl, rfl, rfl⟩ := u32_parses.map_sound hk
          obtain rfl : b = 2 := UInt8.toNat_inj.1 hb2
          exact ⟨2 :: b₂, r, rfl, ⟨b₂, hl, rfl⟩, rfl, rfl⟩
        · split at hk
          · rename_i _ _ _ hb3
            obtain ⟨l, b₂, r, rfl, hl, rfl, rfl, rfl⟩ := u32_parses.map_sound hk
            obtain rfl : b = 3 := UInt8.toNat_inj.1 hb3
            exact ⟨3 :: b₂, r, rfl, ⟨b₂, hl, rfl⟩, rfl, rfl⟩
          · simp at hk
  · intro c pre rest h
    cases c with
    | tag x l =>
      obtain ⟨b₁, b₂, hx, hl, rfl⟩ := h
      simp only [catchClause, List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok, List.append_assoc,
        show Nat.beq (UInt8.toNat 0) 0 = true from rfl, Bool.cond_true]
      rw [u32_parses.complete _ hx, Res.bind_ok, u32_parses.complete _ hl, Res.bind_ok]
    | tagRef x l =>
      obtain ⟨b₁, b₂, hx, hl, rfl⟩ := h
      simp only [catchClause, List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok, List.append_assoc,
        show Nat.beq (UInt8.toNat 1) 0 = false from rfl,
        show Nat.beq (UInt8.toNat 1) 1 = true from rfl, Bool.cond_false, Bool.cond_true]
      rw [u32_parses.complete _ hx, Res.bind_ok, u32_parses.complete _ hl, Res.bind_ok]
    | all l =>
      obtain ⟨b₂, hl, rfl⟩ := h
      simp only [catchClause, List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok,
        show Nat.beq (UInt8.toNat 2) 0 = false from rfl,
        show Nat.beq (UInt8.toNat 2) 1 = false from rfl,
        show Nat.beq (UInt8.toNat 2) 2 = true from rfl, Bool.cond_false, Bool.cond_true]
      rw [u32_parses.complete _ hl, Res.bind_ok]
    | allRef l =>
      obtain ⟨b₂, hl, rfl⟩ := h
      simp only [catchClause, List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok,
        show Nat.beq (UInt8.toNat 3) 0 = false from rfl,
        show Nat.beq (UInt8.toNat 3) 1 = false from rfl,
        show Nat.beq (UInt8.toNat 3) 2 = false from rfl,
        show Nat.beq (UInt8.toNat 3) 3 = true from rfl, Bool.cond_false, Bool.cond_true]
      rw [u32_parses.complete _ hl, Res.bind_ok]

theorem CatchB.ne_nil {c : Catch} {bs : List UInt8} (h : CatchB c bs) : bs ≠ [] := by
  cases c <;> obtain ⟨_, _, _⟩ := h <;> simp_all

/-! ## Opcode tables

Each decoder family, listed by opcode, equals the corresponding slice of the spec table; the
kernel checks the agreement by evaluation (`rfl`). -/

/-- The decoder's load/store lookup, as `instr` performs it. -/
def memOpAt (op : Nat) : Option (MemArg → Instr) :=
  bif Nat.blt op 0x36 then nth loadOps (op - 0x28) else nth storeOps (op - 0x36)

theorem numOp_table : (List.range 128).map (fun k => (UInt8.ofNat (0x45 + k), numOp (0x45 + k))) =
    (plainOps.drop 8).map (fun p => (p.1, some p.2)) := by rfl

theorem memOp_table : (List.range 23).map (fun k => (UInt8.ofNat (0x28 + k), memOpAt (0x28 + k))) =
    memOps.map (fun p => (p.1, some p.2)) := by rfl

theorem varOp_table :
    (List.range 7).map (fun k => (UInt8.ofNat (0x20 + k), nth varOps (0x20 + k - 0x20))) =
    (idxOps.drop 10).map (fun p => (p.1, some p.2)) := by rfl

theorem plainOps_eq : plainOps = [(0x00, .unreachable), (0x01, .nop), (0x0A, .throwRef),
    (0x0F, .return_), (0x1A, .drop), (0x1B, .select none), (0xD1, .refIsNull),
    (0xD4, .refAsNonNull)] ++ plainOps.drop 8 := rfl

theorem idxOps_eq : idxOps = [(0x08, .throw), (0x0C, .br), (0x0D, .brIf), (0x10, .call),
    (0x12, .returnCall), (0x14, .callRef), (0x15, .returnCallRef), (0xD2, .refFunc),
    (0xD5, .brOnNull), (0xD6, .brOnNonNull)] ++ idxOps.drop 10 := rfl

/-- A table entry found by the decoder's lookup is in the spec table. -/
theorem mem_of_table {α : Type} {base len : Nat} {f : Nat → Option α} {tbl : List (UInt8 × α)}
    (ht : (List.range len).map (fun k => (UInt8.ofNat (base + k), f (base + k))) =
      tbl.map (fun p => (p.1, some p.2)))
    {op : Nat} (h₁ : base ≤ op) (h₂ : op < base + len) {a : α} (hf : f op = some a) :
    (UInt8.ofNat op, a) ∈ tbl := by
  have : (UInt8.ofNat op, some a) ∈ tbl.map (fun p => (p.1, some p.2)) := by
    rw [← ht, List.mem_map]
    exact ⟨op - base, List.mem_range.2 (by omega), by rw [Nat.add_sub_cancel' h₁, hf]⟩
  obtain ⟨⟨o, a'⟩, hm, he⟩ := List.mem_map.1 this
  simp only [Prod.mk.injEq, Option.some.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hm

/-- A spec table entry is what the decoder's lookup finds at its opcode. -/
theorem table_of_mem {α : Type} {base len : Nat} {f : Nat → Option α} {tbl : List (UInt8 × α)}
    (ht : (List.range len).map (fun k => (UInt8.ofNat (base + k), f (base + k))) =
      tbl.map (fun p => (p.1, some p.2)))
    (hlen : base + len ≤ 256) {op : UInt8} {a : α} (hm : (op, a) ∈ tbl) :
    base ≤ op.toNat ∧ op.toNat < base + len ∧ f op.toNat = some a := by
  have : (op, some a) ∈ (List.range len).map (fun k => (UInt8.ofNat (base + k), f (base + k))) := by
    rw [ht]; exact List.mem_map.2 ⟨(op, a), hm, rfl⟩
  obtain ⟨k, hk, he⟩ := List.mem_map.1 this
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, hf⟩ := he
  have hk := List.mem_range.1 hk
  have hv : (UInt8.ofNat (base + k)).toNat = base + k := by
    exact UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)
  rw [hv]
  exact ⟨by omega, by omega, hf⟩

/-! ## Non-structured instructions: soundness -/

/-- `instr` with opcode `op` decoded `i` from a prefix `imm` of `bs`: `op :: imm` encodes `i`. -/
def InstrOk (op : UInt8) (i : Instr) (bs : List UInt8) (v n : Nat) : Prop :=
  ∃ imm rest, bs = imm ++ rest ∧ InstrB i (op :: imm) ∧ v = pack rest ∧ n = rest.length

theorem withIdx_parses (mk : Nat → Instr) :
    Parses (withIdx mk) (fun i bs => ∃ x, i = mk x ∧ ULeb 32 x bs) :=
  (u32_parses.bind fun x => pure_parses (mk x)).congr fun i bs => by
    constructor
    · rintro ⟨x, b₁, _, hu, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨x, rfl, by simpa using hu⟩
    · rintro ⟨x, rfl, hu⟩
      exact ⟨x, bs, [], hu, ⟨rfl, rfl⟩, by simp⟩

theorem sound_plain {op : UInt8} {i₀ i : Instr} {bs : List UInt8} {v n : Nat}
    (hm : (op, i₀) ∈ plainOps) (h : Res.ok i₀ (pack bs) bs.length = .ok i v n) :
    InstrOk op i bs v n := by
  simp only [Res.ok.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨[], bs, rfl, .plain hm, rfl, rfl⟩

theorem sound_idx {op : UInt8} {mk : Nat → Instr} {i : Instr} {bs : List UInt8} {v n : Nat}
    (hm : (op, mk) ∈ idxOps) (h : withIdx mk (pack bs) bs.length = .ok i v n) :
    InstrOk op i bs v n := by
  obtain ⟨imm, rest, rfl, ⟨x, rfl, hu⟩, rfl, rfl⟩ := (withIdx_parses mk).sound h
  exact ⟨imm, rest, rfl, .idx hm hu, rfl, rfl⟩

theorem ULeb.ne_nil {N x : Nat} {bs : List UInt8} (h : ULeb N x bs) : bs ≠ [] := by
  cases h <;> simp

theorem sound_brTable {bs : List UInt8} {i : Instr} {v n : Nat}
    (h : ((vec u32 (pack bs) bs.length).bind fun ls v n =>
      (u32 v n).bind fun l v n => .ok (Instr.brTable ls l) v n) = .ok i v n) :
    InstrOk 0x0E i bs v n := by
  obtain ⟨ls, v', n', h₁, h₂⟩ := Res.bind_eq_ok.1 h
  obtain ⟨b₁, rest₁, rfl, hv, rfl, rfl⟩ :=
    (vec_parses u32_parses fun _ _ h => ULeb.ne_nil h).sound h₁
  obtain ⟨l, b₂, rest, rfl, hl, rfl, rfl, rfl⟩ := u32_parses.map_sound h₂
  exact ⟨b₁ ++ b₂, rest, by simp, by simpa using InstrB.brTable hv hl, rfl, rfl⟩

theorem sound_callIndirect {bs : List UInt8} {i : Instr} {v n : Nat}
    (h : ((u32 (pack bs) bs.length).bind fun y v n =>
      (u32 v n).bind fun x v n => .ok (Instr.callIndirect x y) v n) = .ok i v n) :
    InstrOk 0x11 i bs v n := by
  obtain ⟨y, v', n', h₁, h₂⟩ := Res.bind_eq_ok.1 h
  obtain ⟨b₁, rest₁, rfl, hy, rfl, rfl⟩ := u32_parses.sound h₁
  obtain ⟨x, b₂, rest, rfl, hx, rfl, rfl, rfl⟩ := u32_parses.map_sound h₂
  exact ⟨b₁ ++ b₂, rest, by simp, by simpa using InstrB.callIndirect hy hx, rfl, rfl⟩

theorem sound_returnCallIndirect {bs : List UInt8} {i : Instr} {v n : Nat}
    (h : ((u32 (pack bs) bs.length).bind fun y v n =>
      (u32 v n).bind fun x v n => .ok (Instr.returnCallIndirect x y) v n) = .ok i v n) :
    InstrOk 0x13 i bs v n := by
  obtain ⟨y, v', n', h₁, h₂⟩ := Res.bind_eq_ok.1 h
  obtain ⟨b₁, rest₁, rfl, hy, rfl, rfl⟩ := u32_parses.sound h₁
  obtain ⟨x, b₂, rest, rfl, hx, rfl, rfl, rfl⟩ := u32_parses.map_sound h₂
  exact ⟨b₁ ++ b₂, rest, by simp, by simpa using InstrB.returnCallIndirect hy hx, rfl, rfl⟩

theorem sound_selectT {bs : List UInt8} {i : Instr} {v n : Nat}
    (h : ((vec valType (pack bs) bs.length).bind fun ts v n =>
      .ok (Instr.select (some ts)) v n) = .ok i v n) : InstrOk 0x1C i bs v n := by
  obtain ⟨ts, imm, rest, rfl, hv, rfl, rfl, rfl⟩ :=
    (vec_parses valType_parses fun _ _ h => ValTypeB.ne_nil h).map_sound h
  exact ⟨imm, rest, rfl, .selectT hv, rfl, rfl⟩

theorem lowInstr_sound {k : Nat} {bs : List UInt8} {i : Instr} {v n r : Nat} (hk : k < 0x20)
    (h : lowInstr k (pack bs) bs.length r = .ok i v n) : InstrOk (UInt8.ofNat k) i bs v n := by
  simp only [lowInstr, Bool.cond_eq_ite, Nat.blt_eq, Nat.beq_eq, Bool.or_eq_true] at h
  repeat' split at h
  all_goals try subst_vars
  all_goals first
    | (simp at h; done)
    | (refine sound_plain ?_ h; simp [plainOps]; done)
    | (refine sound_idx ?_ h; simp [idxOps]; done)
    | exact sound_callIndirect h
    | exact sound_returnCallIndirect h
    | exact sound_selectT h
    | (obtain rfl : k = 0x0E := by omega
       exact sound_brTable h)
    | (obtain rfl : k = 0x15 := by omega
       refine sound_idx ?_ h; simp [idxOps])

theorem fcInstr_sound {bs : List UInt8} {i : Instr} {v n : Nat}
    (h : fcInstr (pack bs) bs.length = .ok i v n) : InstrOk 0xFC i bs v n := by
  obtain ⟨k, v', n', h₁, hk⟩ := Res.bind_eq_ok.1 h
  obtain ⟨b₁, rest₁, rfl, hu, rfl, rfl⟩ := u32_parses.sound h₁
  simp only [Bool.cond_eq_ite, Nat.blt_eq, Nat.beq_eq] at hk
  repeat' split at hk
  all_goals try subst_vars
  all_goals first
    | (simp only [Res.ok.injEq] at hk
       obtain ⟨rfl, rfl, rfl⟩ := hk
       refine ⟨b₁, rest₁, rfl, .fcPlain ?_ hu, rfl, rfl⟩
       rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | simp [fcPlainOps])
    | skip
  all_goals first
    | (simp at hk; done)
    | (obtain ⟨imm, rest, rfl, ⟨x, rfl, hx⟩, rfl, rfl⟩ := (withIdx_parses _).sound hk
       exact ⟨b₁ ++ imm, rest, by simp, by simpa using InstrB.fcIdx (by simp [fcIdxOps]) hu hx,
         rfl, rfl⟩)
    | (obtain ⟨x, v₂, n₂, h₂, h₃⟩ := Res.bind_eq_ok.1 hk
       obtain ⟨b₂, rest₂, rfl, hx, rfl, rfl⟩ := u32_parses.sound h₂
       obtain ⟨_, b₃, rest, rfl, h0, rfl, rfl, rfl⟩ := memIdx0_parses.map_sound h₃
       exact ⟨b₁ ++ b₂ ++ b₃, rest, by simp, by simpa using InstrB.memoryInit hu hx h0, rfl,
         rfl⟩)
    | (obtain ⟨_, v₂, n₂, h₂, h₃⟩ := Res.bind_eq_ok.1 hk
       obtain ⟨b₂, rest₂, rfl, h0, rfl, rfl⟩ := memIdx0_parses.sound h₂
       obtain ⟨_, b₃, rest, rfl, h1, rfl, rfl, rfl⟩ := memIdx0_parses.map_sound h₃
       exact ⟨b₁ ++ b₂ ++ b₃, rest, by simp, by simpa using InstrB.memoryCopy hu h0 h1, rfl, rfl⟩)
    | (obtain ⟨_, b₂, rest, rfl, h0, rfl, rfl, rfl⟩ := memIdx0_parses.map_sound hk
       exact ⟨b₁ ++ b₂, rest, by simp, by simpa using InstrB.memoryFill hu h0, rfl, rfl⟩)
    | (obtain ⟨y, v₂, n₂, h₂, h₃⟩ := Res.bind_eq_ok.1 hk
       obtain ⟨b₂, rest₂, rfl, hy, rfl, rfl⟩ := u32_parses.sound h₂
       obtain ⟨x, b₃, rest, rfl, hx, rfl, rfl, rfl⟩ := u32_parses.map_sound h₃
       first
         | exact ⟨b₁ ++ b₂ ++ b₃, rest, by simp, by simpa using InstrB.tableInit hu hy hx,
             rfl, rfl⟩
         | exact ⟨b₁ ++ b₂ ++ b₃, rest, by simp, by simpa using InstrB.tableCopy hu hy hx,
             rfl, rfl⟩)

@[simp] theorem leBytes_length (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem pack_leBytes {k n : Nat} (h : n < 256 ^ k) : pack (leBytes k n) = n := by
  induction k generalizing n with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    simp only [leBytes, pack_cons, Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]
    rw [ih (by rw [Nat.pow_succ] at h; omega)]
    omega

theorem floatBits_pack {w : Width} {imm : List UInt8}
    (hl : imm.length = match w with | .w32 => 4 | .w64 => 8) : FloatBits w (pack imm) imm := by
  have h := pack_lt imm
  have h2 := leBytes_pack imm
  rw [hl] at h h2
  cases w <;> exact ⟨by rw [two_pow_eight_mul]; exact h, h2.symm⟩

theorem nth_some_lt {α : Type} {xs : List α} {k : Nat} {a : α} (h : nth xs k = some a) :
    k < xs.length := by
  induction xs generalizing k with
  | nil => simp [nth] at h
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simp only [nth] at h; simpa using ih h

theorem highInstr_sound {k : Nat} {bs : List UInt8} {i : Instr} {v n r : Nat}
    (h : highInstr k (pack bs) bs.length r = .ok i v n) : InstrOk (UInt8.ofNat k) i bs v n := by
  simp only [highInstr, Bool.cond_eq_ite, Nat.beq_eq] at h
  repeat' split at h
  all_goals try subst_vars
  all_goals first
    | (simp at h; done)
    | (refine sound_plain ?_ h; simp [plainOps]; done)
    | (refine sound_idx ?_ h; simp [idxOps]; done)
    | exact fcInstr_sound h
    | (obtain ⟨t, imm, rest, rfl, ht, rfl, rfl, rfl⟩ := heapType_parses.map_sound h
       exact ⟨imm, rest, rfl, .refNull ht, rfl, rfl⟩)

theorem instr_sound_nat {k : Nat} {bs : List UInt8} {i : Instr} {v n r : Nat} (hk : k < 256)
    (h : instr k (pack bs) bs.length r = .ok i v n) : InstrOk (UInt8.ofNat k) i bs v n := by
  unfold instr at h
  cases h₁ : Nat.blt k 0x45
  · simp only [h₁, Bool.cond_false] at h
    cases h₂ : Nat.blt k 0xC5
    · simp only [h₂, Bool.cond_false] at h
      exact highInstr_sound h
    · simp only [h₂, Bool.cond_true] at h
      split at h
      · rename_i i₀ hi
        exact sound_plain (List.mem_of_mem_drop
          (mem_of_table numOp_table (blt_false.1 h₁) (blt_true.1 h₂) hi)) h
      · simp at h
  · simp only [h₁, Bool.cond_true] at h
    cases h₂ : Nat.blt k 0x20
    · simp only [h₂, Bool.cond_false] at h
      cases h₃ : Nat.blt k 0x28
      · simp only [h₃, Bool.cond_false] at h
        cases h₄ : Nat.blt k 0x3F
        · simp only [h₄, Bool.cond_false] at h
          have := blt_false.1 h₄
          have := blt_true.1 h₁
          simp only [Bool.cond_eq_ite, Nat.beq_eq] at h
          repeat' split at h
          all_goals try subst_vars
          all_goals first
            | (obtain ⟨_, imm, rest, rfl, h0, rfl, rfl, rfl⟩ := memIdx0_parses.map_sound h
               first
                 | exact ⟨imm, rest, rfl, .memorySize h0, rfl, rfl⟩
                 | exact ⟨imm, rest, rfl, .memoryGrow h0, rfl, rfl⟩)
            | (obtain ⟨_, imm, rest, rfl, ⟨i', hi, rfl, -⟩, rfl, rfl, rfl⟩ :=
                 (sleb_parses _ _).map_sound h
               first
                 | exact ⟨imm, rest, rfl, .i32Const hi, rfl, rfl⟩
                 | exact ⟨imm, rest, rfl, .i64Const hi, rfl, rfl⟩)
            | (obtain ⟨_, imm, rest, rfl, ⟨hl, rfl⟩, rfl, rfl, rfl⟩ := (leNat_parses _).map_sound h
               first
                 | exact ⟨imm, rest, rfl, .f32Const (floatBits_pack (w := .w32) hl), rfl, rfl⟩
                 | (obtain rfl : k = 0x44 := by omega
                    exact ⟨imm, rest, rfl, .f64Const (floatBits_pack (w := .w64) hl), rfl, rfl⟩))
        · simp only [h₄, Bool.cond_true] at h
          split at h
          · rename_i mk hmk
            obtain ⟨m, imm, rest, rfl, hm, rfl, rfl, rfl⟩ := memArg_parses.map_sound h
            have hlt : k < 0x28 + 23 := by
              cases h5 : Nat.blt k 0x36 <;> simp only [h5, Bool.cond_true, Bool.cond_false] at hmk
              · have := nth_some_lt hmk; simp [storeOps] at this; omega
              · exact (by have := blt_true.1 h5; omega)
            exact ⟨imm, rest, rfl, .mem (mem_of_table memOp_table (blt_false.1 h₃) hlt
              (show memOpAt k = some mk from hmk)) hm, rfl, rfl⟩
          · simp at h
      · simp only [h₃, Bool.cond_true] at h
        split at h
        · rename_i mk hmk
          have hlt : k < 0x20 + 7 := by have := nth_some_lt hmk; simp [varOps] at this; omega
          exact sound_idx (List.mem_of_mem_drop (mem_of_table
            (f := fun x => nth varOps (x - 0x20)) varOp_table (blt_false.1 h₂) hlt hmk)) h
        · simp at h
    · simp only [h₂, Bool.cond_true] at h
      exact lowInstr_sound (blt_true.1 h₂) h

theorem instr_sound {op : UInt8} {bs : List UInt8} {i : Instr} {v n r : Nat}
    (h : instr op.toNat (pack bs) bs.length r = .ok i v n) : InstrOk op i bs v n := by
  have := instr_sound_nat op.toNat_lt h
  rwa [UInt8.ofNat_toNat] at this

/-! ## Non-structured instructions: completeness -/

theorem instr_num {op v n r : Nat} (h₁ : 0x45 ≤ op) (h₂ : op < 0xC5) :
    instr op v n r = match numOp op with
      | some i => .ok i v n
      | none => .bad r "illegal opcode" := by
  unfold instr
  simp only [blt_false.2 h₁, blt_true.2 h₂, Bool.cond_true, Bool.cond_false]
  rfl

theorem instr_var {op v n r : Nat} (h₁ : 0x20 ≤ op) (h₂ : op < 0x28) :
    instr op v n r = match nth varOps (op - 0x20) with
      | some mk => withIdx mk v n
      | none => .bad r "illegal opcode" := by
  unfold instr
  simp only [blt_true.2 (show op < 0x45 by omega), blt_false.2 h₁, blt_true.2 h₂,
    Bool.cond_true, Bool.cond_false]
  rfl

theorem instr_mem {op v n r : Nat} (h₁ : 0x28 ≤ op) (h₂ : op < 0x3F) :
    instr op v n r = match memOpAt op with
      | some mk => (memArg v n).bind fun m v n => .ok (mk m) v n
      | none => .bad r "illegal opcode" := by
  unfold instr
  simp only [blt_true.2 (show op < 0x45 by omega), blt_false.2 (show 0x20 ≤ op by omega),
    blt_false.2 h₁, blt_true.2 h₂, Bool.cond_true, Bool.cond_false]
  rfl

/-- Completeness of a decoder step given by an equation for `instr` at the opcode. -/
theorem complete_of_eq {op : Nat} {p : Nat → Nat → Res Instr} {R : Instr → List UInt8 → Prop}
    (heq : ∀ v n r, instr op v n r = p v n) (hp : Parses p R) {i : Instr} {imm : List UInt8}
    (hR : R i imm) (rest : List UInt8) (r : Nat) :
    instr op (pack (imm ++ rest)) (imm ++ rest).length r = .ok i (pack rest) rest.length := by
  rw [heq]; exact hp.complete rest hR

/-- The opcode and immediates of a non-structured instruction, decodable by `instr`. -/
def InstrDec (i : Instr) (bs : List UInt8) : Prop :=
  ∃ op imm, bs = op :: imm ∧ (op.toNat < 2 ∨ 5 < op.toNat ∧ op.toNat ≠ 0x0B ∧ op.toNat ≠ 0x1F) ∧
    ∀ rest r, instr op.toNat (pack (imm ++ rest)) (imm ++ rest).length r =
      .ok i (pack rest) rest.length

theorem dec_plain {i : Instr} {op : UInt8} (hm : (op, i) ∈ plainOps) :
    InstrDec i [op] := by
  refine ⟨_, [], rfl, ?_⟩
  rw [plainOps_eq, List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, fun _ _ => rfl⟩
  · obtain ⟨h₁, h₂, hf⟩ := table_of_mem numOp_table (by decide) (List.mem_of_mem_drop hm)
    refine ⟨by omega, fun rest r => ?_⟩
    rw [instr_num h₁ h₂, hf]; rfl

theorem dec_fcPlain {i : Instr} {n : Nat} {b : List UInt8} (hm : (n, i) ∈ fcPlainOps)
    (hn : ULeb 32 n b) :
    InstrDec i (0xFC :: b) := by
  refine ⟨0xFC, _, rfl, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr]
  rw [u32_parses.complete rest hn, Res.bind_ok]
  simp only [fcPlainOps, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem dec_mem {mk : MemArg → Instr} {op : UInt8} {m : MemArg} {b : List UInt8}
    (hm : (op, mk) ∈ memOps)
    (hma : MemArgB m b) :
    InstrDec (mk m) (op :: b) := by
  obtain ⟨h₁, h₂, hf⟩ := table_of_mem memOp_table (by decide) hm
  refine ⟨_, _, rfl, by omega, fun rest r => ?_⟩
  rw [instr_mem h₁ (by omega), hf]
  exact (memArg_parses.bind fun m => pure_parses (mk m)).complete rest
    ⟨_, _, [], hma, ⟨rfl, rfl⟩, by simp⟩

theorem dec_idx {mk : Nat → Instr} {op : UInt8} {x : Nat} {b : List UInt8} (hm : (op, mk) ∈ idxOps)
    (hx : ULeb 32 x b) :
    InstrDec (mk x) (op :: b) := by
  rw [idxOps_eq, List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨_, _, rfl, by decide, fun rest r => (withIdx_parses _).complete rest ⟨_, rfl, hx⟩⟩
  · obtain ⟨h₁, h₂, hf⟩ := table_of_mem (f := fun x => nth varOps (x - 0x20)) varOp_table
      (by decide) hm
    refine ⟨_, _, rfl, by omega, fun rest r => ?_⟩
    rw [instr_var h₁ (by omega), show nth varOps (op.toNat - 0x20) = some mk from hf]
    exact (withIdx_parses _).complete rest ⟨_, rfl, hx⟩

theorem dec_fcIdx {mk : Nat → Instr} {n x : Nat} {b₁ b₂ : List UInt8} (hm : (n, mk) ∈ fcIdxOps)
    (hn : ULeb 32 n b₁) (hx : ULeb 32 x b₂) :
    InstrDec (mk x) (0xFC :: b₁ ++ b₂) := by
  refine ⟨0xFC, _, rfl, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr, List.append_eq, List.append_assoc]
  rw [u32_parses.complete _ hn, Res.bind_ok]
  simp only [fcIdxOps, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact (withIdx_parses _).complete rest ⟨_, rfl, hx⟩

theorem dec_brTable {ls : List Nat} {l : Nat} {b₁ b₂ : List UInt8} (hs : Vec (ULeb 32) ls b₁)
    (hl : ULeb 32 l b₂) :
    InstrDec (.brTable ls l) ([0x0E] ++ b₁ ++ b₂) := by
  refine ⟨0x0E, b₁ ++ b₂, by simp, by decide, fun rest r => ?_⟩
  show ((vec u32 _ _).bind fun ls v n =>
    (u32 v n).bind fun l v n => .ok (Instr.brTable ls l) v n) = _
  have := ((vec_parses u32_parses fun _ _ h => ULeb.ne_nil h).bind fun ls =>
    u32_parses.bind fun l => pure_parses (Instr.brTable ls l)).complete rest
    ⟨ls, b₁, b₂, hs, ⟨l, b₂, [], hl, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_callIndirect {x y : Nat} {b₁ b₂ : List UInt8} (hy : ULeb 32 y b₁) (hx : ULeb 32 x b₂) :
    InstrDec (.callIndirect x y) ([0x11] ++ b₁ ++ b₂) := by
  refine ⟨0x11, b₁ ++ b₂, by simp, by decide, fun rest r => ?_⟩
  show ((u32 _ _).bind fun y v n =>
    (u32 v n).bind fun x v n => .ok (Instr.callIndirect x y) v n) = _
  have := (u32_parses.bind fun y => u32_parses.bind fun x =>
    pure_parses (Instr.callIndirect x y)).complete
    rest ⟨y, b₁, b₂, hy, ⟨x, b₂, [], hx, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_returnCallIndirect {x y : Nat} {b₁ b₂ : List UInt8} (hy : ULeb 32 y b₁)
    (hx : ULeb 32 x b₂) : InstrDec (.returnCallIndirect x y) ([0x13] ++ b₁ ++ b₂) := by
  refine ⟨0x13, b₁ ++ b₂, by simp, by decide, fun rest r => ?_⟩
  show ((u32 _ _).bind fun y v n =>
    (u32 v n).bind fun x v n => .ok (Instr.returnCallIndirect x y) v n) = _
  have := (u32_parses.bind fun y => u32_parses.bind fun x =>
    pure_parses (Instr.returnCallIndirect x y)).complete
    rest ⟨y, b₁, b₂, hy, ⟨x, b₂, [], hx, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_selectT {ts : List ValType} {b : List UInt8} (h : Vec ValTypeB ts b) :
    InstrDec (.select (some ts)) (0x1C :: b) := by
  refine ⟨0x1C, _, rfl, by decide, fun rest r => ?_⟩
  show ((vec valType _ _).bind fun ts v n => .ok (Instr.select (some ts)) v n) = _
  exact ((vec_parses valType_parses fun _ _ h => ValTypeB.ne_nil h).bind fun ts =>
    pure_parses (Instr.select (some ts))).complete rest ⟨_, _, [], h, ⟨rfl, rfl⟩, by simp⟩

theorem dec_refNull {ht : HeapType} {b : List UInt8} (h : HeapTypeB ht b) :
    InstrDec (.refNull ht) (0xD0 :: b) := by
  refine ⟨0xD0, _, rfl, by decide, fun rest r => ?_⟩
  show ((heapType _ _).bind fun ht v n => .ok (Instr.refNull ht) v n) = _
  exact (heapType_parses.bind fun ht => pure_parses (Instr.refNull ht)).complete rest
    ⟨_, _, [], h, ⟨rfl, rfl⟩, by simp⟩

theorem dec_memorySize {b : List UInt8} (hx : ULeb 32 0 b) :
    InstrDec .memorySize (0x3F :: b) :=
  ⟨0x3F, b, rfl, by decide, fun rest r =>
    (memIdx0_parses.bind fun _ => pure_parses Instr.memorySize).complete rest
      ⟨(), b, [], hx, ⟨rfl, rfl⟩, by simp⟩⟩

theorem dec_memoryGrow {b : List UInt8} (hx : ULeb 32 0 b) :
    InstrDec .memoryGrow (0x40 :: b) :=
  ⟨0x40, b, rfl, by decide, fun rest r =>
    (memIdx0_parses.bind fun _ => pure_parses Instr.memoryGrow).complete rest
      ⟨(), b, [], hx, ⟨rfl, rfl⟩, by simp⟩⟩

theorem dec_memoryInit {y : Nat} {b₁ b₂ b₃ : List UInt8} (hn : ULeb 32 8 b₁) (hy : ULeb 32 y b₂)
    (hx : ULeb 32 0 b₃) :
    InstrDec (.memoryInit y) ([0xFC] ++ b₁ ++ b₂ ++ b₃) := by
  refine ⟨0xFC, b₁ ++ b₂ ++ b₃, by simp, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr, List.append_assoc]
  rw [u32_parses.complete _ hn, Res.bind_ok]
  have := (u32_parses.bind fun y => memIdx0_parses.bind fun _ =>
    pure_parses (Instr.memoryInit y)).complete rest
    ⟨y, b₂, b₃, hy, ⟨(), b₃, [], hx, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_memoryCopy {b b₁ b₂ : List UInt8} (hn : ULeb 32 10 b) (h₁ : ULeb 32 0 b₁)
    (h₂ : ULeb 32 0 b₂) :
    InstrDec .memoryCopy ([0xFC] ++ b ++ b₁ ++ b₂) := by
  refine ⟨0xFC, b ++ b₁ ++ b₂, by simp, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr, List.append_assoc]
  rw [u32_parses.complete _ hn, Res.bind_ok]
  have := (memIdx0_parses.bind fun _ => memIdx0_parses.bind fun _ =>
    pure_parses Instr.memoryCopy).complete rest
    ⟨(), b₁, b₂, h₁, ⟨(), b₂, [], h₂, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_memoryFill {b b₁ : List UInt8} (hn : ULeb 32 11 b) (hx : ULeb 32 0 b₁) :
    InstrDec .memoryFill ([0xFC] ++ b ++ b₁) := by
  refine ⟨0xFC, b ++ b₁, by simp, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr, List.append_assoc]
  rw [u32_parses.complete _ hn, Res.bind_ok]
  have := (memIdx0_parses.bind fun _ => pure_parses Instr.memoryFill).complete (pre := b₁) rest
    ⟨(), b₁, [], hx, ⟨rfl, rfl⟩, by simp⟩
  exact this

theorem dec_tableInit {x y : Nat} {b₁ b₂ b₃ : List UInt8} (hn : ULeb 32 12 b₁) (hy : ULeb 32 y b₂)
    (hx : ULeb 32 x b₃) :
    InstrDec (.tableInit x y) ([0xFC] ++ b₁ ++ b₂ ++ b₃) := by
  refine ⟨0xFC, b₁ ++ b₂ ++ b₃, by simp, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr, List.append_assoc]
  rw [u32_parses.complete _ hn, Res.bind_ok]
  have := (u32_parses.bind fun y => u32_parses.bind fun x =>
    pure_parses (Instr.tableInit x y)).complete rest
    ⟨y, b₂, b₃, hy, ⟨x, b₃, [], hx, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_tableCopy {x y : Nat} {b₁ b₂ b₃ : List UInt8} (hn : ULeb 32 14 b₁) (hx : ULeb 32 x b₂)
    (hy : ULeb 32 y b₃) :
    InstrDec (.tableCopy x y) ([0xFC] ++ b₁ ++ b₂ ++ b₃) := by
  refine ⟨0xFC, b₁ ++ b₂ ++ b₃, by simp, by decide, fun rest r => ?_⟩
  show fcInstr _ _ = _
  simp only [fcInstr, List.append_assoc]
  rw [u32_parses.complete _ hn, Res.bind_ok]
  have := (u32_parses.bind fun x => u32_parses.bind fun y =>
    pure_parses (Instr.tableCopy x y)).complete rest
    ⟨x, b₂, b₃, hx, ⟨y, b₃, [], hy, ⟨rfl, rfl⟩, by simp⟩, rfl⟩
  simp only [List.append_assoc] at this ⊢
  exact this

theorem dec_i32Const {n : Int} {b : List UInt8} (h : SLeb 32 n b) :
    InstrDec (.iconst .w32 (constBits .w32 n)) (0x41 :: b) := by
  refine ⟨0x41, _, rfl, by decide, fun rest r => ?_⟩
  show ((sleb 5 32 _ _).bind fun x v n => .ok (Instr.iconst .w32 x) v n) = _
  exact ((sleb_parses 5 32).bind fun x => pure_parses (Instr.iconst .w32 x)).complete rest
    ⟨_, _, [], ⟨_, h, rfl, by have := h.length_le; omega⟩, ⟨rfl, rfl⟩, by simp⟩

theorem dec_i64Const {n : Int} {b : List UInt8} (h : SLeb 64 n b) :
    InstrDec (.iconst .w64 (constBits .w64 n)) (0x42 :: b) := by
  refine ⟨0x42, _, rfl, by decide, fun rest r => ?_⟩
  show ((sleb 10 64 _ _).bind fun x v n => .ok (Instr.iconst .w64 x) v n) = _
  exact ((sleb_parses 10 64).bind fun x => pure_parses (Instr.iconst .w64 x)).complete rest
    ⟨_, _, [], ⟨_, h, rfl, by have := h.length_le; omega⟩, ⟨rfl, rfl⟩, by simp⟩

theorem dec_f32Const {bits : Nat} {b : List UInt8} (h : FloatBits .w32 bits b) :
    InstrDec (.fconst .w32 bits) (0x43 :: b) := by
  obtain ⟨hlt, rfl⟩ := h
  simp only at hlt ⊢
  refine ⟨0x43, leBytes _ bits, rfl, by decide, fun rest r => ?_⟩
  show ((leNat 4 (pack (leBytes 4 bits ++ rest)) (leBytes 4 bits ++ rest).length).bind
    fun z v n => .ok (Instr.fconst .w32 z) v n) = _
  have := ((leNat_parses 4).bind fun z => pure_parses (Instr.fconst .w32 z)).complete
    (pre := leBytes 4 bits) rest ⟨bits, leBytes 4 bits, [], ⟨leBytes_length _ _,
      (pack_leBytes (by simpa [two_pow_eight_mul] using hlt)).symm⟩,
      ⟨rfl, rfl⟩, by simp⟩
  exact this

theorem dec_f64Const {bits : Nat} {b : List UInt8} (h : FloatBits .w64 bits b) :
    InstrDec (.fconst .w64 bits) (0x44 :: b) := by
  obtain ⟨hlt, rfl⟩ := h
  simp only at hlt ⊢
  refine ⟨0x44, leBytes _ bits, rfl, by decide, fun rest r => ?_⟩
  show ((leNat 8 (pack (leBytes 8 bits ++ rest)) (leBytes 8 bits ++ rest).length).bind
    fun z v n => .ok (Instr.fconst .w64 z) v n) = _
  have := ((leNat_parses 8).bind fun z => pure_parses (Instr.fconst .w64 z)).complete
    (pre := leBytes 8 bits) rest ⟨bits, leBytes 8 bits, [], ⟨leBytes_length _ _,
      (pack_leBytes (by simpa [two_pow_eight_mul] using hlt)).symm⟩,
      ⟨rfl, rfl⟩, by simp⟩
  exact this

theorem instr_complete {i : Instr} {bs : List UInt8} (h : InstrB i bs) :
    InstrDec i bs ∨ (∃ bt body, i = .block bt body) ∨ (∃ bt body, i = .loop bt body) ∨
      (∃ bt t e, i = .if_ bt t e) ∨ ∃ bt cs body, i = .tryTable bt cs body := by
  cases h with
  | block => exact .inr (.inl ⟨_, _, rfl⟩)
  | loop => exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  | ifNoElse => exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  | ifElse => exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  | tryTable => exact .inr (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  | @returnCallIndirect x y b₁ b₂ hy hx => exact .inl (dec_returnCallIndirect hy hx)
  | plain hm => exact .inl (dec_plain hm)
  | fcPlain hm hn => exact .inl (dec_fcPlain hm hn)
  | @mem mk op m b hm hma => exact .inl (dec_mem hm hma)
  | @idx mk op x b hm hx => exact .inl (dec_idx hm hx)
  | fcIdx hm hn hx => exact .inl (dec_fcIdx hm hn hx)
  | @brTable ls l b₁ b₂ hs hl => exact .inl (dec_brTable hs hl)
  | @callIndirect x y b₁ b₂ hy hx => exact .inl (dec_callIndirect hy hx)
  | selectT h => exact .inl (dec_selectT h)
  | refNull h => exact .inl (dec_refNull h)
  | memorySize hx => exact .inl (dec_memorySize hx)
  | memoryGrow hx => exact .inl (dec_memoryGrow hx)
  | @memoryInit y b₁ b₂ b₃ hn hy hx => exact .inl (dec_memoryInit hn hy hx)
  | @memoryCopy b b₁ b₂ hn h₁ h₂ => exact .inl (dec_memoryCopy hn h₁ h₂)
  | @memoryFill b b₁ hn hx => exact .inl (dec_memoryFill hn hx)
  | @tableInit x y b₁ b₂ b₃ hn hy hx => exact .inl (dec_tableInit hn hy hx)
  | @tableCopy x y b₁ b₂ b₃ hn hx hy => exact .inl (dec_tableCopy hn hx hy)
  | i32Const h => exact .inl (dec_i32Const h)
  | i64Const h => exact .inl (dec_i64Const h)
  | @f32Const bits b h => exact .inl (dec_f32Const h)
  | @f64Const bits b h => exact .inl (dec_f64Const h)

/-! ## Instruction sequences -/

/-- One `seq` step over the encoding `b` of `i`: push `i`, spend one unit of fuel. -/
def Step (i : Instr) (b : List UInt8) : Prop :=
  ∀ F acc r, b.length ≤ F →
    seq (F + 1) acc (pack (b ++ r)) (b ++ r).length = seq F (i :: acc) (pack r) r.length

theorem seq_succ_cons (F : Nat) (acc : List Instr) (op : UInt8) (bs : List UInt8) :
    seq (F + 1) acc (pack (op :: bs)) (op :: bs).length =
      (let plain := (instr op.toNat (pack bs) bs.length (bs.length + 1)).bind
          fun i v n => seq F (i :: acc) v n
       bif Nat.blt 0x05 op.toNat then
         (bif Nat.beq op.toNat 0x0B then .ok (acc, op.toNat) (pack bs) bs.length
          else bif Nat.beq op.toNat 0x1F then
            (blockType (pack bs) bs.length).bind fun bt v n =>
            (vec catchClause v n).bind fun cs v n =>
            (seq F [] v n).bind fun body v n =>
            bif Nat.beq body.2 0x0B then seq F (.tryTable bt cs body.1.reverse :: acc) v n
            else .bad n "else without if"
          else plain)
       else bif Nat.blt op.toNat 0x02 then plain
       else bif Nat.beq op.toNat 0x05 then .ok (acc, op.toNat) (pack bs) bs.length
       else (blockType (pack bs) bs.length).bind fun bt v n =>
         (seq F [] v n).bind fun body v n =>
         bif Nat.beq op.toNat 0x04 then
           (bif Nat.beq body.2 0x0B then seq F (.if_ bt body.1.reverse [] :: acc) v n
            else (seq F [] v n).bind fun els v n =>
              bif Nat.beq els.2 0x0B then
                seq F (.if_ bt body.1.reverse els.1.reverse :: acc) v n
              else .bad n "else without if")
         else bif Nat.beq body.2 0x0B then
           seq F ((bif Nat.beq op.toNat 0x02 then Instr.block else Instr.loop) bt body.1.reverse ::
             acc) v n
         else .bad n "else without if") := by
  simp only [List.length_cons, seq, land_pack_cons, shiftRight_pack_cons]

theorem step_of_dec {i : Instr} {b : List UInt8} (d : InstrDec i b) : Step i b := by
  obtain ⟨op, imm, rfl, hop, hdec⟩ := d
  intro F acc r _
  rw [List.cons_append, seq_succ_cons]
  simp only
  rcases hop with h | ⟨h₁, h₂, h₃⟩
  · rw [blt_false.2 (by omega : op.toNat ≤ 5), blt_true.2 h, Bool.cond_false, Bool.cond_true,
      hdec r _, Res.bind_ok]
  · rw [blt_true.2 h₁, beq_false.2 h₂, beq_false.2 h₃, Bool.cond_true, Bool.cond_false,
      Bool.cond_false, hdec r _, Res.bind_ok]

theorem InstrB.ne_nil {i : Instr} {b : List UInt8} (h : InstrB i b) : b ≠ [] := by
  cases h <;> simp

/-- The terminators `end` (`0x0B`) and `else` (`0x05`). -/
def Term (t : UInt8) : Prop := t.toNat = 0x0B ∨ t.toNat = 0x05

theorem seq_term {F : Nat} {acc : List Instr} {t : UInt8} (ht : Term t) (rest : List UInt8) :
    seq (F + 1) acc (pack (t :: rest)) (t :: rest).length =
      .ok (acc, t.toNat) (pack rest) rest.length := by
  rw [seq_succ_cons]
  rcases ht with h | h <;> rw [h] <;> rfl

theorem structured_block {F : Nat} {acc : List Instr} {op : UInt8} {bt : BlockType}
    {body : List Instr}
    {b₁ b₂ r : List UInt8} (hop : op.toNat = 0x02 ∨ op.toNat = 0x03) (ht : BlockTypeB bt b₁)
    (hbody : seq F [] (pack (b₂ ++ 0x0B :: r)) (b₂ ++ 0x0B :: r).length =
      .ok (body.reverse ++ [], 0x0B) (pack r) r.length) :
    seq (F + 1) acc (pack (op :: (b₁ ++ (b₂ ++ 0x0B :: r))))
      (op :: (b₁ ++ (b₂ ++ 0x0B :: r))).length =
      seq F ((bif Nat.beq op.toNat 0x02 then Instr.block else Instr.loop) bt body :: acc) (pack r)
        r.length := by
  rw [seq_succ_cons]
  have h₁ : Nat.blt 0x05 op.toNat = false := blt_false.2 (by omega)
  have h₂ : Nat.blt op.toNat 0x02 = false := blt_false.2 (by omega)
  have h₃ : Nat.beq op.toNat 0x05 = false := beq_false.2 (by omega)
  have h₄ : Nat.beq op.toNat 0x04 = false := beq_false.2 (by omega)
  simp only [h₁, h₂, h₃, h₄, Bool.cond_false]
  rw [blockType_parses.complete _ ht, Res.bind_ok, hbody, Res.bind_ok]
  simp

theorem structured_if_prefix {F : Nat} {acc : List Instr} {bt : BlockType} {b₁ X : List UInt8}
    (ht : BlockTypeB bt b₁) :
    seq (F + 1) acc (pack (0x04 :: (b₁ ++ X))) (0x04 :: (b₁ ++ X)).length =
      (seq F [] (pack X) X.length).bind fun body v n =>
        bif Nat.beq body.2 0x0B then seq F (.if_ bt body.1.reverse [] :: acc) v n
        else (seq F [] v n).bind fun els v n =>
          bif Nat.beq els.2 0x0B then seq F (.if_ bt body.1.reverse els.1.reverse :: acc) v n
          else .bad n "else without if" := by
  rw [seq_succ_cons]
  simp only [show Nat.blt 0x05 (UInt8.toNat 0x04) = false from rfl,
    show Nat.blt (UInt8.toNat 0x04) 0x02 = false from rfl,
    show Nat.beq (UInt8.toNat 0x04) 0x05 = false from rfl,
    show Nat.beq (UInt8.toNat 0x04) 0x04 = true from rfl, Bool.cond_false, Bool.cond_true]
  rw [blockType_parses.complete _ ht, Res.bind_ok]

theorem structured_tryTable {F : Nat} {acc : List Instr} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {b₁ b₂ b₃ r : List UInt8} (ht : BlockTypeB bt b₁) (hc : Vec CatchB cs b₂)
    (hbody : seq F [] (pack (b₃ ++ 0x0B :: r)) (b₃ ++ 0x0B :: r).length =
      .ok (body.reverse ++ [], 0x0B) (pack r) r.length) :
    seq (F + 1) acc (pack (0x1F :: (b₁ ++ (b₂ ++ (b₃ ++ 0x0B :: r)))))
      (0x1F :: (b₁ ++ (b₂ ++ (b₃ ++ 0x0B :: r)))).length =
      seq F (.tryTable bt cs body :: acc) (pack r) r.length := by
  rw [seq_succ_cons]
  simp only [show Nat.blt 0x05 (UInt8.toNat 0x1F) = true from rfl,
    show Nat.beq (UInt8.toNat 0x1F) 0x0B = false from rfl,
    show Nat.beq (UInt8.toNat 0x1F) 0x1F = true from rfl, Bool.cond_true, Bool.cond_false]
  rw [blockType_parses.complete _ ht, Res.bind_ok,
    (vec_parses catchClause_parses fun _ _ h => CatchB.ne_nil h).complete _ hc, Res.bind_ok,
    hbody, Res.bind_ok]
  simp

/-- `seq` on the encoding of `is` followed by a terminator returns `is` (reversed onto `acc`). -/
def SeqOk (is : List Instr) (pre : List UInt8) : Prop :=
  ∀ (F : Nat) (acc : List Instr) (t : UInt8) (rest : List UInt8), Term t → pre.length < F →
    seq F acc (pack (pre ++ t :: rest)) (pre ++ t :: rest).length =
      .ok (is.reverse ++ acc, t.toNat) (pack rest) rest.length

theorem seqOk_nil : SeqOk [] [] := fun F acc t rest ht hF => by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
  simpa using seq_term ht rest

theorem seqOk_cons {i : Instr} {is : List Instr} {b₁ b₂ : List UInt8} (hi : InstrB i b₁)
    (ihi : Step i b₁) (ihs : SeqOk is b₂) : SeqOk (i :: is) (b₁ ++ b₂) :=
  fun F acc t rest ht hF => by
    have hne := List.length_pos_iff.2 (InstrB.ne_nil hi)
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    simp only [List.length_append] at hF
    rw [List.append_assoc, ihi F acc (b₂ ++ t :: rest) (by omega),
      ihs F (i :: acc) t rest ht (by omega)]
    simp

/-- Completeness of `seq` (by mutual recursion over the derivations). -/
theorem seqOk_of_instrsB {is : List Instr} {pre : List UInt8} (h : InstrsB is pre) : SeqOk is pre :=
  InstrsB.rec (motive_1 := fun i b _ => Step i b) (motive_2 := fun is pre _ => SeqOk is pre)
    (plain := fun hm => step_of_dec (dec_plain hm))
    (fcPlain := fun hm hn => step_of_dec (dec_fcPlain hm hn))
    (mem := fun hm hma => step_of_dec (dec_mem hm hma))
    (idx := fun hm hx => step_of_dec (dec_idx hm hx))
    (fcIdx := fun hm hn hx => step_of_dec (dec_fcIdx hm hn hx))
    (brTable := fun hs hl => step_of_dec (dec_brTable hs hl))
    (callIndirect := fun hy hx => step_of_dec (dec_callIndirect hy hx))
    (returnCallIndirect := fun hy hx => step_of_dec (dec_returnCallIndirect hy hx))
    (selectT := fun h => step_of_dec (dec_selectT h))
    (refNull := fun h => step_of_dec (dec_refNull h))
    (memorySize := fun hx => step_of_dec (dec_memorySize hx))
    (memoryGrow := fun hx => step_of_dec (dec_memoryGrow hx))
    (memoryInit := fun hn hy hx => step_of_dec (dec_memoryInit hn hy hx))
    (memoryCopy := fun hn h₁ h₂ => step_of_dec (dec_memoryCopy hn h₁ h₂))
    (memoryFill := fun hn hx => step_of_dec (dec_memoryFill hn hx))
    (tableInit := fun hn hy hx => step_of_dec (dec_tableInit hn hy hx))
    (tableCopy := fun hn hx hy => step_of_dec (dec_tableCopy hn hx hy))
    (i32Const := fun h => step_of_dec (dec_i32Const h))
    (i64Const := fun h => step_of_dec (dec_i64Const h))
    (f32Const := fun h => step_of_dec (dec_f32Const h))
    (f64Const := fun h => step_of_dec (dec_f64Const h))
    (block := fun {bt} {body} {b₁} {b₂} ht _ ih => fun F acc r hF => by
      have hbody := ih F [] 0x0B r (.inl rfl) (by simp at hF; omega)
      have := structured_block (F := F) (acc := acc) (op := 0x02) (r := r) (.inl rfl) ht hbody
      simpa using this)
    (loop := fun {bt} {body} {b₁} {b₂} ht _ ih => fun F acc r hF => by
      have hbody := ih F [] 0x0B r (.inl rfl) (by simp at hF; omega)
      have := structured_block (F := F) (acc := acc) (op := 0x03) (r := r) (.inr rfl) ht hbody
      simpa using this)
    (ifNoElse := fun {bt} {thn} {b₁} {b₂} ht _ ih => fun F acc r hF => by
      have hbody := ih F [] 0x0B r (.inl rfl) (by simp at hF; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [structured_if_prefix ht, hbody, Res.bind_ok]
      simp)
    (ifElse := fun {bt} {thn} {els} {b₁} {b₂} {b₃} ht _ _ ih₁ ih₂ => fun F acc r hF => by
      simp only [List.length_append, List.length_cons] at hF
      have hthn := ih₁ F [] 0x05 (b₃ ++ 0x0B :: r) (.inr rfl) (by omega)
      have hels := ih₂ F [] 0x0B r (.inl rfl) (by omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [structured_if_prefix ht, hthn, Res.bind_ok]
      simp only [show Nat.beq (UInt8.toNat 0x05) 0x0B = false from rfl, Bool.cond_false]
      rw [hels, Res.bind_ok]
      simp)
    (tryTable := fun {bt} {cs} {body} {b₁} {b₂} {b₃} ht hc _ ih => fun F acc r hF => by
      have hbody := ih F [] 0x0B r (.inl rfl) (by simp at hF; omega)
      have := structured_tryTable (F := F) (acc := acc) (r := r) ht hc hbody
      simpa using this)
    (nil := seqOk_nil)
    (cons := fun hi _ ihi ihs => seqOk_cons hi ihi ihs)
    h

/-- `seq` successes: an instruction sequence, then a terminator. -/
def SeqRes (acc : List Instr) (bs : List UInt8) (res : List Instr × Nat) (v n : Nat) : Prop :=
  ∃ (is : List Instr) (pre : List UInt8) (t : UInt8) (rest : List UInt8),
    bs = pre ++ t :: rest ∧ InstrsB is pre ∧ Term t ∧ res = (is.reverse ++ acc, t.toNat) ∧
      v = pack rest ∧ n = rest.length

theorem seqRes_cons {acc : List Instr} {i : Instr} {b₁ r : List UInt8} {res : List Instr × Nat}
    {v n : Nat} (hi : InstrB i b₁) (h : SeqRes (i :: acc) r res v n) :
    SeqRes acc (b₁ ++ r) res v n := by
  obtain ⟨is, pre, t, rest, rfl, his, ht, rfl, rfl, rfl⟩ := h
  exact ⟨i :: is, b₁ ++ pre, t, rest, by simp, .cons hi his, ht, by simp, rfl, rfl⟩

theorem term_of_toNat {t : UInt8} (h : t.toNat = 0x0B) : t = 0x0B := UInt8.toNat_inj.1 h

/-- Soundness of `seq`. -/
theorem seq_sound (F : Nat) : ∀ {acc : List Instr} {bs : List UInt8} {res : List Instr × Nat}
    {v n : Nat}, seq F acc (pack bs) bs.length = .ok res v n → SeqRes acc bs res v n := by
  induction F with
  | zero => intro acc bs res v n h; simp [seq] at h
  | succ F ih =>
    intro acc bs res v n h
    cases bs with
    | nil => simp [seq] at h
    | cons b bs =>
      rw [seq_succ_cons] at h
      simp only at h
      have plain : (instr b.toNat (pack bs) bs.length (bs.length + 1)).bind
          (fun i v n => seq F (i :: acc) v n) = .ok res v n → SeqRes acc (b :: bs) res v n := by
        intro h
        obtain ⟨i, v₁, n₁, h₁, h₂⟩ := Res.bind_eq_ok.1 h
        obtain ⟨imm, r₁, rfl, hi, rfl, rfl⟩ := instr_sound h₁
        exact seqRes_cons (b₁ := b :: imm) hi (ih h₂)
      cases h₁ : Nat.blt 0x05 b.toNat
      · simp only [h₁, Bool.cond_false] at h
        cases h₂ : Nat.blt b.toNat 0x02
        · simp only [h₂, Bool.cond_false] at h
          cases h₃ : Nat.beq b.toNat 0x05
          · simp only [h₃, Bool.cond_false] at h
            have hb₁ := blt_false.1 h₁
            have hb₂ := blt_false.1 h₂
            have hb₃ := beq_false.1 h₃
            obtain ⟨bt, v₂, n₂, hbt, hk₁⟩ := Res.bind_eq_ok.1 h
            obtain ⟨btb, r₁, rfl, ht, rfl, rfl⟩ := blockType_parses.sound hbt
            obtain ⟨body, v₃, n₃, hbody, hk₂⟩ := Res.bind_eq_ok.1 hk₁
            obtain ⟨is₁, pre₁, t₁, r₂, rfl, his₁, ht₁, rfl, rfl, rfl⟩ := ih hbody
            simp only [List.append_nil, List.reverse_reverse] at hk₂
            cases h₄ : Nat.beq b.toNat 0x04
            · simp only [h₄, Bool.cond_false] at hk₂
              cases h₅ : Nat.beq t₁.toNat 0x0B
              · simp only [h₅, Bool.cond_false] at hk₂; simp at hk₂
              · simp only [h₅, Bool.cond_true] at hk₂
                obtain rfl := term_of_toNat (beq_true.1 h₅)
                have hb₄ := beq_false.1 h₄
                rcases (show b.toNat = 2 ∨ b.toNat = 3 by omega) with hb | hb
                · obtain rfl : b = 0x02 := UInt8.toNat_inj.1 hb
                  have := seqRes_cons (InstrB.block ht his₁) (ih hk₂)
                  simpa using this
                · obtain rfl : b = 0x03 := UInt8.toNat_inj.1 hb
                  have := seqRes_cons (InstrB.loop ht his₁) (ih hk₂)
                  simpa using this
            · simp only [h₄, Bool.cond_true] at hk₂
              obtain rfl : b = 0x04 := UInt8.toNat_inj.1 (beq_true.1 h₄)
              cases h₅ : Nat.beq t₁.toNat 0x0B
              · simp only [h₅, Bool.cond_false] at hk₂
                obtain rfl : t₁ = 0x05 := by
                  rcases ht₁ with e | e
                  · exact absurd e (beq_false.1 h₅)
                  · exact UInt8.toNat_inj.1 e
                obtain ⟨els, v₄, n₄, hels, hk₃⟩ := Res.bind_eq_ok.1 hk₂
                obtain ⟨is₂, pre₂, t₂, r₃, rfl, his₂, -, rfl, rfl, rfl⟩ := ih hels
                simp only [List.append_nil, List.reverse_reverse] at hk₃
                cases h₆ : Nat.beq t₂.toNat 0x0B
                · simp only [h₆, Bool.cond_false] at hk₃; simp at hk₃
                · simp only [h₆, Bool.cond_true] at hk₃
                  obtain rfl := term_of_toNat (beq_true.1 h₆)
                  have := seqRes_cons (InstrB.ifElse ht his₁ his₂) (ih hk₃)
                  simpa using this
              · simp only [h₅, Bool.cond_true] at hk₂
                obtain rfl := term_of_toNat (beq_true.1 h₅)
                have := seqRes_cons (InstrB.ifNoElse ht his₁) (ih hk₂)
                simpa using this
          · simp only [h₃, Bool.cond_true, Res.ok.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨[], [], b, bs, rfl, .nil, .inr (beq_true.1 h₃), by simp, rfl, rfl⟩
        · simp only [h₂, Bool.cond_true] at h
          exact plain h
      · simp only [h₁, Bool.cond_true] at h
        cases h₂ : Nat.beq b.toNat 0x0B
        · simp only [h₂, Bool.cond_false] at h
          cases h₃ : Nat.beq b.toNat 0x1F
          · simp only [h₃, Bool.cond_false] at h
            exact plain h
          · simp only [h₃, Bool.cond_true] at h
            obtain rfl : b = 0x1F := UInt8.toNat_inj.1 (beq_true.1 h₃)
            obtain ⟨bt, v₂, n₂, hbt, hk₁⟩ := Res.bind_eq_ok.1 h
            obtain ⟨btb, r₁, rfl, ht, rfl, rfl⟩ := blockType_parses.sound hbt
            obtain ⟨cs, v₃, n₃, hcs, hk₂⟩ := Res.bind_eq_ok.1 hk₁
            obtain ⟨csb, r₂, rfl, hc, rfl, rfl⟩ :=
              (vec_parses catchClause_parses fun _ _ h => CatchB.ne_nil h).sound hcs
            obtain ⟨body, v₄, n₄, hbody, hk₃⟩ := Res.bind_eq_ok.1 hk₂
            obtain ⟨is₁, pre₁, t₁, r₃, rfl, his₁, ht₁, rfl, rfl, rfl⟩ := ih hbody
            simp only [List.append_nil, List.reverse_reverse] at hk₃
            cases h₅ : Nat.beq t₁.toNat 0x0B
            · simp [h₅] at hk₃
            · simp only [h₅, Bool.cond_true] at hk₃
              obtain rfl := term_of_toNat (beq_true.1 h₅)
              have := seqRes_cons (InstrB.tryTable ht hc his₁) (ih hk₃)
              simpa using this
        · simp only [h₂, Bool.cond_true, Res.ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨[], [], b, bs, rfl, .nil, .inl (beq_true.1 h₂), by simp, rfl, rfl⟩

/-- `expr` decodes exactly `expr` encodings (instructions, then `end`). -/
theorem expr_parses : Parses expr ExprB := by
  constructor
  · intro bs e v n h
    obtain ⟨res, v₁, n₁, h₁, h₂⟩ := Res.bind_eq_ok.1 h
    obtain ⟨is, pre, t, rest, rfl, his, -, rfl, rfl, rfl⟩ := seq_sound _ h₁
    cases h₃ : Nat.beq t.toNat 0x0B
    · simp only [h₃, Bool.cond_false] at h₂; simp at h₂
    · simp only [h₃, Bool.cond_true, Res.ok.injEq] at h₂
      obtain ⟨rfl, rfl, rfl⟩ := h₂
      obtain rfl := term_of_toNat (beq_true.1 h₃)
      exact ⟨pre ++ [0x0B], rest, by simp, ⟨pre, by simpa using his, rfl⟩, rfl, rfl⟩
  · rintro e _ rest ⟨b, hb, rfl⟩
    have := seqOk_of_instrsB hb ((b ++ [0x0B]) ++ rest).length [] 0x0B rest (.inl rfl) (by simp)
    simp only [List.append_assoc, List.singleton_append] at this ⊢
    simp only [expr, this, Res.bind_ok]
    simp

end FVA.Wasm.Decode
