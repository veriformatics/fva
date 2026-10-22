import FVA.Proof.Decode.Pack
import FVA.Impl.Decode
import FVA.Spec.Binary.Types

/-!
# The parsing judgement and the byte-reader combinators

`Parses p R`: run on any input starting with an `R`-encoding of `a`, the decoder step `p`
returns `a` and the rest of the input (complete); every success of `p` splits its input that way
(sound). Both directions are stated on packed inputs `(pack bs, bs.length)`, the form `decode`
receives. Combinator lemmas lift the judgement through `Res.bind`, `sub`, `many` and `vec`.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm FVA.Wasm.Binary

/-- `p` decodes exactly the encodings `R a pre`, as a prefix of any input. -/
structure Parses {α : Type} (p : Nat → Nat → Res α) (R : α → List UInt8 → Prop) : Prop where
  /-- Every success consumes an encoding of its value. -/
  sound : ∀ {bs a v n}, p (pack bs) bs.length = .ok a v n →
    ∃ pre rest, bs = pre ++ rest ∧ R a pre ∧ v = pack rest ∧ n = rest.length
  /-- Every encoding is decoded, whatever follows it. -/
  complete : ∀ {a pre} (rest : List UInt8), R a pre →
    p (pack (pre ++ rest)) (pre ++ rest).length = .ok a (pack rest) rest.length

@[simp] theorem Res.bind_ok {α β : Type} (a : α) (v n : Nat) (f : α → Nat → Nat → Res β) :
    (Res.ok a v n).bind f = f a v n := rfl

theorem Res.bind_eq_ok {α β : Type} {x : Res α} {f : α → Nat → Nat → Res β} {b : β} {v n : Nat} :
    x.bind f = .ok b v n ↔ ∃ a v' n', x = .ok a v' n' ∧ f a v' n' = .ok b v n := by
  cases x with
  | ok a' v' n' =>
    simp only [Res.bind]
    exact ⟨fun h => ⟨a', v', n', rfl, h⟩, fun ⟨_, _, _, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | bad => simp [Res.bind]
  | unsup => simp [Res.bind]

theorem blt_true {a b : Nat} : Nat.blt a b = true ↔ a < b := by simp [Nat.blt_eq]
theorem blt_false {a b : Nat} : Nat.blt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, blt_true]; exact Nat.not_lt
theorem ble_true {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by simp [Nat.ble_eq]
theorem ble_false {a b : Nat} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, ble_true]; exact Nat.not_le
theorem beq_true {a b : Nat} : Nat.beq a b = true ↔ a = b := by simp [Nat.beq_eq]
theorem beq_false {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_true]

/-- The low `k ≤ |bs|` bytes. -/
theorem land_pack_take {bs : List UInt8} {k : Nat} (hk : k ≤ bs.length) :
    Nat.land (pack bs) (Nat.pow 2 (8 * k) - 1) = pack (bs.take k) := by
  have := land_pack_append (bs.take k) (bs.drop k)
  rwa [List.take_append_drop, List.length_take_of_le hk] at this

/-- Dropping `k ≤ |bs|` bytes. -/
theorem shiftRight_pack_drop {bs : List UInt8} {k : Nat} (hk : k ≤ bs.length) :
    Nat.shiftRight (pack bs) (8 * k) = pack (bs.drop k) := by
  have := shiftRight_pack_append (bs.take k) (bs.drop k)
  rwa [List.take_append_drop, List.length_take_of_le hk] at this

theorem Parses.sound_of_len {α : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) {bs : List UInt8} {a : α} {v n k : Nat} (hk : bs.length = k)
    (h : p (pack bs) k = .ok a v n) :
    ∃ pre rest, bs = pre ++ rest ∧ R a pre ∧ v = pack rest ∧ n = rest.length := by
  subst hk; exact hp.sound h

theorem Parses.congr {α : Type} {p : Nat → Nat → Res α} {R S : α → List UInt8 → Prop}
    (h : Parses p R) (hRS : ∀ a bs, R a bs ↔ S a bs) : Parses p S :=
  ⟨fun hp => by
    obtain ⟨pre, rest, h₁, h₂, h₃, h₄⟩ := h.sound hp
    exact ⟨pre, rest, h₁, (hRS _ _).1 h₂, h₃, h₄⟩,
   fun rest hs => h.complete rest ((hRS _ _).2 hs)⟩

/-- Sequencing: `p` then `q a` parses the concatenated encodings. -/
theorem Parses.bind {α β : Type} {p : Nat → Nat → Res α} {q : α → Nat → Nat → Res β}
    {R : α → List UInt8 → Prop} {S : α → β → List UInt8 → Prop}
    (hp : Parses p R) (hq : ∀ a, Parses (q a) (S a)) :
    Parses (fun v n => (p v n).bind fun a v n => q a v n)
      (fun b bs => ∃ a b₁ b₂, R a b₁ ∧ S a b b₂ ∧ bs = b₁ ++ b₂) := by
  constructor
  · intro bs b v n h
    obtain ⟨a, v', n', h₁, h₂⟩ := Res.bind_eq_ok.1 h
    obtain ⟨pre₁, rest₁, rfl, hR, rfl, rfl⟩ := hp.sound h₁
    obtain ⟨pre₂, rest, rfl, hS, rfl, rfl⟩ := (hq a).sound h₂
    exact ⟨pre₁ ++ pre₂, rest, by simp, ⟨a, pre₁, pre₂, hR, hS, rfl⟩, rfl, rfl⟩
  · rintro b _ rest ⟨a, b₁, b₂, hR, hS, rfl⟩
    simp only [List.append_assoc]
    rw [hp.complete (b₂ ++ rest) hR]
    exact (hq a).complete rest hS

/-- `byte` reads one byte. -/
theorem byte_parses : Parses byte (fun x bs => ∃ b : UInt8, x = b.toNat ∧ bs = [b]) := by
  constructor
  · intro bs x v n h
    cases bs with
    | nil => simp [byte] at h
    | cons b bs =>
      simp only [byte, List.length_cons, Res.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[b], bs, rfl, ⟨b, land_pack_cons b bs, rfl⟩, shiftRight_pack_cons b bs, rfl⟩
  · rintro x _ rest ⟨b, rfl, rfl⟩
    simp only [List.cons_append, List.nil_append, byte, List.length_cons, land_pack_cons,
      shiftRight_pack_cons]

/-- `leNat k` reads `k` raw bytes as their packing. -/
theorem leNat_parses (k : Nat) : Parses (leNat k) (fun x bs => bs.length = k ∧ x = pack bs) := by
  constructor
  · intro bs x v n h
    simp only [leNat] at h
    cases hk : Nat.blt bs.length k
    · simp only [hk, Bool.cond_false, Res.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hle := blt_false.1 hk
      refine ⟨bs.take k, bs.drop k, (List.take_append_drop k bs).symm,
        ⟨List.length_take_of_le hle, land_pack_take hle⟩, shiftRight_pack_drop hle, ?_⟩
      simp [Nat.sub_eq]
    · simp [hk] at h
  · rintro x pre rest ⟨rfl, rfl⟩
    have hk : Nat.blt (pre.length + rest.length) pre.length = false := blt_false.2 (by omega)
    simp only [leNat, List.length_append, hk, Bool.cond_false, land_pack_append,
      shiftRight_pack_append,
      List.length_append, Nat.sub_eq, Nat.add_sub_cancel_left]

/-- `sub k p` runs `p` on exactly the next `k` bytes, which `p` must consume. -/
theorem sub_parses {α : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) (k : Nat) : Parses (sub k p) (fun a bs => bs.length = k ∧ R a bs) := by
  constructor
  · intro bs a v n h
    simp only [sub] at h
    cases hk : Nat.blt bs.length k
    · have hle := blt_false.1 hk
      have hlen : (bs.take k).length = k := List.length_take_of_le hle
      simp only [hk, Bool.cond_false, land_pack_take hle] at h
      generalize hr : p (pack (bs.take k)) k = r at h
      cases r with
      | bad => simp at h
      | unsup => simp at h
      | ok a' v' n' =>
        cases n' with
        | succ => simp at h
        | zero =>
          simp only [Res.ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨pre, rest', hpre, hR, -, hn⟩ := hp.sound_of_len hlen hr
          have : rest' = [] := List.eq_nil_of_length_eq_zero hn.symm
          subst this
          simp only [List.append_nil] at hpre
          exact ⟨bs.take k, bs.drop k, (List.take_append_drop k bs).symm, ⟨hlen, hpre ▸ hR⟩,
            shiftRight_pack_drop hle, by simp [Nat.sub_eq]⟩
    · simp [hk] at h
  · rintro a pre rest ⟨rfl, hR⟩
    have hk : Nat.blt (pre.length + rest.length) pre.length = false := blt_false.2 (by omega)
    have hin := hp.complete [] hR
    simp only [List.append_nil, pack_nil, List.length_nil] at hin
    simp only [sub, List.length_append, hk, Bool.cond_false, land_pack_append, hin,
      shiftRight_pack_append,
      List.length_append, Nat.sub_eq, Nat.add_sub_cancel_left]

/-- `many p count` parses exactly `count` consecutive encodings. -/
theorem many_parses {α : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) (count : Nat) :
    Parses (many p count) (fun as bs => as.length = count ∧ Seq R as bs) := by
  induction count with
  | zero =>
    constructor
    · intro bs as v n h
      simp only [many, Res.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], bs, rfl, ⟨rfl, .nil⟩, rfl, rfl⟩
    · rintro as pre rest ⟨hl, hs⟩
      cases hs with
      | nil => rfl
      | cons => simp at hl
  | succ count ih =>
    have h := (hp.bind fun a => (ih.bind fun as => (show Parses (fun v n => Res.ok (a :: as) v n)
      (fun r bs => r = a :: as ∧ bs = []) from
      ⟨fun {bs _ _ _} h => by
        simp only [Res.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], bs, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩,
       fun rest ⟨h₁, h₂⟩ => by subst h₁; subst h₂; rfl⟩)))
    refine (h.congr ?_)
    intro as bs
    constructor
    · rintro ⟨a, b₁, b₂, hR, ⟨as', b₃, b₄, ⟨hl, hs⟩, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
      exact ⟨by simp [hl], by simpa using Seq.cons hR hs⟩
    · rintro ⟨hl, hs⟩
      cases hs with
      | nil => simp at hl
      | @cons a as' b₁ b₂ hR hs =>
        exact ⟨a, b₁, b₂, hR, ⟨as', b₂, [], ⟨by simpa using hl, hs⟩, ⟨rfl, rfl⟩, by simp⟩, rfl⟩

/-- `uleb fuel N` decodes `uN` encodings of at most `fuel` bytes. -/
theorem uleb_parses (fuel N : Nat) :
    Parses (uleb fuel N) (fun x bs => ULeb N x bs ∧ bs.length ≤ fuel) := by
  induction fuel generalizing N with
  | zero =>
    constructor
    · intro bs x v n h; simp [uleb] at h
    · rintro x pre rest ⟨h, hl⟩
      cases h <;> simp at hl
  | succ fuel ih =>
    constructor
    · intro bs x v n h
      cases bs with
      | nil => simp [uleb] at h
      | cons b bs =>
        have hb := b.toNat_lt
        simp only [uleb, List.length_cons, land_pack_cons, shiftRight_pack_cons] at h
        cases h1 : Nat.blt b.toNat 128
        · simp only [h1, Bool.cond_false] at h
          cases h2 : Nat.blt 7 N
          · simp only [h2, Bool.cond_false] at h; simp at h
          · simp only [h2, Bool.cond_true] at h
            obtain ⟨m, v', n', hr, hk⟩ := Res.bind_eq_ok.1 h
            simp only [Res.ok.injEq] at hk
            obtain ⟨rfl, rfl, rfl⟩ := hk
            obtain ⟨pre, rest, rfl, ⟨hm, hl⟩, rfl, rfl⟩ := (ih (N - 7)).sound hr
            refine ⟨b :: pre, rest, rfl, ⟨?_, by simp; omega⟩, rfl, rfl⟩
            have := ULeb.more b (by have := blt_false.1 h1; simpa using this) (blt_true.1 h2) hm
            simpa using this
        · simp only [h1, Bool.cond_true] at h
          cases h2 : Nat.blt b.toNat (Nat.pow 2 N)
          · simp only [h2, Bool.cond_false] at h; simp at h
          · simp only [h2, Bool.cond_true, Res.ok.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨[b], bs, rfl, ⟨ULeb.last b (by simpa using blt_true.1 h1) (blt_true.1 h2),
              by simp⟩, rfl, rfl⟩
    · rintro x pre rest ⟨h, hl⟩
      cases h with
      | last b h7 hN =>
        have h1 : Nat.blt b.toNat 128 = true := blt_true.2 (by simpa using h7)
        have h2 : Nat.blt b.toNat (Nat.pow 2 N) = true := blt_true.2 hN
        simp only [List.cons_append, List.nil_append, uleb, List.length_cons, land_pack_cons,
          shiftRight_pack_cons, h1, h2, Bool.cond_true]
      | @more _ m rest' b h7 hN hm =>
        have h1 : Nat.blt b.toNat 128 = false := blt_false.2 (by simpa using h7)
        have h2 : Nat.blt 7 N = true := blt_true.2 hN
        have hr := (ih (N - 7)).complete rest ⟨hm, by simp at hl; omega⟩
        simp only [List.cons_append, uleb, List.length_cons, land_pack_cons, shiftRight_pack_cons,
          h1, h2, Bool.cond_false, Bool.cond_true, Nat.sub_eq, hr, Res.bind_ok]
        simp only [Nat.mul_eq, Nat.add_eq]

/-- A `uN` encoding (`N > 0`) has at most `⌈N/7⌉` bytes. -/
theorem _root_.FVA.Wasm.Binary.ULeb.length_lt {N x : Nat} {bs : List UInt8} (h : ULeb N x bs)
    (hN : 0 < N) :
    7 * bs.length < N + 7 := by
  induction h with
  | last => simp; omega
  | more _ _ hN' _ ih => simp; have := ih (by omega); omega

/-- `u32`. -/
theorem u32_parses : Parses u32 (ULeb 32) :=
  (uleb_parses 5 32).congr fun _ _ => ⟨fun h => h.1, fun h => ⟨h, by have := h.length_lt; omega⟩⟩

theorem pow_pred_le (N : Nat) : 2 ^ (N - 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) (by omega)

/-- `sN` bits of a one-byte non-negative value. -/
theorem bits_pos {N b : Nat} (hb : b < 2 ^ (N - 1)) : ((b : Int) % 2 ^ N).toNat = b := by
  have h := pow_pred_le N
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast (show b < 2 ^ N by omega))]
  simp

/-- `sN` bits of a one-byte negative value. -/
theorem bits_neg {N b : Nat} (h128 : b < 128) (hN : 128 - 2 ^ (N - 1) ≤ b) :
    (((b : Int) - 128) % 2 ^ N).toNat = 2 ^ N + b - 128 := by
  have h := pow_pred_le N
  have hP : ((2 : Int) ^ N) = ((2 ^ N : Nat) : Int) := by push_cast; rfl
  rw [hP, ← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- `sN` bits of `128·m + c` from the `s(N−7)` bits of `m`. -/
theorem bits_more {N m : Nat} {mi : Int} {c : Nat} (hN : 7 < N) (hc : c < 128)
    (hm : m = (mi % 2 ^ (N - 7)).toNat) :
    ((128 * mi + c : Int) % 2 ^ N).toNat = 128 * m + c := by
  have hM : (2 : Int) ^ N = 128 * 2 ^ (N - 7) := by
    rw [show N = (N - 7) + 7 by omega, Int.pow_add]; simp [Int.mul_comm]
  have hpos : (0 : Int) < 2 ^ (N - 7) := Int.pow_pos (by decide)
  have hr0 := Int.emod_nonneg mi (Int.ne_of_gt hpos)
  have hr1 := Int.emod_lt_of_pos mi hpos
  have hdecomp := Int.emod_def mi (2 ^ (N - 7))
  have : (128 * mi + c : Int) = (128 * (mi % 2 ^ (N - 7)) + c) + 2 ^ N * (mi / 2 ^ (N - 7)) := by
    rw [hM, Int.mul_assoc]; omega
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by rw [hM]; omega), hm]
  omega

/-- `sleb fuel N` decodes `sN` encodings of at most `fuel` bytes, as `N`-bit two's complement. -/
theorem sleb_parses (fuel N : Nat) :
    Parses (sleb fuel N)
      (fun x bs => ∃ i, SLeb N i bs ∧ x = (i % 2 ^ N).toNat ∧ bs.length ≤ fuel) := by
  induction fuel generalizing N with
  | zero =>
    constructor
    · intro bs x v n h; simp [sleb] at h
    · rintro x pre rest ⟨i, h, -, hl⟩
      cases h <;> simp at hl
  | succ fuel ih =>
    constructor
    · intro bs x v n h
      cases bs with
      | nil => simp [sleb] at h
      | cons b bs =>
        have hb := b.toNat_lt
        simp only [sleb, List.length_cons, land_pack_cons, shiftRight_pack_cons] at h
        cases h1 : Nat.blt b.toNat 64
        · simp only [h1, Bool.cond_false] at h
          cases h2 : Nat.blt b.toNat 128
          · simp only [h2, Bool.cond_false] at h
            cases h3 : Nat.blt 7 N
            · simp only [h3, Bool.cond_false] at h; simp at h
            · simp only [h3, Bool.cond_true] at h
              obtain ⟨m, v', n', hr, hk⟩ := Res.bind_eq_ok.1 h
              simp only [Res.ok.injEq] at hk
              obtain ⟨rfl, rfl, rfl⟩ := hk
              obtain ⟨pre, rest, rfl, ⟨mi, hm, hmv, hl⟩, rfl, rfl⟩ := (ih (N - 7)).sound hr
              have h7 : 2 ^ 7 ≤ b.toNat := by have := blt_false.1 h2; simpa using this
              refine ⟨b :: pre, rest, rfl, ⟨_, SLeb.more b h7 (blt_true.1 h3) hm, ?_, ?_⟩, rfl, rfl⟩
              · have := bits_more (c := b.toNat - 128) (blt_true.1 h3) (by omega) hmv
                simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
                rw [← this]; congr 2; push_cast [show 128 ≤ b.toNat by omega]; omega
              · simp; omega
          · simp only [h2, Bool.cond_true] at h
            cases h3 : Nat.ble (128 - Nat.pow 2 (N - 1)) b.toNat
            · simp only [h3, Bool.cond_false] at h; simp at h
            · simp only [h3, Bool.cond_true, Res.ok.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              have h64 : 2 ^ 6 ≤ b.toNat := by have := blt_false.1 h1; simpa using this
              have h128 := blt_true.1 h2
              have hN := ble_true.1 h3
              have hNi : (2 ^ 7 : Int) - 2 ^ (N - 1) ≤ b.toNat := by
                have : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by push_cast; rfl
                have hp := pow_pred_le N
                simp only [Nat.pow_eq] at hN
                omega
              refine ⟨[b], bs, rfl, ⟨_, SLeb.neg b h64 (by simpa using h128) hNi, ?_, by simp⟩,
                rfl, rfl⟩
              rw [show (2 : Int) ^ 7 = 128 by decide, bits_neg h128 (by simpa using hN)]
              simp [Nat.sub_eq, Nat.add_eq]
        · simp only [h1, Bool.cond_true] at h
          cases h2 : Nat.blt b.toNat (Nat.pow 2 (N - 1))
          · simp only [h2, Bool.cond_false] at h; simp at h
          · simp only [h2, Bool.cond_true, Res.ok.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨[b], bs, rfl, ⟨_, SLeb.pos b (by simpa using blt_true.1 h1) (blt_true.1 h2),
              (bits_pos (blt_true.1 h2)).symm, by simp⟩, rfl, rfl⟩
    · rintro x pre rest ⟨i, h, rfl, hl⟩
      cases h with
      | pos b h6 hN =>
        have h1 : Nat.blt b.toNat 64 = true := blt_true.2 (by simpa using h6)
        have h2 : Nat.blt b.toNat (Nat.pow 2 (N - 1)) = true := blt_true.2 hN
        simp only [List.cons_append, List.nil_append, sleb, List.length_cons, land_pack_cons,
          shiftRight_pack_cons, h1, h2, Bool.cond_true, bits_pos hN]
      | neg b h6 h7 hN =>
        have h1 : Nat.blt b.toNat 64 = false := blt_false.2 (by simpa using h6)
        have h2 : Nat.blt b.toNat 128 = true := blt_true.2 (by simpa using h7)
        have hNn : 128 - 2 ^ (N - 1) ≤ b.toNat := by
          have : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by push_cast; rfl
          omega
        have h3 : Nat.ble (128 - Nat.pow 2 (N - 1)) b.toNat = true := ble_true.2 hNn
        simp only [List.cons_append, List.nil_append, sleb, List.length_cons, land_pack_cons,
          shiftRight_pack_cons, h1, h2, h3, Bool.cond_true, Bool.cond_false]
        rw [show (2 : Int) ^ 7 = 128 by decide, bits_neg (by simpa using h7) hNn]
        simp [Nat.sub_eq, Nat.add_eq]
      | @more _ mi rest' b h7 hN hm =>
        have h1 : Nat.blt b.toNat 64 = false := blt_false.2 (by simp at h7; omega)
        have h2 : Nat.blt b.toNat 128 = false := blt_false.2 (by simpa using h7)
        have h3 : Nat.blt 7 N = true := blt_true.2 hN
        have hr := (ih (N - 7)).complete rest ⟨mi, hm, rfl, by simp at hl; omega⟩
        simp only [List.cons_append, sleb, List.length_cons, land_pack_cons, shiftRight_pack_cons,
          h1, h2, h3, Bool.cond_false, Bool.cond_true, Nat.sub_eq, hr, Res.bind_ok]
        have := bits_more (c := b.toNat - 128) hN (by have := b.toNat_lt; omega) rfl (mi := mi)
        simp only [Nat.mul_eq, Nat.add_eq, Res.ok.injEq, and_true]
        rw [← this]; congr 2; push_cast [show 128 ≤ b.toNat by simpa using h7]; omega

end FVA.Wasm.Decode
