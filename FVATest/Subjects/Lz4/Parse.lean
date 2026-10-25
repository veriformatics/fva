import FVATest.Subjects.Lz4.Format

/-! A parser for LZ4 blocks with enough fuel returns every parse (`Parses`) of its input, so a
block's sequences are unique (proof support; outside the review surface). -/

namespace Lz4

/-- The value of extension bytes after a token field of 15, added to `acc`, and the bytes after
them. -/
def readExt (acc : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs => if b.toNat = 255 then readExt (acc + 255) bs else some (acc + b.toNat, bs)

/-- A length with token field `f`, and the bytes after it. -/
def readLen (f : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  if f < 15 then some (f, bs) else readExt 15 bs

/-- The sequences and last literals of a block, one fuel unit per sequence. -/
def parse : Nat → List UInt8 → Option (List Seq × List UInt8)
  | 0, _ | _ + 1, [] => none
  | fuel + 1, t :: bs => (readLen (t.toNat / 16) bs).bind fun (l, bs) =>
    if bs.length < l then none else
    match bs.drop l with
    | [] => some ([], bs.take l)
    | [_] => none
    | o0 :: o1 :: rest => (readLen (t.toNat % 16) rest).bind fun (m, rest) =>
      (parse fuel rest).map fun (ss, last) =>
        (⟨bs.take l, o0.toNat + 256 * o1.toNat, m + 4⟩ :: ss, last)

theorem readExt_ext (acc k r : Nat) (hr : r < 255) (rest : List UInt8) :
    readExt acc (List.replicate k 255 ++ [UInt8.ofNat r] ++ rest) =
      some (acc + 255 * k + r, rest) := by
  induction k generalizing acc with
  | zero =>
    have : (UInt8.ofNat r).toNat = r := by simp; omega
    simp [readExt, this, show r ≠ 255 by omega]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, readExt]
    simp only [show (255 : UInt8).toNat = 255 from rfl, ↓reduceIte]
    rw [ih]
    congr 2
    omega

theorem readLen_ext (n : Nat) (rest : List UInt8) :
    readLen (min n 15) (ext n ++ rest) = some (n, rest) := by
  unfold readLen ext
  by_cases hn : n < 15
  · simp [hn, Nat.min_eq_left (Nat.le_of_lt hn)]
  · simp only [Nat.min_eq_right (Nat.le_of_not_lt hn), Nat.lt_irrefl, hn, ↓reduceIte]
    rw [readExt_ext 15 _ _ (Nat.mod_lt _ (by omega))]
    congr 2
    omega

theorem token_toNat (a b : Nat) (ha : a ≤ 15) (hb : b < 16) :
    (UInt8.ofNat (16 * a + b)).toNat = 16 * a + b := by
  simp
  omega

theorem offset_toNat (off : Nat) (h : off < 65536) :
    (UInt8.ofNat off).toNat + 256 * (UInt8.ofNat (off / 256)).toNat = off := by
  simp
  omega

/-- The last sequence: its literals end the block. -/
theorem parse_last (fuel : Nat) (last : List UInt8) (low : Nat) (hlow : low < 16) :
    parse (fuel + 1) (head last low) = some ([], last) := by
  have ht := token_toNat (min last.length 15) low (Nat.min_le_right _ _) hlow
  have hd : (16 * min last.length 15 + low) / 16 = min last.length 15 := by omega
  simp only [head, List.cons_append, parse, ht, hd, readLen_ext, Option.bind_some,
    Nat.lt_irrefl, ↓reduceIte, List.drop_length, List.take_length]

/-- A sequence with a match, then more bytes: one sequence, then the parse of the rest. -/
theorem parse_seq (fuel : Nat) (s : Seq) (rest : List UInt8) (hoff : s.off < 65536)
    (hlen : 4 ≤ s.len) :
    parse (fuel + 1) (s.bytes ++ rest) =
      (parse fuel rest).map fun (ss, last) => (s :: ss, last) := by
  have ht := token_toNat (min s.lits.length 15) (min (s.len - 4) 15) (Nat.min_le_right _ _)
    (by omega)
  have hd : (16 * min s.lits.length 15 + min (s.len - 4) 15) / 16 = min s.lits.length 15 := by
    omega
  have hm : (16 * min s.lits.length 15 + min (s.len - 4) 15) % 16 = min (s.len - 4) 15 := by
    omega
  have hb : s.bytes ++ rest = UInt8.ofNat (16 * min s.lits.length 15 + min (s.len - 4) 15) ::
      (ext s.lits.length ++ (s.lits ++ (UInt8.ofNat s.off :: UInt8.ofNat (s.off / 256) ::
        (ext (s.len - 4) ++ rest)))) := by
    simp [Seq.bytes, head]
  have hl : ¬ (s.lits ++ (UInt8.ofNat s.off :: UInt8.ofNat (s.off / 256) ::
      (ext (s.len - 4) ++ rest))).length < s.lits.length := by simp
  rw [hb]
  simp only [parse, ht, hd, hm, readLen_ext, Option.bind_some, hl, ↓reduceIte, List.drop_left,
    List.take_left, offset_toNat _ hoff, Nat.sub_add_cancel hlen]

/-- The parser returns every parse, given a fuel unit per sequence. -/
theorem parse_complete {b : List UInt8} {ss : List Seq} {last : List UInt8}
    (h : Parses b ss last) : ∀ fuel, ss.length < fuel → parse fuel b = some (ss, last) := by
  obtain ⟨low, hlow, hb, hss⟩ := h
  subst hb
  induction ss with
  | nil =>
    intro fuel hf
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simpa using parse_last fuel last low hlow
  | cons s ss ih =>
    intro fuel hf
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨-, hoff, hlen⟩ := hss s (by simp)
    have hrest := ih (fun s' h' => hss s' (by simp [h'])) fuel (by simp at hf; omega)
    rw [List.flatMap_cons, List.append_assoc, parse_seq fuel s _ hoff hlen, hrest]
    rfl

/-- A block's sequences and last literals are unique. -/
theorem Parses.unique {b : List UInt8} {ss ss' : List Seq} {last last' : List UInt8}
    (h : Parses b ss last) (h' : Parses b ss' last') : ss = ss' ∧ last = last' := by
  have := (parse_complete h (ss.length + ss'.length + 1) (by omega)).symm.trans
    (parse_complete h' (ss.length + ss'.length + 1) (by omega))
  simpa using this

end Lz4
