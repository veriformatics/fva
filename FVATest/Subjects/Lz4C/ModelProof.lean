import FVATest.Subjects.Lz4C.Model
import FVATest.Subjects.Lz4.Any
import FVATest.Subjects.Lz4.Parse

/-! `Model.decode` against the LZ4 format: an accepted block parses (`ParsesAny`) to the decoded
content (R3's model half), and a valid block that fits decodes (R2's) (proof support; outside the
review surface). -/

namespace Subjects.Lz4C.Model

open Lz4

theorem at!_of_drop {inp rest : List UInt8} {q : Nat} {b : UInt8} (h : inp.drop q = b :: rest) :
    at! inp q = b.toNat := by
  have : inp[q]? = some b := by
    have h' := congrArg (·[0]?) h
    simpa [List.getElem?_drop] using h'
  simp [at!, this]

theorem drop_succ_of_drop {inp rest : List UInt8} {q : Nat} {b : UInt8}
    (h : inp.drop q = b :: rest) : inp.drop (q + 1) = rest := by
  have := congrArg (·.drop 1) h
  simpa [List.drop_drop, Nat.add_comm] using this

theorem drop_cons {inp : List UInt8} {q : Nat} (hq : q < inp.length) :
    inp.drop q = inp[q] :: inp.drop (q + 1) := by
  rw [List.drop_eq_getElem_cons hq]

/-- An extension-byte read is `k` bytes of 255 then one byte `r < 255`: the canonical encoding. -/
theorem ext_sound {inp : List UInt8} {L : Nat} :
    ∀ {fuel q acc a q' : Nat}, ext inp L fuel q acc = some (a, q') →
      ∃ k r, r < 255 ∧ a = acc + 255 * k + r ∧ q' = q + k + 1 ∧ q' + L ≤ inp.length ∧
        a < 2 ^ 31 ∧ inp.drop q = List.replicate k 255 ++ [UInt8.ofNat r] ++ inp.drop q' := by
  intro fuel
  induction fuel with
  | zero => intro q acc a q' h; simp [ext] at h
  | succ fuel ih =>
    intro q acc a q' h
    unfold ext at h
    split at h
    · rename_i hq
      have hlt : q < inp.length := by omega
      have hb := drop_cons hlt
      have hat : at! inp q = inp[q].toNat := at!_of_drop hb
      split at h
      · rename_i hacc
        split at h
        · rename_i h255
          obtain ⟨k, r, hr, ha, hq', hL, ha31, hd⟩ := ih h
          refine ⟨k + 1, r, hr, by omega, by omega, hL, ha31, ?_⟩
          rw [hb, hd]
          have : inp[q] = 255 := by
            apply UInt8.toNat_inj.mp; rw [← hat, h255]; rfl
          simp [this, List.replicate_succ]
        · rename_i h255
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlt' : at! inp q < 255 := by
            have := inp[q].toNat_lt; omega
          refine ⟨0, at! inp q, hlt', by omega, by omega, by omega, by omega, ?_⟩
          rw [hb]
          simp [hat]
      · simp at h
    · simp at h

/-- The canonical encoding reads back (enough fuel, room after it, no overflow). -/
theorem ext_complete {inp : List UInt8} {L r : Nat} (hr : r < 255) :
    ∀ (k : Nat) {fuel q acc : Nat} {rest : List UInt8}, k < fuel →
      inp.drop q = List.replicate k 255 ++ [UInt8.ofNat r] ++ rest →
      q + k + 1 + L ≤ inp.length → acc + 255 * k + r < 2 ^ 31 →
      ext inp L fuel q acc = some (acc + 255 * k + r, q + k + 1) := by
  intro k
  induction k with
  | zero =>
    intro fuel q acc rest hf hd hL hacc
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hat : at! inp q = r := by
      rw [at!_of_drop (b := UInt8.ofNat r) (rest := rest) (by simpa using hd)]
      simp; omega
    unfold ext
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega), hat]
    simp
  | succ k ih =>
    intro fuel q acc rest hf hd hL hacc
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hd' : inp.drop q = 255 :: (List.replicate k 255 ++ [UInt8.ofNat r] ++ rest) := by
      simpa [List.replicate_succ] using hd
    have hat : at! inp q = 255 := by rw [at!_of_drop hd']; rfl
    have hnext := drop_succ_of_drop hd'
    unfold ext
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hat, hat,
      ih (fuel := fuel) (q := q + 1) (acc := acc + 255) (rest := rest) (by omega) hnext (by omega)
        (by omega)]
    congr 2 <;> omega


/-- A literal or match length `n ≥ 15` read as extension bytes onto 15 is `Lz4.ext n`. -/
theorem ext_bytes {inp : List UInt8} {L fuel q a q' : Nat} (h : ext inp L fuel q 0 = some (a, q')) :
    inp.drop q = Lz4.ext (15 + a) ++ inp.drop q' ∧ q' + L ≤ inp.length ∧ a < 2 ^ 31 ∧ q < q' := by
  obtain ⟨k, r, hr, ha, hq', hL, ha31, hd⟩ := ext_sound h
  refine ⟨?_, hL, ha31, by omega⟩
  have h1 : (15 + a - 15) / 255 = k := by omega
  have h2 : (15 + a - 15) % 255 = r := by omega
  simp only [Lz4.ext, show ¬ 15 + a < 15 by omega, ite_false, h1, h2, hd, List.append_assoc]

/-- `copyMatch` continuing: the match length `m` (its field `ml0 = min m 15`, its extension bytes
from `j`), the offset inside the output, room for the match + 5, the copied output. -/
theorem copyMatch_cont {inp : List UInt8} {cap j off ml0 i' : Nat} {out o : List UInt8}
    (hml : ml0 < 16) (h : copyMatch inp cap j out off ml0 = .cont i' o) :
    ∃ m, min m 15 = ml0 ∧ inp.drop j = Lz4.ext m ++ inp.drop i' ∧ j ≤ i' ∧
      (ml0 = 15 → i' ≤ inp.length) ∧ off ≤ out.length ∧ out.length + (m + 4) + 5 ≤ cap ∧
      Lz4.copy out off (m + 4) = some o := by
  unfold copyMatch at h
  split at h
  · simp at h
  · rename_i mm ii hm
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i o' hc
          simp only [Out.cont.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          by_cases h15 : ml0 = 15
          · rw [ite_eq_left h15] at hm
            obtain ⟨⟨a, q⟩, hx, hy⟩ := Option.map_eq_some_iff.mp hm
            simp only [Prod.mk.injEq] at hy
            obtain ⟨rfl, rfl⟩ := hy
            obtain ⟨hd, hL, -, hlt⟩ := ext_bytes hx
            exact ⟨15 + a, by omega, hd, by omega, fun _ => by omega, by omega, by omega, hc⟩
          · rw [ite_eq_right h15] at hm
            simp only [Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨h1, h2⟩ := hm
            subst h1 h2
            have hle : ml0 < 15 := by omega
            exact ⟨ml0, by omega, by simp [Lz4.ext, hle], Nat.le_refl _, fun h => absurd h h15,
              by omega, by omega, hc⟩
        · simp at h

theorem at!_lt {inp : List UInt8} {i : Nat} (hi : i < inp.length) : at! inp i = inp[i].toNat := by
  simp [at!, List.getElem?_eq_getElem hi]

/-- The bytes from a token at `i`: the token (fields `min len 15`, `min m 15`), the literal
length's extension bytes, `len` literals from `q`, a 2-byte offset, the match length's extension
bytes up to `i'`, form one sequence. -/
theorem assemble {inp : List UInt8} {i q len m i' : Nat} (hi : i < inp.length)
    (hll : min len 15 = at! inp i / 16) (hml : min m 15 = at! inp i % 16)
    (hlit : inp.drop (i + 1) = Lz4.ext len ++ inp.drop q) (hroom : q + len + 2 ≤ inp.length)
    (hmatch : inp.drop (q + len + 2) = Lz4.ext m ++ inp.drop i') :
    inp.drop i = Seq.bytes ⟨(inp.drop q).take len, off16 inp (q + len), m + 4⟩ ++ inp.drop i' ∧
      off16 inp (q + len) < 65536 := by
  have hq : q + len + 1 < inp.length := by omega
  have hq0 : q + len < inp.length := by omega
  have hb0 := at!_lt hq0
  have hb1 := at!_lt hq
  have ht := at!_lt hi
  have hlen : ((inp.drop q).take len).length = len := by simp; omega
  have hoff : off16 inp (q + len) = inp[q + len].toNat + 256 * inp[q + len + 1].toNat := by
    simp only [off16, hb0, hb1]
  have hlt0 := inp[q + len].toNat_lt
  have hlt1 := inp[q + len + 1].toNat_lt
  refine ⟨?_, by omega⟩
  have hsplit : inp.drop q = (inp.drop q).take len ++
      (inp[q + len] :: inp[q + len + 1] :: inp.drop (q + len + 2)) := by
    rw [← drop_cons hq, ← drop_cons hq0]
    have : inp.drop (q + len) = (inp.drop q).drop len := by rw [List.drop_drop]
    rw [this, List.take_append_drop]
  have htok : UInt8.ofNat (16 * min len 15 + min m 15) = inp[i] := by
    rw [hll, hml, ht]
    have : 16 * (inp[i].toNat / 16) + inp[i].toNat % 16 = inp[i].toNat := by omega
    rw [this]; exact UInt8.ofNat_toNat
  have hlo : UInt8.ofNat (off16 inp (q + len)) = inp[q + len] := by
    rw [hoff]; apply UInt8.toNat_inj.mp; simp
  have hhi : UInt8.ofNat (off16 inp (q + len) / 256) = inp[q + len + 1] := by
    rw [hoff]; apply UInt8.toNat_inj.mp; simp; omega
  conv => lhs; rw [drop_cons hi, hlit, hsplit, hmatch]
  simp only [Seq.bytes, head, hlen, show m + 4 - 4 = m by omega, htok, hlo, hhi, List.cons_append,
    List.append_assoc, List.nil_append]

/-- `literal` continuing: the literal check passed, then `copyMatch`. -/
theorem literal_cont {inp : List UInt8} {cap q len ml0 i' : Nat} {out o : List UInt8}
    (h : literal inp cap q out len ml0 = .cont i' o) :
    out.length + len + 12 ≤ cap ∧ q + len + 8 ≤ inp.length ∧
      copyMatch inp cap (q + len + 2) (out ++ (inp.drop q).take len) (off16 inp (q + len)) ml0 =
        .cont i' o := by
  unfold literal at h
  split at h
  · split at h <;> simp at h
  · rename_i hc
    exact ⟨by omega, by omega, h⟩

/-- `literal` ending the block: the literals reach the input's end and fit. -/
theorem literal_done {inp : List UInt8} {cap q len ml0 : Nat} {out o : List UInt8}
    (h : literal inp cap q out len ml0 = .done o) :
    q + len = inp.length ∧ out.length + len ≤ cap ∧ o = out ++ inp.drop q := by
  unfold literal at h
  split at h
  · split at h
    · rename_i hc
      simp only [Out.done.injEq] at h
      refine ⟨hc.1, hc.2, ?_⟩
      rw [← h, List.take_of_length_le (by simp; omega)]
    · simp at h
  · unfold copyMatch at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h <;> simp at h

theorem token_fields {inp : List UInt8} {i : Nat} : at! inp i / 16 < 16 ∧ at! inp i % 16 < 16 := by
  have : at! inp i < 256 := by simp only [at!]; exact (inp[i]?.getD 0).toNat_lt
  omega

/-- A continuing step consumed one sequence (offset < 65536, match ≥ 4) and copied its match. -/
theorem step_cont {inp : List UInt8} {cap i i' : Nat} {out o : List UInt8}
    (h : step inp cap i out = .cont i' o) :
    ∃ s : Seq, s.off < 65536 ∧ 4 ≤ s.len ∧ inp.drop i = s.bytes ++ inp.drop i' ∧
      Lz4.copy (out ++ s.lits) s.off s.len = some o ∧ i < i' := by
  obtain ⟨hll16, hml16⟩ := token_fields (inp := inp) (i := i)
  unfold step at h
  dsimp only at h
  split at h
  · -- literal length 15 + extension bytes
    rename_i hll
    split at h
    · simp at h
    · rename_i a q hx
      obtain ⟨hd, hL, -, hlt⟩ := ext_bytes hx
      obtain ⟨hroom, hroom', hcm⟩ := literal_cont h
      obtain ⟨m, hm, hmd, hj, -, -, -, hc⟩ := copyMatch_cont hml16 hcm
      have hi : i < inp.length := by omega
      obtain ⟨hb, hoff⟩ := assemble (len := 15 + a) hi (by omega) hm hd (by omega) hmd
      exact ⟨_, hoff, by simp, hb, hc, by omega⟩
  · split at h
    · -- the shortcut
      rename_i hll hsc
      have hi : i < inp.length := by omega
      split at h
      · rename_i hfast
        split at h
        · split at h
          · rename_i o' hc
            simp only [Out.cont.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hb, hoff⟩ := assemble (len := at! inp i / 16) (m := at! inp i % 16)
              (q := i + 1) (i' := i + 1 + at! inp i / 16 + 2) hi (by omega) (by omega)
              (by simp [Lz4.ext, show at! inp i / 16 < 15 by omega]) (by omega)
              (by simp [Lz4.ext, show at! inp i % 16 < 15 by omega])
            exact ⟨_, hoff, by simp, hb, hc, by omega⟩
          · simp at h
        · simp at h
      · obtain ⟨m, hm, hmd, hj, -, -, -, hc⟩ := copyMatch_cont hml16 h
        obtain ⟨hb, hoff⟩ := assemble (len := at! inp i / 16) (q := i + 1) hi (by omega) hm
          (by simp [Lz4.ext, show at! inp i / 16 < 15 by omega]) (by omega) hmd
        exact ⟨_, hoff, by simp, hb, hc, by omega⟩
    · -- the general path
      rename_i hll hsc
      obtain ⟨hroom, hroom', hcm⟩ := literal_cont h
      obtain ⟨m, hm, hmd, hj, -, -, -, hc⟩ := copyMatch_cont hml16 hcm
      have hi : i < inp.length := by omega
      obtain ⟨hb, hoff⟩ := assemble (len := at! inp i / 16) (q := i + 1) hi (by omega) hm
        (by simp [Lz4.ext, show at! inp i / 16 < 15 by omega]) (by omega) hmd
      exact ⟨_, hoff, by simp, hb, hc, by omega⟩

theorem copyMatch_ne_done {inp : List UInt8} {cap j off ml0 : Nat} {out o : List UInt8} :
    copyMatch inp cap j out off ml0 ≠ .done o := by
  unfold copyMatch
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

/-- An ending step read the last literals: a token with literal field `min lits.length 15`,
their extension bytes, the literals up to the input's end. -/
theorem step_done {inp : List UInt8} {cap i : Nat} {out o : List UInt8}
    (h : step inp cap i out = .done o) :
    ∃ lits, ∃ low < 16, inp.drop i = Lz4.head lits low ∧ o = out ++ lits ∧ o.length ≤ cap := by
  obtain ⟨hll16, hml16⟩ := token_fields (inp := inp) (i := i)
  have hlast : ∀ {q len : Nat}, min len 15 = at! inp i / 16 →
      inp.drop (i + 1) = Lz4.ext len ++ inp.drop q → i < inp.length →
      literal inp cap q out len (at! inp i % 16) = .done o →
      ∃ lits, ∃ low < 16, inp.drop i = Lz4.head lits low ∧ o = out ++ lits ∧ o.length ≤ cap := by
    intro q len hm hd hi hl
    obtain ⟨hend, hcap, rfl⟩ := literal_done hl
    have hlen : (inp.drop q).length = len := by simp; omega
    refine ⟨inp.drop q, at! inp i % 16, hml16, ?_, rfl, by simp; omega⟩
    have htok : UInt8.ofNat (16 * min len 15 + at! inp i % 16) = inp[i] := by
      rw [hm, at!_lt hi]
      have : 16 * (inp[i].toNat / 16) + inp[i].toNat % 16 = inp[i].toNat := by omega
      rw [this]; exact UInt8.ofNat_toNat
    rw [drop_cons hi, hd]
    simp only [Lz4.head, hlen, htok, List.cons_append]
  unfold step at h
  dsimp only at h
  split at h
  · split at h
    · simp at h
    · rename_i a q hx
      obtain ⟨hd, hL, -, hlt⟩ := ext_bytes hx
      have hl := h
      unfold literal at hl
      have hi : i < inp.length := by
        split at hl
        · split at hl
          · rename_i hc; omega
          · simp at hl
        · exact absurd hl copyMatch_ne_done
      exact hlast (by omega) hd hi h
  · split at h
    · split at h
      · split at h
        · split at h <;> simp at h
        · simp at h
      · exact absurd h copyMatch_ne_done
    · rename_i hll hsc
      have hl := h
      unfold literal at hl
      have hi : i < inp.length := by
        split at hl
        · split at hl
          · rename_i hc; omega
          · simp at hl
        · exact absurd hl copyMatch_ne_done
      exact hlast (len := at! inp i / 16) (by omega)
        (by simp [Lz4.ext, show at! inp i / 16 < 15 by omega]) hi h

/-- The main loop accepting: the input from `i` is sequences then last literals, decoding from
`out` to the content, which fits. -/
theorem loop_sound {inp : List UInt8} {cap : Nat} :
    ∀ {fuel i : Nat} {out content : List UInt8}, loop inp cap fuel i out = some content →
      content.length ≤ cap ∧ ∃ ss last, (∃ low < 16, inp.drop i = ss.flatMap Seq.bytes ++
        head last low) ∧ (∀ s ∈ ss, s.off < 65536 ∧ 4 ≤ s.len) ∧
        (Lz4.decode ss out).map (· ++ last) = some content := by
  intro fuel
  induction fuel with
  | zero => intro i out content h; simp [loop] at h
  | succ fuel ih =>
    intro i out content h
    unfold loop at h
    split at h
    · rename_i i' o hs
      obtain ⟨s, hoff, hlen, hb, hc, -⟩ := step_cont hs
      obtain ⟨hcap, ss, last, ⟨low, hlow, hd⟩, hss, hdec⟩ := ih h
      refine ⟨hcap, s :: ss, last, ⟨low, hlow, ?_⟩, ?_, ?_⟩
      · rw [hb, hd]; simp
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hoff, hlen⟩
        · exact hss x hx
      · simp only [Lz4.decode, hc, Option.bind_some]; exact hdec
    · rename_i o hs
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨lits, low, hlow, hd, rfl, hcap⟩ := step_done hs
      exact ⟨hcap, [], lits, ⟨low, hlow, by simpa using hd⟩, by simp, by simp [Lz4.decode]⟩
    · simp at h

/-- R3's model half: an accepted block parses (offsets 0 … 65535, no end conditions) to its
decoded content, which fits. -/
theorem decode_sound {inp : List UInt8} {cap : Nat} {content : List UInt8}
    (h : decode inp cap = some content) :
    content.length ≤ cap ∧ ∃ ss last, ParsesAny inp ss last ∧
      (Lz4.decode ss []).map (· ++ last) = some content := by
  unfold decode at h
  split at h
  · split at h
    · rename_i hcap h0
      simp only [Option.some.injEq] at h
      subst h h0
      exact ⟨by simp, [], [], ⟨0, by decide, by decide, by simp⟩, by simp [Lz4.decode]⟩
    · simp at h
  · split at h
    · simp at h
    · obtain ⟨hcap, ss, last, ⟨low, hlow, hd⟩, hss, hdec⟩ := loop_sound h
      exact ⟨hcap, ss, last, ⟨low, hlow, by simpa using hd, hss⟩, hdec⟩

theorem drop_of_drop_append {inp xs ys : List UInt8} {a : Nat} (h : inp.drop a = xs ++ ys) :
    inp.drop (a + xs.length) = ys := by
  rw [← List.drop_drop, h, List.drop_left]

theorem length_ge_of_drop {inp xs : List UInt8} {a : Nat} (h : inp.drop a = xs)
    (hx : 0 < xs.length) : a + xs.length ≤ inp.length := by
  have := congrArg List.length h; simp at this; omega

theorem ext_length (n : Nat) : (Lz4.ext n).length = if n < 15 then 0 else (n - 15) / 255 + 1 := by
  unfold Lz4.ext; split <;> simp

/-- Reading `Lz4.ext n` back from `q` (for `n ≥ 15`), with `L` bytes or more after it. -/
theorem ext_read {inp rest : List UInt8} {L n q : Nat} (hn : 15 ≤ n)
    (hd : inp.drop q = Lz4.ext n ++ rest) (hroom : L ≤ rest.length)
    (hbound : 255 * inp.length < 2 ^ 31) :
    ext inp L inp.length q 0 = some (n - 15, q + (Lz4.ext n).length) := by
  have hk : (Lz4.ext n).length = (n - 15) / 255 + 1 := by rw [ext_length]; simp; omega
  have hlen := length_ge_of_drop hd (by simp; omega)
  simp only [List.length_append] at hlen
  have hr : (n - 15) % 255 < 255 := Nat.mod_lt _ (by decide)
  have h := ext_complete (inp := inp) (L := L) hr ((n - 15) / 255) (fuel := inp.length) (q := q)
    (acc := 0) (rest := rest) (by omega)
    (by simpa [Lz4.ext, show ¬ n < 15 by omega, List.append_assoc] using hd) (by omega)
    (by omega)
  rw [h, hk]
  congr 2; omega

theorem copy_length : ∀ {n : Nat} {out o : List UInt8} {off : Nat},
    Lz4.copy out off n = some o → o.length = out.length + n := by
  intro n
  induction n with
  | zero => intro out o off h; simp [Lz4.copy] at h; subst h; rfl
  | succ n ih =>
    intro out o off h
    unfold Lz4.copy at h
    split at h
    · have := ih h; simp at this; omega
    · simp at h

theorem copy_off {n : Nat} {out o : List UInt8} {off : Nat}
    (h : Lz4.copy out off (n + 1) = some o) : off ≤ out.length := by
  unfold Lz4.copy at h
  split at h
  · assumption
  · simp at h

/-- `copyMatch` on a match the format allows (its extension bytes from `j`, 5 bytes or more
after them), inside the output, with room for it + 5: it continues after the match. -/
theorem copyMatch_complete {inp rest : List UInt8} {cap j off M : Nat} {out o : List UInt8}
    (hd : inp.drop j = Lz4.ext M ++ rest) (hrest : 5 ≤ rest.length)
    (hc : Lz4.copy out off (M + 4) = some o) (hroom5 : o.length + 5 ≤ cap)
    (hbound : 255 * inp.length < 2 ^ 31) :
    copyMatch inp cap j out off (min M 15) = .cont (j + (Lz4.ext M).length) o := by
  have hoff := copy_off (n := M + 3) hc
  have hol := copy_length hc
  unfold copyMatch
  by_cases hM : 15 ≤ M
  · rw [ite_eq_left (by omega), ext_read hM hd (by omega) hbound]
    simp only [Option.map_some]
    rw [show 15 + (M - 15) = M by omega, ite_eq_right (by omega), ite_eq_right (by omega), hc]
  · rw [ite_eq_right (by omega), show min M 15 = M by omega]
    simp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega), hc]
    simp [Lz4.ext, show M < 15 by omega]

theorem off16_of_drop {inp rest : List UInt8} {p off : Nat} (hoff : off < 65536)
    (h : inp.drop p = [UInt8.ofNat off, UInt8.ofNat (off / 256)] ++ rest) :
    off16 inp p = off := by
  have h0 := at!_of_drop (rest := UInt8.ofNat (off / 256) :: rest) (by simpa using h)
  have h1 := at!_of_drop (q := p + 1) (rest := rest) (b := UInt8.ofNat (off / 256))
    (drop_succ_of_drop (by simpa using h))
  simp only [off16, h0, h1]
  simp
  omega

/-- A sequence the format allows passes every check of `step`, given room for its literals + 12
and its match + 5 and 6 or more input bytes after it: the step continues after it, with its match
copied. -/
theorem step_complete {inp rest : List UInt8} {cap i : Nat} {out o : List UInt8} {s : Seq}
    (hd : inp.drop i = s.bytes ++ rest) (hoff : s.off < 65536) (hlen4 : 4 ≤ s.len)
    (hc : Lz4.copy (out ++ s.lits) s.off s.len = some o)
    (hroom : out.length + s.lits.length + 12 ≤ cap) (hroom5 : o.length + 5 ≤ cap)
    (hrest : 6 ≤ rest.length) (hbound : 255 * inp.length < 2 ^ 31) :
    step inp cap i out = .cont (i + s.bytes.length) o := by
  obtain ⟨lits, off, len⟩ := s
  simp only at hoff hlen4 hc hroom
  obtain ⟨M, rfl⟩ : ∃ M, len = M + 4 := ⟨len - 4, by omega⟩
  obtain ⟨L, hL⟩ : ∃ L, lits.length = L := ⟨_, rfl⟩
  have hb : Seq.bytes ⟨lits, off, M + 4⟩ = UInt8.ofNat (16 * min L 15 + min M 15) ::
      (Lz4.ext L ++ (lits ++ ([UInt8.ofNat off, UInt8.ofNat (off / 256)] ++ Lz4.ext M))) := by
    simp [Seq.bytes, head, hL]
  rw [hb] at hd ⊢
  have ht0 : 16 * min L 15 + min M 15 < 256 := by omega
  have hat : at! inp i = 16 * min L 15 + min M 15 := by
    rw [at!_of_drop (by simpa using hd)]; simp; omega
  have hd1 := drop_succ_of_drop (by simpa using hd)
  -- positions: literals at `q`, offset at `q + L`, match extension at `q + L + 2`
  have hdq := drop_of_drop_append (by simpa [List.append_assoc] using hd1)
  have hdo := drop_of_drop_append (a := i + 1 + (Lz4.ext L).length) (by simpa using hdq)
  have hdm := drop_of_drop_append (a := i + 1 + (Lz4.ext L).length + L) (xs :=
    [UInt8.ofNat off, UInt8.ofNat (off / 256)]) (by simpa [hL] using hdo)
  have hoff16 := off16_of_drop hoff (by simpa [hL] using hdo)
  have htake : (inp.drop (i + 1 + (Lz4.ext L).length)).take L = lits := by
    rw [hdq, ← hL, List.take_left]
  have hn := length_ge_of_drop hd1 (by simp)
  simp only [List.length_append, List.length_cons] at hn
  have hlenb : (UInt8.ofNat (16 * min L 15 + min M 15) :: (Lz4.ext L ++ (lits ++
      ([UInt8.ofNat off, UInt8.ofNat (off / 256)] ++ Lz4.ext M)))).length =
      1 + (Lz4.ext L).length + L + 2 + (Lz4.ext M).length := by simp [hL]; omega
  rw [hlenb]
  have hcm := copyMatch_complete (inp := inp) (cap := cap) (out := out ++ lits) (off := off)
    (j := i + 1 + (Lz4.ext L).length + L + 2) (M := M) (by simpa using hdm) (by omega) hc hroom5
    hbound
  have hidx : i + 1 + (Lz4.ext L).length + L + 2 + (Lz4.ext M).length =
      i + (1 + (Lz4.ext L).length + L + 2 + (Lz4.ext M).length) := by omega
  rw [← hidx]
  have hml : (16 * min L 15 + min M 15) % 16 = min M 15 := by omega
  unfold step
  simp only [hat, hml]
  by_cases hLL : 15 ≤ L
  · -- extension bytes for the literal length, then the general path
    have hx := ext_read (L := 15) hLL hd1 (by simp; omega) hbound
    rw [ite_eq_left (by omega), hx]
    simp only
    rw [show 15 + (L - 15) = L by omega]
    unfold literal
    rw [ite_eq_right (by omega), htake, hoff16, hcm]
  · have hext0 : (Lz4.ext L).length = 0 := by simp [ext_length]; omega
    rw [ite_eq_right (by omega)]
    rw [hext0] at htake hoff16 hcm ⊢
    simp only [Nat.add_zero] at htake hoff16 hcm ⊢
    have hll : (16 * min L 15 + min M 15) / 16 = L := by omega
    simp only [hll]
    split
    · -- the shortcut
      rw [htake, hoff16]
      split
      · rename_i hfast
        have hM : min M 15 = M := by omega
        have hext0' : (Lz4.ext M).length = 0 := by simp [ext_length]; omega
        rw [ite_eq_left (by have := copy_off (n := M + 3) hc; simp at this; omega), hM, hc,
          hext0']
      · exact hcm
    · unfold literal
      rw [ite_eq_right (by omega), htake, hoff16, hcm]

/-- The last literals pass `step`: the block ends, the output with them fits. -/
theorem step_complete_last {inp lits : List UInt8} {cap i low : Nat} {out : List UInt8}
    (hd : inp.drop i = Lz4.head lits low) (hlow : low < 16)
    (hcap : out.length + lits.length ≤ cap) (hbound : 255 * inp.length < 2 ^ 31) :
    step inp cap i out = .done (out ++ lits) := by
  obtain ⟨L, hL⟩ : ∃ L, lits.length = L := ⟨_, rfl⟩
  have hd' : inp.drop i = UInt8.ofNat (16 * min L 15 + low) :: (Lz4.ext L ++ lits) := by
    simpa [Lz4.head, hL] using hd
  have hat : at! inp i = 16 * min L 15 + low := by
    rw [at!_of_drop hd']; simp; omega
  have hd1 := drop_succ_of_drop hd'
  have hdq := drop_of_drop_append hd1
  have hn := length_ge_of_drop hd' (by simp)
  have hn' : inp.length = i + 1 + (Lz4.ext L).length + L := by
    have := congrArg List.length hd'; simp [hL] at this; omega
  have hml : (16 * min L 15 + low) % 16 = low := by omega
  have hlitq : inp.drop (i + 1 + (Lz4.ext L).length) = lits := hdq
  unfold step
  simp only [hat, hml]
  by_cases hLL : 15 ≤ L
  · have hx := ext_read (L := 15) hLL hd1 (by omega) hbound
    rw [ite_eq_left (by omega), hx]
    simp only
    rw [show 15 + (L - 15) = L by omega]
    unfold literal
    rw [ite_eq_left (by omega), ite_eq_left (by omega), hlitq, List.take_of_length_le (by omega)]
  · have hext0 : (Lz4.ext L).length = 0 := by simp [ext_length]; omega
    rw [hext0] at hlitq hn'
    simp only [Nat.add_zero] at hlitq hn'
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    unfold literal
    rw [ite_eq_left (by omega), ite_eq_left (by omega), hlitq, List.take_of_length_le (by omega)]

theorem decode_cons {s : Seq} {ss : List Seq} {out o : List UInt8}
    (h : Lz4.decode (s :: ss) out = some o) :
    ∃ o', Lz4.copy (out ++ s.lits) s.off s.len = some o' ∧ Lz4.decode ss o' = some o := by
  simp only [Lz4.decode] at h
  cases hc : Lz4.copy (out ++ s.lits) s.off s.len with
  | none => rw [hc] at h; simp at h
  | some o' => rw [hc] at h; exact ⟨o', rfl, h⟩

theorem decode_length : ∀ {ss : List Seq} {out o : List UInt8},
    Lz4.decode ss out = some o → out.length ≤ o.length := by
  intro ss
  induction ss with
  | nil => intro out o h; simp [Lz4.decode] at h; subst h; exact Nat.le_refl _
  | cons s ss ih =>
    intro out o h
    obtain ⟨o', hc, hd⟩ := decode_cons h
    have := copy_length hc
    have := ih hd
    simp at *; omega

/-- With the end conditions, the output before any remaining sequence ends 12 bytes or more
before the content's end (the last match starts that early). -/
theorem tail_room {last : List UInt8} : ∀ {ss : List Seq} {x o : List UInt8}, ss ≠ [] →
    Lz4.decode ss x = some o → EndOk ss last → x.length + 12 ≤ o.length + last.length := by
  intro ss
  induction ss with
  | nil => intro x o h; exact absurd rfl h
  | cons s ss ih =>
    intro x o _ hd hend
    obtain ⟨o', hc, hd'⟩ := decode_cons hd
    have hl := copy_length hc
    simp only [List.length_append] at hl
    cases ss with
    | nil =>
      simp only [Lz4.decode, Option.some.injEq] at hd'
      subst hd'
      have := (hend s (by simp)).2
      omega
    | cons s' ss' =>
      have hend' : EndOk (s' :: ss') last := by
        intro t ht; exact hend t (by simpa using ht)
      have := ih (by simp) hd' hend'
      omega

/-- The main loop on a parse with the end conditions and room for the content decodes it. -/
theorem loop_complete {inp last : List UInt8} {cap low : Nat} (hlow : low < 16)
    (hbound : 255 * inp.length < 2 ^ 31) :
    ∀ (ss : List Seq) {fuel i : Nat} {out o : List UInt8},
      inp.drop i = ss.flatMap Seq.bytes ++ head last low →
      (∀ s ∈ ss, s.off < 65536 ∧ 4 ≤ s.len) → Lz4.decode ss out = some o → EndOk ss last →
      o.length + last.length ≤ cap → ss.length < fuel →
      loop inp cap fuel i out = some (o ++ last) := by
  intro ss
  induction ss with
  | nil =>
    intro fuel i out o hd _ hdec _ hcap hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [Lz4.decode, Option.some.injEq] at hdec
    subst hdec
    unfold loop
    rw [step_complete_last (by simpa using hd) hlow hcap hbound]
  | cons s ss ih =>
    intro fuel i out o hd hss hdec hend hcap hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨o', hc, hd'⟩ := decode_cons hdec
    have hlen' := copy_length hc
    have hle := decode_length hd'
    have h5 : 5 ≤ last.length := by
      have : ∃ t, (s :: ss).getLast? = some t := ⟨(s :: ss).getLast (by simp),
        List.getLast?_eq_some_getLast _⟩
      obtain ⟨t, ht⟩ := this
      exact (hend t (by simp [ht])).1
    -- the room the decoder's checks need, from the end conditions
    have hroom : (out ++ s.lits).length + 12 ≤ cap ∧ o'.length + 5 ≤ cap := by
      cases ss with
      | nil =>
        simp only [Lz4.decode, Option.some.injEq] at hd'
        subst hd'
        have := (hend s (by simp)).2
        simp only [List.length_append] at hlen' ⊢
        omega
      | cons s' ss' =>
        have hend' : EndOk (s' :: ss') last := by
          intro t ht; exact hend t (by simpa using ht)
        have := tail_room (last := last) (by simp) hd' hend'
        simp only [List.length_append] at hlen' ⊢
        omega
    have hrest : 6 ≤ (ss.flatMap Seq.bytes ++ head last low).length := by
      simp [Lz4.head]; omega
    have hstep := step_complete (rest := ss.flatMap Seq.bytes ++ head last low) (cap := cap)
      (i := i) (out := out) (o := o') (s := s) (by simpa [List.append_assoc] using hd)
      (hss s (by simp)).1 (hss s (by simp)).2 hc (by simpa using hroom.1) hroom.2 hrest hbound
    unfold loop
    rw [hstep]
    simp only
    have hd2 : inp.drop (i + s.bytes.length) = ss.flatMap Seq.bytes ++ head last low :=
      drop_of_drop_append (by simpa [List.append_assoc] using hd)
    have hend' : EndOk ss last := by
      cases ss with
      | nil => intro t ht; simp at ht
      | cons s' ss' => intro t ht; exact hend t (by simpa using ht)
    exact ih hd2 (fun x hx => hss x (by simp [hx])) hd' hend' hcap (by simp at hf; omega)

/-- R2's model half: a valid block whose content fits, with room or the one-byte block `0`,
decodes to its content. -/
theorem decode_complete {inp c : List UInt8} {cap : Nat} (hv : Valid inp c)
    (hcap : c.length ≤ cap) (hroom : 1 ≤ cap ∨ inp = [0])
    (hbound : 255 * inp.length < 2 ^ 31) : decode inp cap = some c := by
  obtain ⟨ss, last, ⟨low, hlow, hb, hss⟩, hdec, hend⟩ := hv
  obtain ⟨o, hd, rfl⟩ : ∃ o, Lz4.decode ss [] = some o ∧ c = o ++ last := by
    cases h : Lz4.decode ss [] with
    | none => rw [h] at hdec; simp at hdec
    | some o => rw [h] at hdec; simp at hdec; exact ⟨o, rfl, hdec.symm⟩
  unfold decode
  by_cases h0 : cap = 0
  · rw [ite_eq_left h0]
    have hi : inp = [0] := by rcases hroom with h | h; omega; exact h
    rw [ite_eq_left hi]
    simp only [List.length_append, h0] at hcap
    have : o = [] ∧ last = [] := ⟨List.eq_nil_of_length_eq_zero (by omega),
      List.eq_nil_of_length_eq_zero (by omega)⟩
    rw [this.1, this.2]
    rfl
  · rw [ite_eq_right h0]
    have hne : inp ≠ [] := by rw [hb]; simp [Lz4.head]
    rw [ite_eq_right hne]
    have hfuel : ss.length < inp.length := by
      have hl : ∀ t : Seq, 3 ≤ t.bytes.length := fun t => by simp [Seq.bytes, Lz4.head]; omega
      have : 3 * ss.length ≤ (ss.flatMap Seq.bytes).length := by
        clear hb hss hdec hend hd
        induction ss with
        | nil => simp
        | cons t ts ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          have := hl t; omega
      have h1 : 1 ≤ (head last low).length := by simp [Lz4.head]
      rw [hb, List.length_append]; omega
    exact loop_complete hlow hbound ss (by simpa using hb) (fun s hs => ⟨(hss s hs).2.1,
      (hss s hs).2.2⟩) hd hend (by simpa using hcap) hfuel

end Subjects.Lz4C.Model
