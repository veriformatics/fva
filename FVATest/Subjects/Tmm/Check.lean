import FVATest.Subjects.Tmm.Rel
import FVA.Spec.Cert
import Mathlib.Data.Nat.Digits.Lemmas

/-! `FactorsDiffer`'s checker, proven sound (certificate convention `R.check`, `R.check_sound`).
The parser may read any spelling: the checker reprints what it read and compares bytes, and a
decimal file has one reading (`decFile_inj`), so "every reading" follows from the one parse. -/

namespace Subjects.Tmm

open FVA.Cert

/-! ## One reading per file -/

theorem digit_toNat (d : Fin 10) : (digit d).toNat = 48 + d.val := by
  simp [digit]; omega

theorem digit_inj {a b : Fin 10} (h : digit a = digit b) : a = b := by
  have := congrArg UInt8.toNat h
  rw [digit_toNat, digit_toNat] at this
  exact Fin.ext (by omega)

theorem decimal_byte {n : Nat} {b : UInt8} (h : b ∈ decimal n) : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  unfold decimal at h
  split at h
  · simp at h; subst h; decide
  · simp only [List.mem_map, List.mem_reverse] at h
    obtain ⟨d, hd, rfl⟩ := h
    have := Nat.digits_lt_base (by norm_num) hd
    simp; omega

/-- Two lists with the same image under a map injective on their elements are equal. -/
theorem map_eq_of_injOn {α β : Type} {f : α → β} {p : α → Prop}
    (hinj : ∀ a b, p a → p b → f a = f b → a = b) :
    ∀ {l l' : List α}, (∀ a ∈ l, p a) → (∀ a ∈ l', p a) → l.map f = l'.map f → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l, b :: l', hl, hl', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hinj a b (hl a (by simp)) (hl' b (by simp)) h.1,
      map_eq_of_injOn hinj (fun x hx => hl x (by simp [hx])) (fun x hx => hl' x (by simp [hx]))
        h.2]

theorem decimal_inj {n m : Nat} (h : decimal n = decimal m) : n = m := by
  have hf : ∀ a b : Nat, a < 10 → b < 10 →
      (fun d => (48 + d).toUInt8) a = (fun d => (48 + d).toUInt8) b → a = b := by
    intro a b ha hb hab
    have := congrArg UInt8.toNat hab
    simp at this; omega
  have hlast : ∀ k, k ≠ 0 → (Nat.digits 10 k).reverse.head? ≠ some 0 := by
    intro k hk h0
    rw [List.head?_reverse] at h0
    exact Nat.getLast_digit_ne_zero 10 hk (by
      rw [List.getLast?_eq_some_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hk)] at h0
      exact Option.some.inj h0)
  unfold decimal at h
  by_cases hn : n = 0 <;> by_cases hm : m = 0
  · rw [hn, hm]
  · simp only [hn, hm, ↓reduceIte] at h
    exfalso
    have := map_eq_of_injOn (p := (· < 10)) hf (l := [0]) (l' := (Nat.digits 10 m).reverse)
      (by simp) (fun a ha => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp ha))
      (by simpa using h)
    exact hlast m hm (by rw [← this]; rfl)
  · simp only [hn, hm, ↓reduceIte] at h
    exfalso
    have := map_eq_of_injOn (p := (· < 10)) hf (l := (Nat.digits 10 n).reverse) (l' := [0])
      (fun a ha => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp ha)) (by simp)
      (by simpa using h)
    exact hlast n hn (by rw [this]; rfl)
  · simp only [hn, hm, ↓reduceIte] at h
    have hr := map_eq_of_injOn (p := (· < 10)) hf
      (fun a ha => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp ha))
      (fun a ha => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp ha)) h
    rw [← Nat.ofDigits_digits 10 n, ← Nat.ofDigits_digits 10 m, ← List.reverse_reverse
      (Nat.digits 10 n), hr, List.reverse_reverse]

/-- Splitting at the first occurrence of a byte that neither prefix contains is unique. -/
theorem split_first {x : UInt8} :
    ∀ {a b r r' : List UInt8}, x ∉ a → x ∉ b → a ++ x :: r = b ++ x :: r' → a = b ∧ r = r'
  | [], [], _, _, _, _, h => by simpa using h
  | [], c :: b, _, _, _, hb, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hb
  | c :: a, [], _, _, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) ha
  | c :: a, d :: b, _, _, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨hab, hr⟩ := split_first (fun hx => ha (List.mem_cons_of_mem _ hx))
      (fun hx => hb (List.mem_cons_of_mem _ hx)) h
    exact ⟨by rw [hab], hr⟩

theorem decLine_inj {n n' : Nat} {f f' : List (Fin 10)} {r r' : List UInt8}
    (h : decLine n f ++ r = decLine n' f' ++ r') : n = n' ∧ f = f' ∧ r = r' := by
  have hno : ∀ k (b : UInt8), b ∈ decimal k → b.toNat ≠ 46 ∧ b.toNat ≠ 10 := by
    intro k b hb
    have := decimal_byte hb; omega
  have hdig : ∀ (g : List (Fin 10)) (b : UInt8), b ∈ g.map digit → b.toNat ≠ 10 := by
    intro g b hb
    simp only [List.mem_map] at hb
    obtain ⟨d, -, rfl⟩ := hb
    rw [digit_toNat]; omega
  simp only [decLine, List.append_assoc, List.cons_append] at h
  obtain ⟨hn, h⟩ := split_first (x := 46) (fun hx => (hno n _ hx).1 rfl)
    (fun hx => (hno n' _ hx).1 rfl) h
  obtain ⟨hf, hr⟩ := split_first (x := 10) (fun hx => hdig f _ hx rfl)
    (fun hx => hdig f' _ hx rfl) (by simpa only [List.append_assoc, List.singleton_append] using h)
  refine ⟨decimal_inj hn, ?_, hr⟩
  exact map_eq_of_injOn (p := fun _ => True) (fun a b _ _ => digit_inj) (by simp) (by simp) hf

theorem decFile_inj : ∀ {xs ys : List (Nat × List (Fin 10))}, decFile xs = decFile ys → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by simp [decFile, decLine] at h
  | x :: xs, [], h => by simp [decFile, decLine] at h
  | x :: xs, y :: ys, h => by
    simp only [decFile, List.flatMap_cons] at h
    obtain ⟨h1, h2, h3⟩ := decLine_inj h
    rw [decFile_inj (xs := xs) (ys := ys) h3, show x = y from Prod.ext h1 h2]

/-! ## The checker -/

/-- A digit byte's value. -/
def digitOf (b : UInt8) : Option (Fin 10) :=
  if h : 48 ≤ b.toNat ∧ b.toNat < 58 then some ⟨b.toNat - 48, by omega⟩ else none

/-- Decimal digits as a number. -/
def natOf (bs : List UInt8) : Option Nat :=
  bs.foldlM (fun acc b => (digitOf b).map fun d => acc * 10 + d.val) 0

/-- The lines of `bs` (each ended by a line feed; trailing bytes without one dropped). -/
def lines : List UInt8 → List UInt8 → List (List UInt8)
  | [], _ => []
  | b :: bs, cur => if b = 10 then cur.reverse :: lines bs [] else lines bs (b :: cur)

/-- One line read as integer part, `.`, fraction digits. -/
def parseLine (l : List UInt8) : Option (Nat × List (Fin 10)) :=
  match l.span (· ≠ 46) with
  | (int, _ :: frac) => do
    let n ← natOf int
    let f ← frac.mapM digitOf
    pure (n, f)
  | _ => none

/-- A file read as decimal lines. -/
def parseDec (bs : List UInt8) : Option (List (Nat × List (Fin 10))) := (lines bs []).mapM parseLine

/-- Both files are decimal files whose readings differ somewhere by more than 10⁻¹⁰. -/
def FactorsDiffer.check (e r : Blob) : Bool :=
  match parseDec e.data, parseDec r.data with
  | some xs, some ys =>
    decFile xs == e.data && decFile ys == r.data &&
      (xs.zip ys).any fun p => decide (1 / 10 ^ 10 < |decVal p.1 - decVal p.2|)
  | _, _ => false

theorem FactorsDiffer.check_sound (e r : Blob) (h : FactorsDiffer.check e r = true) :
    Accepted FactorsDiffer e r := by
  unfold FactorsDiffer.check at h
  split at h
  · rename_i xs ys _ _
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨he, hr⟩, p, hp, hd⟩ := h
    refine ⟨⟨xs, ys, he.symm, hr.symm⟩, fun xs' ys' he' hr' => ?_⟩
    obtain rfl := decFile_inj (he.trans he')
    obtain rfl := decFile_inj (hr.trans hr')
    exact ⟨p, hp, hd⟩
  · simp at h

end Subjects.Tmm
