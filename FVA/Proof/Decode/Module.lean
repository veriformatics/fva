import FVA.Proof.Decode.Items

/-!
# Module decoding is sound and complete (T1–T3)

`decode (pack b) b.length = .ok m ↔ ModuleB m b`. The decoder reads custom sections greedily
before each slot of `slotIds`; `Layout` restates `ModuleB`'s flat section sequence slot by slot,
so both directions are walks over the slot list.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm FVA.Wasm.Binary

/-! ## Custom sections -/

/-- The decoder's custom-section content step: a name, the rest ignored. -/
def customBody (v n : Nat) : Res Unit := (name v n).bind fun _ _ _ => .ok () 0 0

theorem customs_eq_succ (F v n : Nat) : customs (F + 1) v n =
    bif Nat.beq n 0 || !Nat.beq (Nat.land v 255) 0 then .ok () v n else
    (byte v n).bind fun _ v n => (u32 v n).bind fun k v n =>
    (sub k customBody v n).bind fun _ v n => customs F v n := rfl

theorem sub_customBody_sound {k : Nat} {bs : List UInt8} {u : Unit} {v n : Nat}
    (h : sub k customBody (pack bs) bs.length = .ok u v n) :
    ∃ cont rest, bs = cont ++ rest ∧ cont.length = k ∧
      (∃ (nm : String) (nb r : List UInt8), Name nm nb ∧ cont = nb ++ r) ∧
      v = pack rest ∧ n = rest.length := by
  simp only [sub] at h
  cases hk : Nat.blt bs.length k
  · have hle := blt_false.1 hk
    have hlen : (bs.take k).length = k := List.length_take_of_le hle
    simp only [hk, Bool.cond_false, land_pack_take hle] at h
    generalize hr : customBody (pack (bs.take k)) k = r at h
    cases r with
    | bad => simp at h
    | unsup => simp at h
    | ok u' v' n' =>
      cases n' with
      | succ => simp at h
      | zero =>
        simp only [Res.ok.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        obtain ⟨s, v₁, n₁, hn, -⟩ := Res.bind_eq_ok.1 hr
        obtain ⟨nb, r, hsplit, hname, -, -⟩ := name_parses.sound_of_len hlen hn
        exact ⟨bs.take k, bs.drop k, (List.take_append_drop k bs).symm, hlen,
          ⟨s, nb, r, hname, hsplit⟩, shiftRight_pack_drop hle, by simp [Nat.sub_eq]⟩
  · simp [hk] at h

theorem sub_customBody_complete {nm : String} {nb r rest : List UInt8} (hn : Name nm nb) :
    sub (nb ++ r).length customBody (pack (nb ++ r ++ rest)) (nb ++ r ++ rest).length =
      .ok () (pack rest) rest.length := by
  have hk : Nat.blt (nb ++ r ++ rest).length (nb ++ r).length = false := blt_false.2 (by simp)
  have hin : customBody (pack (nb ++ r)) (nb ++ r).length = .ok () 0 0 := by
    simp only [customBody, name_parses.complete r hn, Res.bind_ok]
  simp only [sub, hk, Bool.cond_false, land_pack_append, hin, shiftRight_pack_append]
  simp only [Nat.sub_eq, List.length_append, Res.ok.injEq, true_and]
  omega

theorem Res.bind_congr {α β : Type} {x : Res α} {f g : α → Nat → Nat → Res β}
    (h : ∀ a v n, x = .ok a v n → f a v n = g a v n) : x.bind f = x.bind g := by
  cases x with
  | ok a v n => exact h a v n rfl
  | bad => rfl
  | unsup => rfl

/-- The next byte is not a custom section id (or the input has ended). -/
def NoCustom (bs : List UInt8) : Prop := ∀ b rest, bs = b :: rest → b ≠ 0

theorem CustomB.head {b : List UInt8} (h : CustomB b) : ∃ rest, b = 0 :: rest := by
  obtain ⟨_, _, _, sb, cont, -, -, rfl⟩ := h
  exact ⟨_, rfl⟩

theorem customs_sound (F : Nat) : ∀ {bs : List UInt8} {u : Unit} {v n : Nat},
    customs F (pack bs) bs.length = .ok u v n →
      ∃ c rest, bs = c ++ rest ∧ CustomsB c ∧ v = pack rest ∧ n = rest.length := by
  induction F with
  | zero =>
    intro bs u v n h
    simp only [customs, Res.ok.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨[], bs, rfl, .nil, rfl, rfl⟩
  | succ F ih =>
    intro bs u v n h
    rw [customs_eq_succ] at h
    cases hc : (Nat.beq bs.length 0 || !Nat.beq (Nat.land (pack bs) 255) 0)
    · simp only [hc, Bool.cond_false] at h
      obtain ⟨_, v₁, n₁, h₁, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨_, r₁, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound h₁
      obtain ⟨k, v₂, n₂, h₂, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨sb, r₂, rfl, hsb, rfl, rfl⟩ := u32_parses.sound h₂
      obtain ⟨_, v₃, n₃, h₃, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨cont, r₃, rfl, hlen, ⟨nm, nb, r, hname, rfl⟩, rfl, rfl⟩ := sub_customBody_sound h₃
      obtain ⟨c, rest, rfl, hcs, rfl, rfl⟩ := ih h
      have hb : b = 0 := by
        simp only [List.cons_append, List.nil_append, land_pack_cons, Bool.or_eq_false_iff,
          Bool.not_eq_false'] at hc
        exact UInt8.toNat_inj.1 (beq_true.1 hc.2)
      subst hb
      refine ⟨(0 :: sb ++ (nb ++ r)) ++ c, rest, by simp, .cons ?_ hcs, rfl, rfl⟩
      exact ⟨nm, nb, r, sb, nb ++ r, ⟨hname, rfl⟩, hlen ▸ hsb, rfl⟩
    · simp only [hc, Bool.cond_true, Res.ok.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨[], bs, rfl, .nil, rfl, rfl⟩

/-- Fuel beyond the input length does not change `customs`. -/
theorem customs_fuel (F : Nat) : ∀ (G : Nat) (bs : List UInt8), bs.length ≤ F → bs.length ≤ G →
    customs F (pack bs) bs.length = customs G (pack bs) bs.length := by
  induction F with
  | zero =>
    intro G bs hF hG
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    cases G <;> rfl
  | succ F ih =>
    intro G bs hF hG
    cases bs with
    | nil => cases G <;> rfl
    | cons b bs =>
      obtain ⟨G, rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by simp at hG; omega⟩
      rw [customs_eq_succ, customs_eq_succ]
      congr 1
      apply Res.bind_congr; intro _ v₁ n₁ h₁
      obtain ⟨_, r₁, e₁, ⟨_, -, rfl⟩, rfl, rfl⟩ := byte_parses.sound h₁
      apply Res.bind_congr; intro k v₂ n₂ h₂
      obtain ⟨_, r₂, e₂, -, rfl, rfl⟩ := u32_parses.sound h₂
      apply Res.bind_congr; intro _ v₃ n₃ h₃
      obtain ⟨_, r₃, e₃, -, -, rfl, rfl⟩ := sub_customBody_sound h₃
      have l₁ := congrArg List.length e₁
      have l₂ := congrArg List.length e₂
      have l₃ := congrArg List.length e₃
      simp only [List.length_append, List.length_cons] at l₁ l₂ l₃ hF hG
      exact ih G r₃ (by omega) (by omega)

/-- Reading a run of custom sections leaves `customs` on the rest. -/
theorem customs_append {c : List UInt8} (hc : CustomsB c) : ∀ (Y : List UInt8) (F : Nat),
    (c ++ Y).length ≤ F →
      customs F (pack (c ++ Y)) (c ++ Y).length = customs Y.length (pack Y) Y.length := by
  induction hc with
  | nil => intro Y F hF; exact customs_fuel F Y.length Y hF (Nat.le_refl _)
  | @cons b₁ b₂ h₁ _ ih =>
    intro Y F hF
    obtain ⟨nm, nb, r, sb, cont, ⟨hname, rfl⟩, hsb, rfl⟩ := h₁
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    rw [customs_eq_succ]
    have hc : (Nat.beq (0 :: (sb ++ (nb ++ r ++ (b₂ ++ Y)))).length 0 ||
        !Nat.beq (Nat.land (pack (0 :: (sb ++ (nb ++ r ++ (b₂ ++ Y))))) 255) 0) = false := by
      rw [land_pack_cons]; simp only [Bool.or_eq_false_iff]; exact ⟨beq_false.2 (by simp), rfl⟩
    simp only [List.cons_append, List.append_assoc] at hc ⊢
    rw [hc, Bool.cond_false]
    simp only [byte, List.length_cons, land_pack_cons, shiftRight_pack_cons, Res.bind_ok]
    have hu := u32_parses.complete (nb ++ r ++ (b₂ ++ Y)) hsb
    simp only [List.append_assoc] at hu
    rw [hu, Res.bind_ok]
    have hs := sub_customBody_complete (rest := b₂ ++ Y) (r := r) hname
    simp only [List.append_assoc] at hs
    rw [hs, Res.bind_ok]
    exact ih Y F (by simp at hF ⊢; omega)

/-- A maximal run of custom sections is read completely. -/
theorem customs_complete {c rest : List UInt8} (hc : CustomsB c) (hr : NoCustom rest) {F : Nat}
    (hF : (c ++ rest).length ≤ F) :
    customs F (pack (c ++ rest)) (c ++ rest).length = .ok () (pack rest) rest.length := by
  rw [customs_append hc rest F hF]
  cases rest with
  | nil => rfl
  | cons b rest =>
    have hb := hr b rest rfl
    rw [List.length_cons, customs_eq_succ]
    have : (Nat.beq (rest.length + 1) 0 ||
        !Nat.beq (Nat.land (pack (b :: rest)) 255) 0) = true := by
      simp only [land_pack_cons]
      have : b.toNat ≠ 0 := fun h => hb (UInt8.toNat_inj.1 h)
      simp [beq_false.2 this]
    rw [this, Bool.cond_true]

/-! ## Sections -/

/-- What an optional section's content `cont` adds to the accumulator, per the spec. -/
def IntoB : Nat → Acc → List UInt8 → Acc → Prop
  | 1, a, cont, a' => ∃ xs, Vec FuncTypeB xs cont ∧ a' = { a with m := { a.m with types := xs } }
  | 2, a, cont, a' => ∃ xs, Vec ImportB xs cont ∧ a' = { a with m := { a.m with imports := xs } }
  | 3, a, cont, a' => ∃ xs, Vec IdxB xs cont ∧ a' = { a with typeIdxs := xs }
  | 4, a, cont, a' => ∃ xs, Vec TableTypeB xs cont ∧ a' = { a with m := { a.m with tables := xs } }
  | 5, a, cont, a' => ∃ xs, Vec LimitsB xs cont ∧ a' = { a with m := { a.m with mems := xs } }
  | 6, a, cont, a' => ∃ xs, Vec GlobalB xs cont ∧ a' = { a with m := { a.m with globals := xs } }
  | 7, a, cont, a' => ∃ xs, Vec ExportB xs cont ∧ a' = { a with m := { a.m with exports := xs } }
  | 8, a, cont, a' => ∃ x, IdxB x cont ∧ a' = { a with m := { a.m with start := some x } }
  | 9, a, cont, a' => ∃ xs, Vec ElemB xs cont ∧ a' = { a with m := { a.m with elems := xs } }
  | 12, a, cont, a' => ∃ x, ULeb 32 x cont ∧ a' = { a with dataCount := some x }
  | 10, a, cont, a' => ∃ xs, Vec CodeB xs cont ∧ a' = { a with codes := xs }
  | 11, a, cont, a' => ∃ xs, Vec DataB xs cont ∧ a' = { a with m := { a.m with datas := xs } }
  | _, _, _, _ => False

/-- A vector section's content decoder parses `Vec R` and stores the vector with `f`. -/
theorem vecInto_parses {α : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) (hne : ∀ a bs, R a bs → bs ≠ []) (f : List α → Acc) :
    Parses (fun v n => (vec p v n).bind fun xs v n => .ok (f xs) v n)
      (fun a' cont => ∃ xs, Vec R xs cont ∧ a' = f xs) :=
  ((vec_parses hp hne).bind fun xs => pure_parses (f xs)).congr fun a' cont => by
    constructor
    · rintro ⟨xs, b₁, _, hv, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨xs, by simpa using hv, rfl⟩
    · rintro ⟨xs, hv, rfl⟩
      exact ⟨xs, cont, [], hv, ⟨rfl, rfl⟩, by simp⟩

/-- A single-value section's content decoder (`u32`) stores the value with `f`. -/
theorem u32Into_parses (f : Nat → Acc) :
    Parses (fun v n => (u32 v n).bind fun x v n => .ok (f x) v n)
      (fun a' cont => ∃ x, ULeb 32 x cont ∧ a' = f x) :=
  (u32_parses.bind fun x => pure_parses (f x)).congr fun a' cont => by
    constructor
    · rintro ⟨x, b₁, _, hu, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨x, by simpa using hu, rfl⟩
    · rintro ⟨x, hu, rfl⟩
      exact ⟨x, cont, [], hu, ⟨rfl, rfl⟩, by simp⟩

theorem sectionInto_parses (a : Acc) {id : Nat} (hid : id ∈ slotIds) :
    Parses (sectionInto id a) (fun a' cont => IntoB id a cont a') := by
  simp only [slotIds, List.mem_cons, List.mem_nil_iff, or_false] at hid
  rcases hid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vecInto_parses funcType_parses (fun _ _ h => FuncTypeB.ne_nil h) _
  · exact vecInto_parses import_parses (fun _ _ h => ImportB.ne_nil h) _
  · exact vecInto_parses u32_parses (fun _ _ h => ULeb.ne_nil h) _
  · exact vecInto_parses tableType_parses (fun _ _ h => TableTypeB.ne_nil h) _
  · exact vecInto_parses limits_parses (fun _ _ h => LimitsB.ne_nil h) _
  · exact vecInto_parses global_parses (fun _ _ h => GlobalB.ne_nil h) _
  · exact vecInto_parses export_parses (fun _ _ h => ExportB.ne_nil h) _
  · exact u32Into_parses _
  · exact vecInto_parses elem_parses (fun _ _ h => ElemB.ne_nil h) _
  · exact u32Into_parses _
  · exact vecInto_parses code_parses (fun _ _ h => CodeB.ne_nil h) _
  · exact vecInto_parses data_parses (fun _ _ h => DataB.ne_nil h) _

/-- An optional section slot: absent, or the section `id` whose content adds to the
accumulator. -/
def SlotB (id : Nat) (a : Acc) (s : List UInt8) (a' : Acc) : Prop :=
  (s = [] ∧ a' = a) ∨
    ∃ sb cont, s = UInt8.ofNat id :: sb ++ cont ∧ ULeb 32 cont.length sb ∧ IntoB id a cont a'

/-- The section slots `ids` in order, each after custom sections, then trailing custom
sections: `ModuleB`'s section sequence, slot by slot. -/
def Layout : List Nat → Acc → List UInt8 → Acc → Prop
  | [], a, bs, a' => CustomsB bs ∧ a' = a
  | id :: ids, a, bs, a' => ∃ c s rest a₁,
      CustomsB c ∧ SlotB id a s a₁ ∧ Layout ids a₁ rest a' ∧ bs = c ++ s ++ rest

theorem slots_cons (id : Nat) (ids : List Nat) (a : Acc) (v n : Nat) :
    slots (id :: ids) a v n = (customs n v n).bind fun _ v n =>
      bif !Nat.beq n 0 && Nat.beq (Nat.land v 255) id then
        (byte v n).bind fun _ v n => (u32 v n).bind fun k v n =>
        (sub k (sectionInto id a) v n).bind fun a v n => slots ids a v n
      else slots ids a v n := rfl

theorem slots_sound : ∀ {ids : List Nat}, (∀ id ∈ ids, id ∈ slotIds) →
    ∀ {a a' : Acc} {bs : List UInt8} {v n : Nat}, slots ids a (pack bs) bs.length = .ok a' v n →
      ∃ pre rest, bs = pre ++ rest ∧ Layout ids a pre a' ∧ v = pack rest ∧ n = rest.length
  | [], _, a, a', bs, v, n, h => by
    obtain ⟨_, v₁, n₁, h₁, h₂⟩ := Res.bind_eq_ok.1 h
    obtain ⟨c, rest, rfl, hc, rfl, rfl⟩ := customs_sound _ h₁
    simp only [Res.ok.injEq] at h₂
    obtain ⟨rfl, rfl, rfl⟩ := h₂
    exact ⟨c, rest, rfl, ⟨hc, rfl⟩, rfl, rfl⟩
  | id :: ids, hids, a, a', bs, v, n, h => by
    rw [slots_cons] at h
    obtain ⟨_, v₁, n₁, h₁, h₂⟩ := Res.bind_eq_ok.1 h
    obtain ⟨c, r₁, rfl, hc, rfl, rfl⟩ := customs_sound _ h₁
    have hid := hids id (List.mem_cons_self ..)
    have hrec := @slots_sound ids (fun i hi => hids i (List.mem_cons_of_mem _ hi))
    cases hb : (!Nat.beq r₁.length 0 && Nat.beq (Nat.land (pack r₁) 255) id)
    · simp only [hb, Bool.cond_false] at h₂
      obtain ⟨pre, rest, rfl, hl, rfl, rfl⟩ := hrec h₂
      exact ⟨c ++ pre, rest, by simp, ⟨c, [], pre, a, hc, .inl ⟨rfl, rfl⟩, hl, by simp⟩, rfl, rfl⟩
    · simp only [hb, Bool.cond_true] at h₂
      obtain ⟨_, v₂, n₂, h₃, h₄⟩ := Res.bind_eq_ok.1 h₂
      obtain ⟨_, r₂, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound h₃
      obtain ⟨k, v₃, n₃, h₅, h₆⟩ := Res.bind_eq_ok.1 h₄
      obtain ⟨sb, r₃, rfl, hsb, rfl, rfl⟩ := u32_parses.sound h₅
      obtain ⟨a₁, v₄, n₄, h₇, h₈⟩ := Res.bind_eq_ok.1 h₆
      obtain ⟨cont, r₄, rfl, ⟨hlen, hinto⟩, rfl, rfl⟩ :=
        (sub_parses (sectionInto_parses a hid) k).sound h₇
      obtain ⟨pre, rest, rfl, hl, rfl, rfl⟩ := hrec h₈
      have hbid : b = UInt8.ofNat id := by
        simp only [List.cons_append, List.nil_append, land_pack_cons, Bool.and_eq_true,
          Bool.not_eq_true', beq_true] at hb
        rw [← hb.2, UInt8.ofNat_toNat]
      subst hbid
      exact ⟨c ++ (UInt8.ofNat id :: sb ++ cont) ++ pre, rest, by simp,
        ⟨c, UInt8.ofNat id :: sb ++ cont, pre, a₁, hc, .inr ⟨sb, cont, rfl, hlen ▸ hsb, hinto⟩,
          hl, rfl⟩, rfl, rfl⟩

theorem _root_.FVA.Wasm.Binary.CustomsB.append {c c' : List UInt8} (h : CustomsB c)
    (h' : CustomsB c') :
    CustomsB (c ++ c') := by
  induction h with
  | nil => simpa using h'
  | cons h₁ _ ih => simpa using CustomsB.cons h₁ ih

/-- Leading custom sections do not change what `slots` decodes. -/
theorem slots_absorb {cs : List UInt8} (hcs : CustomsB cs) (ids : List Nat) (a : Acc)
    (Y : List UInt8) :
    slots ids a (pack (cs ++ Y)) (cs ++ Y).length = slots ids a (pack Y) Y.length := by
  cases ids with
  | nil => simp only [slots, customs_append hcs Y _ (Nat.le_refl _)]
  | cons id ids => simp only [slots_cons, customs_append hcs Y _ (Nat.le_refl _)]

theorem slotIds_pos {id : Nat} (h : id ∈ slotIds) : 0 < id ∧ id < 256 := by
  simp only [slotIds, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- After its leading custom sections, a layout starts with a present slot's id, or is empty. -/
theorem Layout.head : ∀ {ids : List Nat} {a : Acc} {bs : List UInt8} {a' : Acc},
    Layout ids a bs a' → ∃ c X, bs = c ++ X ∧ CustomsB c ∧
      (X = [] ∨ ∃ id ∈ ids, ∃ r, X = UInt8.ofNat id :: r)
  | [], _, bs, _, h => ⟨bs, [], by simp, h.1, .inl rfl⟩
  | id :: ids, _, _, _, ⟨c, s, rest, a₁, hc, hs, hl, e⟩ => by
    subst e
    rcases hs with ⟨rfl, rfl⟩ | ⟨sb, cont, rfl, -, -⟩
    · obtain ⟨c', X, rfl, hc', hX⟩ := Layout.head hl
      refine ⟨c ++ c', X, by simp, hc.append hc', ?_⟩
      rcases hX with hX | ⟨id', hid', r, hX⟩
      · exact .inl hX
      · exact .inr ⟨id', List.mem_cons_of_mem _ hid', r, hX⟩
    · exact ⟨c, UInt8.ofNat id :: sb ++ cont ++ rest, by simp, hc,
        .inr ⟨id, List.mem_cons_self .., sb ++ cont ++ rest, by simp⟩⟩

theorem toNat_ofNat_slot {id : Nat} (h : id ∈ slotIds) : (UInt8.ofNat id).toNat = id :=
  UInt8.toNat_ofNat_of_lt' (by have := (slotIds_pos h).2; simp [UInt8.size]; omega)

theorem slots_complete : ∀ {ids : List Nat}, (∀ id ∈ ids, id ∈ slotIds) → ids.Nodup →
    ∀ {a : Acc} {bs : List UInt8} {a' : Acc}, Layout ids a bs a' →
      ∀ {pre : List UInt8}, CustomsB pre →
        slots ids a (pack (pre ++ bs)) (pre ++ bs).length = .ok a' 0 0
  | [], _, _, a, bs, a', ⟨hbs, ha⟩, pre, hpre => by
    subst ha
    have := customs_complete (hpre.append hbs) (rest := []) (fun _ _ h => by cases h)
      (Nat.le_refl _)
    simp only [List.append_nil] at this
    simp only [slots, this, Res.bind_ok]; rfl
  | id :: ids, hids, hnd, a, _, a', ⟨c, s, rest, a₁, hc, hs, hl, rfl⟩, pre, hpre => by
    have hid := hids id (List.mem_cons_self ..)
    have hids' : ∀ i ∈ ids, i ∈ slotIds := fun i hi => hids i (List.mem_cons_of_mem _ hi)
    have hnd' := (List.nodup_cons.1 hnd)
    rw [slots_cons]
    rcases hs with ⟨rfl, rfl⟩ | ⟨sb, cont, rfl, hsb, hinto⟩
    · obtain ⟨c', X, rfl, hc', hX⟩ := Layout.head hl
      have hcus := customs_complete (c := pre ++ c ++ c') (rest := X) ((hpre.append hc).append hc')
        (by
          intro b r e
          rcases hX with rfl | ⟨id', hid', r', rfl⟩
          · cases e
          · cases e; intro h0
            have := toNat_ofNat_slot (hids' id' hid')
            rw [h0] at this; exact absurd this.symm (Nat.ne_of_gt (slotIds_pos (hids' id' hid')).1))
        (Nat.le_refl _)
      simp only [List.append_assoc, List.nil_append] at hcus ⊢
      rw [hcus, Res.bind_ok]
      have hb : (!Nat.beq X.length 0 && Nat.beq (Nat.land (pack X) 255) id) = false := by
        rcases hX with rfl | ⟨id', hid', r', rfl⟩
        · rfl
        · rw [land_pack_cons, toNat_ofNat_slot (hids' id' hid')]
          have : id' ≠ id := fun e => hnd'.1 (e ▸ hid')
          simp [beq_false.2 this]
      rw [hb, Bool.cond_false]
      have := slots_complete hids' hnd'.2 hl (pre := pre ++ c) (hpre.append hc)
      rw [← this, ← slots_absorb ((hpre.append hc).append hc') ids _ X]
      simp only [List.append_assoc]
    · have hcus := customs_complete (c := pre ++ c) (rest := UInt8.ofNat id :: sb ++ cont ++ rest)
        (hpre.append hc)
        (by
          intro b r e; cases e; intro h0
          have := toNat_ofNat_slot hid
          rw [h0] at this; exact absurd this.symm (Nat.ne_of_gt (slotIds_pos hid).1))
        (Nat.le_refl _)
      simp only [List.append_assoc, List.cons_append] at hcus ⊢
      rw [hcus, Res.bind_ok]
      have hb : (!Nat.beq (UInt8.ofNat id :: (sb ++ (cont ++ rest))).length 0 &&
          Nat.beq (Nat.land (pack (UInt8.ofNat id :: (sb ++ (cont ++ rest)))) 255) id) = true := by
        rw [land_pack_cons, toNat_ofNat_slot hid]; simp only [Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨beq_false.2 (by simp), beq_true.2 rfl⟩
      rw [hb, Bool.cond_true]
      simp only [byte, List.length_cons, land_pack_cons, shiftRight_pack_cons, Res.bind_ok]
      have hu := u32_parses.complete (cont ++ rest) hsb
      rw [hu, Res.bind_ok]
      have hsub := (sub_parses (sectionInto_parses a hid) cont.length).complete rest ⟨rfl, hinto⟩
      rw [hsub, Res.bind_ok]
      have := slots_complete hids' hnd'.2 hl (pre := []) .nil
      simpa using this

/-! ## Cross-section checks -/

theorem usesData_iff_all :
    (∀ i : Instr, usesData i = true ↔ UsesData i) ∧
      (∀ is : List Instr, usesDataList is = true ↔ UsesDataS is) := by
  have hi : ∀ i : Instr, usesData i = true ↔ UsesData i := by
    intro i
    induction i using Instr.rec (motive_2 := fun is => usesDataList is = true ↔ UsesDataS is) with
    | nil => simp only [usesDataList, Bool.false_eq_true, false_iff]; intro h; cases h
    | cons i is ih₁ ih₂ =>
      simp only [usesDataList, Bool.or_eq_true, ih₁, ih₂]
      constructor
      · rintro (h | h)
        · exact .head h
        · exact .tail h
      · intro h; cases h with | head h => exact .inl h | tail h => exact .inr h
    | block bt b ih =>
      simp only [usesData, ih]; exact ⟨.block, fun h => by cases h; assumption⟩
    | loop bt b ih =>
      simp only [usesData, ih]; exact ⟨.loop, fun h => by cases h; assumption⟩
    | if_ bt t e ih₁ ih₂ =>
      simp only [usesData, Bool.or_eq_true, ih₁, ih₂]
      constructor
      · rintro (h | h)
        · exact .thn h
        · exact .els h
      · intro h; cases h with | thn h => exact .inl h | els h => exact .inr h
    | memoryInit x => simp only [usesData]; exact ⟨fun _ => .init x, fun _ => trivial⟩
    | dataDrop x => simp only [usesData]; exact ⟨fun _ => .drop x, fun _ => trivial⟩
    | _ => simp only [usesData]; constructor <;> intro h <;> cases h
  refine ⟨hi, fun is => ?_⟩
  induction is with
  | nil => simp only [usesDataList, Bool.false_eq_true, false_iff]; intro h; cases h
  | cons i is ih =>
    simp only [usesDataList, Bool.or_eq_true, hi, ih]
    constructor
    · rintro (h | h)
      · exact .head h
      · exact .tail h
    · intro h; cases h with | head h => exact .inl h | tail h => exact .inr h

theorem usesDataList_iff (is : List Instr) : usesDataList is = true ↔ UsesDataS is :=
  usesData_iff_all.2 is

/-! ## Slots and accumulator fields -/

theorem slotB_vec {k : Nat} {α : Type} {R : α → List UInt8 → Prop} {get : Acc → List α}
    {set : Acc → List α → Acc}
    (hinto : ∀ a cont a₁, IntoB k a cont a₁ ↔ ∃ xs, Vec R xs cont ∧ a₁ = set a xs)
    (hset : ∀ a, get a = [] → set a [] = a) {a : Acc} {s : List UInt8} {a₁ : Acc}
    (h : SlotB k a s a₁) (h0 : get a = []) :
    ∃ xs, VecSecB (UInt8.ofNat k) R xs s ∧ a₁ = set a xs := by
  rcases h with ⟨rfl, rfl⟩ | ⟨sb, cont, rfl, hsb, hi⟩
  · exact ⟨[], .inl ⟨rfl, rfl⟩, (hset _ h0).symm⟩
  · obtain ⟨xs, hv, rfl⟩ := (hinto _ _ _).1 hi
    exact ⟨xs, .inr ⟨sb, cont, hv, hsb, rfl⟩, rfl⟩

theorem slotB_of_vec {k : Nat} {α : Type} {R : α → List UInt8 → Prop} {get : Acc → List α}
    {set : Acc → List α → Acc}
    (hinto : ∀ a cont a₁, IntoB k a cont a₁ ↔ ∃ xs, Vec R xs cont ∧ a₁ = set a xs)
    (hset : ∀ a, get a = [] → set a [] = a) {a : Acc} {s : List UInt8} {xs : List α}
    (h : VecSecB (UInt8.ofNat k) R xs s) (h0 : get a = []) : SlotB k a s (set a xs) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨sb, cont, hv, hsb, rfl⟩
  · exact .inl ⟨rfl, hset a h0⟩
  · exact .inr ⟨sb, cont, rfl, hsb, (hinto _ _ _).2 ⟨xs, hv, rfl⟩⟩

theorem slotB_opt {k : Nat} {α : Type} {R : α → List UInt8 → Prop} {get : Acc → Option α}
    {set : Acc → Option α → Acc}
    (hinto : ∀ a cont a₁, IntoB k a cont a₁ ↔ ∃ x, R x cont ∧ a₁ = set a (some x))
    (hset : ∀ a, get a = none → set a none = a) {a : Acc} {s : List UInt8} {a₁ : Acc}
    (h : SlotB k a s a₁) (h0 : get a = none) :
    ∃ x, OptSecB (UInt8.ofNat k) R x s ∧ a₁ = set a x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨sb, cont, rfl, hsb, hi⟩
  · exact ⟨none, rfl, (hset _ h0).symm⟩
  · obtain ⟨x, hx, rfl⟩ := (hinto _ _ _).1 hi
    exact ⟨some x, ⟨sb, cont, hx, hsb, rfl⟩, rfl⟩

theorem slotB_of_opt {k : Nat} {α : Type} {R : α → List UInt8 → Prop} {get : Acc → Option α}
    {set : Acc → Option α → Acc}
    (hinto : ∀ a cont a₁, IntoB k a cont a₁ ↔ ∃ x, R x cont ∧ a₁ = set a (some x))
    (hset : ∀ a, get a = none → set a none = a) {a : Acc} {s : List UInt8} {x : Option α}
    (h : OptSecB (UInt8.ofNat k) R x s) (h0 : get a = none) : SlotB k a s (set a x) := by
  cases x with
  | none => exact .inl ⟨h, hset a h0⟩
  | some x =>
    obtain ⟨sb, cont, hx, hsb, rfl⟩ := h
    exact .inr ⟨sb, cont, rfl, hsb, (hinto _ _ _).2 ⟨x, hx, rfl⟩⟩

/-- Per-slot instances: each section slot sets exactly its own accumulator field. -/

theorem slot_types {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 1 a s a₁)
    (h0 : a.m.types = []) :
    ∃ x, VecSecB 1 FuncTypeB x s ∧ a₁ = { a with m := { a.m with types := x } } :=
  slotB_vec (get := fun a => a.m.types)
    (set := fun a x => { a with m := { a.m with types := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_types {a : Acc} {s : List UInt8} {x} (h : VecSecB 1 FuncTypeB x s)
    (h0 : a.m.types = []) : SlotB 1 a s ({ a with m := { a.m with types := x } }) :=
  slotB_of_vec (get := fun a => a.m.types)
    (set := fun a x => { a with m := { a.m with types := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_imports {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 2 a s a₁)
    (h0 : a.m.imports = []) :
    ∃ x, VecSecB 2 ImportB x s ∧ a₁ = { a with m := { a.m with imports := x } } :=
  slotB_vec (get := fun a => a.m.imports)
    (set := fun a x => { a with m := { a.m with imports := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_imports {a : Acc} {s : List UInt8} {x} (h : VecSecB 2 ImportB x s)
    (h0 : a.m.imports = []) : SlotB 2 a s ({ a with m := { a.m with imports := x } }) :=
  slotB_of_vec (get := fun a => a.m.imports)
    (set := fun a x => { a with m := { a.m with imports := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_typeIdxs {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 3 a s a₁)
    (h0 : a.typeIdxs = []) :
    ∃ x, VecSecB 3 IdxB x s ∧ a₁ = { a with typeIdxs := x } :=
  slotB_vec (get := fun a => a.typeIdxs)
    (set := fun a x => { a with typeIdxs := x }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_typeIdxs {a : Acc} {s : List UInt8} {x} (h : VecSecB 3 IdxB x s)
    (h0 : a.typeIdxs = []) : SlotB 3 a s ({ a with typeIdxs := x }) :=
  slotB_of_vec (get := fun a => a.typeIdxs)
    (set := fun a x => { a with typeIdxs := x }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_tables {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 4 a s a₁)
    (h0 : a.m.tables = []) :
    ∃ x, VecSecB 4 TableTypeB x s ∧ a₁ = { a with m := { a.m with tables := x } } :=
  slotB_vec (get := fun a => a.m.tables)
    (set := fun a x => { a with m := { a.m with tables := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_tables {a : Acc} {s : List UInt8} {x} (h : VecSecB 4 TableTypeB x s)
    (h0 : a.m.tables = []) : SlotB 4 a s ({ a with m := { a.m with tables := x } }) :=
  slotB_of_vec (get := fun a => a.m.tables)
    (set := fun a x => { a with m := { a.m with tables := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_mems {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 5 a s a₁)
    (h0 : a.m.mems = []) :
    ∃ x, VecSecB 5 LimitsB x s ∧ a₁ = { a with m := { a.m with mems := x } } :=
  slotB_vec (get := fun a => a.m.mems)
    (set := fun a x => { a with m := { a.m with mems := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_mems {a : Acc} {s : List UInt8} {x} (h : VecSecB 5 LimitsB x s)
    (h0 : a.m.mems = []) : SlotB 5 a s ({ a with m := { a.m with mems := x } }) :=
  slotB_of_vec (get := fun a => a.m.mems)
    (set := fun a x => { a with m := { a.m with mems := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_globals {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 6 a s a₁)
    (h0 : a.m.globals = []) :
    ∃ x, VecSecB 6 GlobalB x s ∧ a₁ = { a with m := { a.m with globals := x } } :=
  slotB_vec (get := fun a => a.m.globals)
    (set := fun a x => { a with m := { a.m with globals := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_globals {a : Acc} {s : List UInt8} {x} (h : VecSecB 6 GlobalB x s)
    (h0 : a.m.globals = []) : SlotB 6 a s ({ a with m := { a.m with globals := x } }) :=
  slotB_of_vec (get := fun a => a.m.globals)
    (set := fun a x => { a with m := { a.m with globals := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_exports {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 7 a s a₁)
    (h0 : a.m.exports = []) :
    ∃ x, VecSecB 7 ExportB x s ∧ a₁ = { a with m := { a.m with exports := x } } :=
  slotB_vec (get := fun a => a.m.exports)
    (set := fun a x => { a with m := { a.m with exports := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_exports {a : Acc} {s : List UInt8} {x} (h : VecSecB 7 ExportB x s)
    (h0 : a.m.exports = []) : SlotB 7 a s ({ a with m := { a.m with exports := x } }) :=
  slotB_of_vec (get := fun a => a.m.exports)
    (set := fun a x => { a with m := { a.m with exports := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_start {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 8 a s a₁)
    (h0 : a.m.start = none) :
    ∃ x, OptSecB 8 IdxB x s ∧ a₁ = { a with m := { a.m with start := x } } :=
  slotB_opt (get := fun a => a.m.start)
    (set := fun a x => { a with m := { a.m with start := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_start {a : Acc} {s : List UInt8} {x} (h : OptSecB 8 IdxB x s)
    (h0 : a.m.start = none) : SlotB 8 a s ({ a with m := { a.m with start := x } }) :=
  slotB_of_opt (get := fun a => a.m.start)
    (set := fun a x => { a with m := { a.m with start := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_elems {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 9 a s a₁)
    (h0 : a.m.elems = []) :
    ∃ x, VecSecB 9 ElemB x s ∧ a₁ = { a with m := { a.m with elems := x } } :=
  slotB_vec (get := fun a => a.m.elems)
    (set := fun a x => { a with m := { a.m with elems := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_elems {a : Acc} {s : List UInt8} {x} (h : VecSecB 9 ElemB x s)
    (h0 : a.m.elems = []) : SlotB 9 a s ({ a with m := { a.m with elems := x } }) :=
  slotB_of_vec (get := fun a => a.m.elems)
    (set := fun a x => { a with m := { a.m with elems := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_dataCount {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 12 a s a₁)
    (h0 : a.dataCount = none) :
    ∃ x, OptSecB 12 (ULeb 32) x s ∧ a₁ = { a with dataCount := x } :=
  slotB_opt (get := fun a => a.dataCount)
    (set := fun a x => { a with dataCount := x }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_dataCount {a : Acc} {s : List UInt8} {x} (h : OptSecB 12 (ULeb 32) x s)
    (h0 : a.dataCount = none) : SlotB 12 a s ({ a with dataCount := x }) :=
  slotB_of_opt (get := fun a => a.dataCount)
    (set := fun a x => { a with dataCount := x }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_codes {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 10 a s a₁)
    (h0 : a.codes = []) :
    ∃ x, VecSecB 10 CodeB x s ∧ a₁ = { a with codes := x } :=
  slotB_vec (get := fun a => a.codes)
    (set := fun a x => { a with codes := x }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_codes {a : Acc} {s : List UInt8} {x} (h : VecSecB 10 CodeB x s)
    (h0 : a.codes = []) : SlotB 10 a s ({ a with codes := x }) :=
  slotB_of_vec (get := fun a => a.codes)
    (set := fun a x => { a with codes := x }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slot_datas {a : Acc} {s : List UInt8} {a₁ : Acc} (h : SlotB 11 a s a₁)
    (h0 : a.m.datas = []) :
    ∃ x, VecSecB 11 DataB x s ∧ a₁ = { a with m := { a.m with datas := x } } :=
  slotB_vec (get := fun a => a.m.datas)
    (set := fun a x => { a with m := { a.m with datas := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

theorem slotOf_datas {a : Acc} {s : List UInt8} {x} (h : VecSecB 11 DataB x s)
    (h0 : a.m.datas = []) : SlotB 11 a s ({ a with m := { a.m with datas := x } }) :=
  slotB_of_vec (get := fun a => a.m.datas)
    (set := fun a x => { a with m := { a.m with datas := x } }) (fun _ _ _ => Iff.rfl)
    (fun a h => by cases a with | mk m ti cs dc => cases m; simp_all) h h0

/-! ## Whole modules -/

theorem finish_ok {a : Acc} {n : Nat} {m : Module} {v n' : Nat} (h : finish a n = .ok m v n') :
    m = finish.assemble a ∧ a.typeIdxs.length = a.codes.length ∧
      (∀ c, a.dataCount = some c → c = a.m.datas.length) ∧
      (a.dataCount = none → ∀ c ∈ a.codes, ¬ UsesDataS c.2) := by
  unfold finish at h
  cases h₁ : Nat.beq a.typeIdxs.length a.codes.length
  · simp only [h₁, Bool.not_false, Bool.cond_true] at h; simp at h
  · simp only [h₁, Bool.not_true, Bool.cond_false] at h
    have hlen := beq_true.1 h₁
    split at h
    · rename_i c hc
      cases h₂ : Nat.beq c a.m.datas.length
      · simp only [h₂, Bool.cond_false] at h; simp at h
      · simp only [h₂, Bool.cond_true, Res.ok.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        refine ⟨rfl, hlen, fun c' hc' => ?_, fun h => (by rw [hc] at h; cases h)⟩
        rw [hc] at hc'; cases hc'; exact beq_true.1 h₂
    · rename_i hc
      cases h₂ : a.codes.any (fun c => usesDataList c.2)
      · simp only [h₂, Bool.cond_false, Res.ok.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        refine ⟨rfl, hlen, fun c' hc' => (by rw [hc] at hc'; cases hc'), fun _ c hm hu => ?_⟩
        have : a.codes.any (fun c => usesDataList c.2) = true :=
          List.any_eq_true.2 ⟨c, hm, (usesDataList_iff _).2 hu⟩
        rw [h₂] at this; cases this
      · simp only [h₂, Bool.cond_true] at h; simp at h

theorem finish_of {a : Acc} {n : Nat} (h₁ : a.typeIdxs.length = a.codes.length)
    (h₂ : ∀ c, a.dataCount = some c → c = a.m.datas.length)
    (h₃ : a.dataCount = none → ∀ c ∈ a.codes, ¬ UsesDataS c.2) :
    finish a n = .ok (finish.assemble a) 0 n := by
  unfold finish
  simp only [beq_true.2 h₁, Bool.not_true, Bool.cond_false]
  split
  · rename_i c hc
    simp only [beq_true.2 (h₂ c hc), Bool.cond_true]
  · rename_i hc
    have : a.codes.any (fun c => usesDataList c.2) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨c, hm, hu⟩ := List.any_eq_true.1 h
      exact h₃ hc c hm ((usesDataList_iff _).1 hu)
    simp only [this, Bool.cond_false]

theorem preamble_eq : preamble = [0x00, 0x61, 0x73, 0x6D] ++ [0x01, 0x00, 0x00, 0x00] := rfl

theorem magic_bytes {m4 : List UInt8} (hl : m4.length = 4) (h : pack m4 = 0x6D736100) :
    m4 = [0x00, 0x61, 0x73, 0x6D] :=
  pack_injective (by simp [hl]) (by rw [h]; rfl)

theorem version_bytes {v4 : List UInt8} (hl : v4.length = 4) (h : pack v4 = 1) :
    v4 = [0x01, 0x00, 0x00, 0x00] :=
  pack_injective (by simp [hl]) (by rw [h]; rfl)

/-- T1 (soundness): a decoded module is what the bytes encode. -/
theorem decode_sound {b : List UInt8} {m : Module} (h : decode (pack b) b.length = .ok m) :
    ModuleB m b := by
  unfold decode at h
  dsimp only at h
  split at h
  case h_2 | h_3 => simp at h
  rename_i m' v n hr
  cases h
  obtain ⟨magic, v₁, n₁, h₁, k₁⟩ := Res.bind_eq_ok.1 hr
  obtain ⟨m4, r₁, rfl, ⟨hl4, rfl⟩, rfl, rfl⟩ := (leNat_parses 4).sound h₁
  cases hmg : Nat.beq (pack m4) 0x6D736100
  · simp only [hmg, Bool.not_false, Bool.cond_true] at k₁; simp at k₁
  simp only [hmg, Bool.not_true, Bool.cond_false] at k₁
  have em4 := magic_bytes hl4 (beq_true.1 hmg)
  obtain ⟨version, v₂, n₂, h₂, k₂⟩ := Res.bind_eq_ok.1 k₁
  obtain ⟨v4, r₂, er₁, ⟨hv4, rfl⟩, rfl, rfl⟩ := (leNat_parses 4).sound h₂
  cases hvs : Nat.beq (pack v4) 1
  · simp only [hvs, Bool.not_false, Bool.cond_true] at k₂; simp at k₂
  simp only [hvs, Bool.not_true, Bool.cond_false] at k₂
  have ev4 := version_bytes hv4 (beq_true.1 hvs)
  obtain ⟨a, v₃, n₃, h₃, k₃⟩ := Res.bind_eq_ok.1 k₂
  obtain ⟨body, rest, er₂, hl, rfl, rfl⟩ := slots_sound (fun _ h => h) h₃
  cases hz : Nat.beq rest.length 0
  · simp only [hz, Bool.cond_false] at k₃
    revert k₃
    cases Nat.beq (Nat.land (pack rest) 255) 13 <;> cases Nat.blt 12 (Nat.land (pack rest) 255) <;>
      simp
  simp only [hz, Bool.cond_true] at k₃
  obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (beq_true.1 hz)
  subst em4 ev4 er₁ er₂
  obtain ⟨rfl, hlen, hdc, hdc'⟩ := finish_ok k₃
  -- unpack the twelve slots
  obtain ⟨c₀, s₁, r₁, a₁, hc₀, hs₁, hl, rfl⟩ := hl
  obtain ⟨c₁, s₂, r₂, a₂, hc₁, hs₂, hl, rfl⟩ := hl
  obtain ⟨c₂, s₃, r₃, a₃, hc₂, hs₃, hl, rfl⟩ := hl
  obtain ⟨c₃, s₄, r₄, a₄, hc₃, hs₄, hl, rfl⟩ := hl
  obtain ⟨c₄, s₅, r₅, a₅, hc₄, hs₅, hl, rfl⟩ := hl
  obtain ⟨c₅, s₆, r₆, a₆, hc₅, hs₆, hl, rfl⟩ := hl
  obtain ⟨c₆, s₇, r₇, a₇, hc₆, hs₇, hl, rfl⟩ := hl
  obtain ⟨c₇, s₈, r₈, a₈, hc₇, hs₈, hl, rfl⟩ := hl
  obtain ⟨c₈, s₉, r₉, a₉, hc₈, hs₉, hl, rfl⟩ := hl
  obtain ⟨c₉, s₁₂, r₁₂, a₁₂, hc₉, hs₁₂, hl, rfl⟩ := hl
  obtain ⟨c₁₂, s₁₀, r₁₀, a₁₀, hc₁₂, hs₁₀, hl, rfl⟩ := hl
  obtain ⟨c₁₀, s₁₁, c₁₁, a₁₁, hc₁₀, hs₁₁, ⟨hc₁₁, rfl⟩, rfl⟩ := hl
  obtain ⟨x₁, hx₁, rfl⟩ := slot_types hs₁ rfl
  obtain ⟨x₂, hx₂, rfl⟩ := slot_imports hs₂ rfl
  obtain ⟨x₃, hx₃, rfl⟩ := slot_typeIdxs hs₃ rfl
  obtain ⟨x₄, hx₄, rfl⟩ := slot_tables hs₄ rfl
  obtain ⟨x₅, hx₅, rfl⟩ := slot_mems hs₅ rfl
  obtain ⟨x₆, hx₆, rfl⟩ := slot_globals hs₆ rfl
  obtain ⟨x₇, hx₇, rfl⟩ := slot_exports hs₇ rfl
  obtain ⟨x₈, hx₈, rfl⟩ := slot_start hs₈ rfl
  obtain ⟨x₉, hx₉, rfl⟩ := slot_elems hs₉ rfl
  obtain ⟨x₁₂, hx₁₂, rfl⟩ := slot_dataCount hs₁₂ rfl
  obtain ⟨x₁₀, hx₁₀, rfl⟩ := slot_codes hs₁₀ rfl
  obtain ⟨x₁₁, hx₁₁, rfl⟩ := slot_datas hs₁₁ rfl
  refine ⟨x₃, x₁₀, x₁₂, c₀, s₁, c₁, s₂, c₂, s₃, c₃, s₄, c₄, s₅, c₅, s₆, c₆, s₇, c₇, s₈, c₈, s₉,
    c₉, s₁₂, c₁₂, s₁₀, c₁₀, s₁₁, c₁₁, hc₀, hx₁, hc₁, hx₂, hc₂, hx₃, hc₃, hx₄, hc₄, hx₅, hc₅, hx₆,
    hc₆, hx₇, hc₇, hx₈, hc₈, hx₉, hc₉, hx₁₂, hc₁₂, hx₁₀, hc₁₀, hx₁₁, hc₁₁, hlen, rfl, hdc, hdc', ?_⟩
  simp [preamble]

theorem slotIds_nodup : slotIds.Nodup := by simp [slotIds]

/-- The accumulator after all twelve slots. -/
def accOf (types : List FuncType) (imports : List Import) (typeIdxs : List Nat)
    (tables : List TableType) (mems : List Limits) (globals : List Global) (exports : List Export)
    (start : Option Nat) (elems : List Elem) (dataCount : Option Nat)
    (codes : List (List (Nat × ValType) × Expr)) (datas : List Data) : Acc :=
  { m := { types, imports, tables, mems, globals, exports, start, elems, datas },
    typeIdxs, codes, dataCount }

theorem layout_of_slots {x₁ : List FuncType} {x₂ : List Import} {x₃ : List Nat}
    {x₄ : List TableType} {x₅ : List Limits} {x₆ : List Global} {x₇ : List Export}
    {x₈ : Option Nat} {x₉ : List Elem} {x₁₂ : Option Nat}
    {x₁₀ : List (List (Nat × ValType) × Expr)} {x₁₁ : List Data}
    {c₀ s₁ c₁ s₂ c₂ s₃ c₃ s₄ c₄ s₅ c₅ s₆ c₆ s₇ c₇ s₈ c₈ s₉ c₉ s₁₂ c₁₂ s₁₀ c₁₀ s₁₁ c₁₁ :
      List UInt8}
    (hc₀ : CustomsB c₀) (hx₁ : VecSecB 1 FuncTypeB x₁ s₁) (hc₁ : CustomsB c₁)
    (hx₂ : VecSecB 2 ImportB x₂ s₂) (hc₂ : CustomsB c₂) (hx₃ : VecSecB 3 IdxB x₃ s₃)
    (hc₃ : CustomsB c₃) (hx₄ : VecSecB 4 TableTypeB x₄ s₄) (hc₄ : CustomsB c₄)
    (hx₅ : VecSecB 5 LimitsB x₅ s₅) (hc₅ : CustomsB c₅) (hx₆ : VecSecB 6 GlobalB x₆ s₆)
    (hc₆ : CustomsB c₆) (hx₇ : VecSecB 7 ExportB x₇ s₇) (hc₇ : CustomsB c₇)
    (hx₈ : OptSecB 8 IdxB x₈ s₈) (hc₈ : CustomsB c₈) (hx₉ : VecSecB 9 ElemB x₉ s₉)
    (hc₉ : CustomsB c₉) (hx₁₂ : OptSecB 12 (ULeb 32) x₁₂ s₁₂) (hc₁₂ : CustomsB c₁₂)
    (hx₁₀ : VecSecB 10 CodeB x₁₀ s₁₀) (hc₁₀ : CustomsB c₁₀) (hx₁₁ : VecSecB 11 DataB x₁₁ s₁₁)
    (hc₁₁ : CustomsB c₁₁) :
    Layout slotIds {} (c₀ ++ s₁ ++ (c₁ ++ s₂ ++ (c₂ ++ s₃ ++ (c₃ ++ s₄ ++ (c₄ ++ s₅ ++
      (c₅ ++ s₆ ++ (c₆ ++ s₇ ++ (c₇ ++ s₈ ++ (c₈ ++ s₉ ++ (c₉ ++ s₁₂ ++ (c₁₂ ++ s₁₀ ++
      (c₁₀ ++ s₁₁ ++ c₁₁))))))))))))
      (accOf x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₂ x₁₀ x₁₁) :=
  ⟨c₀, s₁, _, _, hc₀, slotOf_types hx₁ rfl,
   ⟨c₁, s₂, _, _, hc₁, slotOf_imports hx₂ rfl,
    ⟨c₂, s₃, _, _, hc₂, slotOf_typeIdxs hx₃ rfl,
     ⟨c₃, s₄, _, _, hc₃, slotOf_tables hx₄ rfl,
      ⟨c₄, s₅, _, _, hc₄, slotOf_mems hx₅ rfl,
       ⟨c₅, s₆, _, _, hc₅, slotOf_globals hx₆ rfl,
        ⟨c₆, s₇, _, _, hc₆, slotOf_exports hx₇ rfl,
         ⟨c₇, s₈, _, _, hc₇, slotOf_start hx₈ rfl,
          ⟨c₈, s₉, _, _, hc₈, slotOf_elems hx₉ rfl,
           ⟨c₉, s₁₂, _, _, hc₉, slotOf_dataCount hx₁₂ rfl,
            ⟨c₁₂, s₁₀, _, _, hc₁₂, slotOf_codes hx₁₀ rfl,
             ⟨c₁₀, s₁₁, c₁₁, _, hc₁₀, slotOf_datas hx₁₁ rfl, ⟨hc₁₁, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
                rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- T2 (completeness): every encoding of a module decodes to it. -/
theorem decode_complete {b : List UInt8} {m : Module} (h : ModuleB m b) :
    decode (pack b) b.length = .ok m := by
  obtain ⟨typeIdxs, codes, dataCount, c₀, s₁, c₁, s₂, c₂, s₃, c₃, s₄, c₄, s₅, c₅, s₆, c₆, s₇, c₇,
    s₈, c₈, s₉, c₉, s₁₂, c₁₂, s₁₀, c₁₀, s₁₁, c₁₁, hc₀, hx₁, hc₁, hx₂, hc₂, hx₃, hc₃, hx₄, hc₄,
    hx₅, hc₅, hx₆, hc₆, hx₇, hc₇, hx₈, hc₈, hx₉, hc₉, hx₁₂, hc₁₂, hx₁₀, hc₁₀, hx₁₁, hc₁₁, hlen,
    hfuncs, hdc, hdc', hb⟩ := h
  have hl := layout_of_slots hc₀ hx₁ hc₁ hx₂ hc₂ hx₃ hc₃ hx₄ hc₄ hx₅ hc₅ hx₆ hc₆ hx₇ hc₇ hx₈ hc₈
    hx₉ hc₉ hx₁₂ hc₁₂ hx₁₀ hc₁₀ hx₁₁ hc₁₁
  generalize hbody : c₀ ++ s₁ ++ (c₁ ++ s₂ ++ (c₂ ++ s₃ ++ (c₃ ++ s₄ ++ (c₄ ++ s₅ ++
      (c₅ ++ s₆ ++ (c₆ ++ s₇ ++ (c₇ ++ s₈ ++ (c₈ ++ s₉ ++ (c₉ ++ s₁₂ ++ (c₁₂ ++ s₁₀ ++
      (c₁₀ ++ s₁₁ ++ c₁₁))))))))))) = body at hl
  have hb' : b = [0x00, 0x61, 0x73, 0x6D] ++ ([0x01, 0x00, 0x00, 0x00] ++ body) := by
    rw [hb, ← hbody]; simp [preamble]
  subst hb'
  generalize hacc : accOf m.types m.imports typeIdxs m.tables m.mems m.globals m.exports m.start
    m.elems dataCount codes m.datas = a at hl
  have hsl := slots_complete (fun _ h => h) slotIds_nodup hl (pre := []) .nil
  simp only [List.nil_append] at hsl
  have hfin : finish a 0 = .ok (finish.assemble a) 0 0 := by
    subst hacc
    exact finish_of hlen hdc (fun h c hc => hdc' h c hc)
  have hm : finish.assemble a = m := by
    subst hacc
    cases m; simp_all [finish.assemble, accOf]
  unfold decode
  dsimp only
  rw [(leNat_parses 4).complete _ ⟨rfl, rfl⟩, Res.bind_ok]
  simp only [show Nat.beq (pack [0x00, 0x61, 0x73, 0x6D]) 0x6D736100 = true from rfl,
    Bool.not_true, Bool.cond_false]
  rw [(leNat_parses 4).complete _ ⟨rfl, rfl⟩, Res.bind_ok]
  simp only [show Nat.beq (pack [0x01, 0x00, 0x00, 0x00]) 1 = true from rfl, Bool.not_true,
    Bool.cond_false]
  rw [hsl, Res.bind_ok]
  simp only [show Nat.beq 0 0 = true from rfl, Bool.cond_true, hfin, hm]

/-- T3: the grammar is unambiguous: an encoding determines its module. -/
theorem moduleB_functional {b : List UInt8} {m m' : Module} (h : ModuleB m b) (h' : ModuleB m' b) :
    m = m' := by
  have := (decode_complete h).symm.trans (decode_complete h')
  simpa using this

/-- The decoder decides the binary grammar. -/
theorem decode_iff {b : List UInt8} {m : Module} :
    decode (pack b) b.length = .ok m ↔ ModuleB m b :=
  ⟨decode_sound, decode_complete⟩

end FVA.Wasm.Decode
