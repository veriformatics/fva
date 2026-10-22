import FVA.Proof.Decode.Instr
import FVA.Proof.Decode.Name

/-!
# Module-item decoders

Types, imports, exports, globals, element/data segments and code entries decode exactly their
reviewed binary relations, including every supported segment encoding and code-body size bound.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm FVA.Wasm.Binary

theorem Parses.map {α β : Type} {p : Nat → Nat → Res α} {R : α → List UInt8 → Prop}
    (hp : Parses p R) (f : α → β) :
    Parses (fun v n => (p v n).bind fun a v n => .ok (f a) v n)
      (fun b bs => ∃ a, R a bs ∧ b = f a) := by
  constructor
  · intro bs b v n h
    obtain ⟨a, pre, rest, rfl, ha, rfl, rfl, rfl⟩ := hp.map_sound h
    exact ⟨pre, rest, rfl, ⟨a, ha, rfl⟩, rfl, rfl⟩
  · rintro b pre rest ⟨a, ha, rfl⟩
    rw [hp.complete rest ha, Res.bind_ok]

theorem limits_parses : Parses limits LimitsB := by
  constructor
  · intro bs l v n h
    obtain ⟨f, v₁, n₁, hb, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, rest₁, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hb
    cases h₀ : Nat.beq b.toNat 0
    · simp only [h₀, Bool.cond_false] at hk
      cases h₁ : Nat.beq b.toNat 1
      · simp only [h₁, Bool.cond_false] at hk
        simp only [Bool.cond_eq_ite] at hk
        split at hk <;> cases hk
      · have hb : b = 1 := UInt8.toNat_inj.1 (beq_true.1 h₁)
        subst hb
        simp only [h₁, Bool.cond_true] at hk
        obtain ⟨a, v₂, n₂, ha, hk⟩ := Res.bind_eq_ok.1 hk
        obtain ⟨b₁, rest₂, rfl, hpa, rfl, rfl⟩ := u32_parses.sound ha
        obtain ⟨c, b₂, rest, rfl, hc, rfl, rfl, rfl⟩ := u32_parses.map_sound hk
        exact ⟨[1] ++ b₁ ++ b₂, rest, by simp, ⟨b₁, b₂, hpa, hc, rfl⟩, rfl, rfl⟩
    · have hb : b = 0 := UInt8.toNat_inj.1 (beq_true.1 h₀)
      subst hb
      simp only [h₀, Bool.cond_true] at hk
      obtain ⟨a, b₁, rest, rfl, ha, rfl, rfl, rfl⟩ := u32_parses.map_sound hk
      exact ⟨[0] ++ b₁, rest, rfl, ⟨b₁, ha, rfl⟩, rfl, rfl⟩
  · rintro ⟨a, m⟩ pre rest h
    cases m with
    | none =>
      obtain ⟨b, hb, rfl⟩ := h
      simp only [List.cons_append, List.nil_append, limits, byte, List.length_cons,
        land_pack_cons, shiftRight_pack_cons, Res.bind_ok]
      change (u32 (pack (b ++ rest)) (b ++ rest).length).bind _ = _
      rw [u32_parses.complete rest hb, Res.bind_ok]
    | some c =>
      obtain ⟨b₁, b₂, ha, hc, rfl⟩ := h
      simp only [List.append_assoc, List.cons_append, List.nil_append, limits, byte,
        List.length_cons, land_pack_cons, shiftRight_pack_cons, Res.bind_ok]
      change (u32 (pack (b₁ ++ (b₂ ++ rest))) (b₁ ++ (b₂ ++ rest)).length).bind _ = _
      rw [u32_parses.complete (b₂ ++ rest) ha, Res.bind_ok,
        u32_parses.complete rest hc, Res.bind_ok]

theorem funcType_parses : Parses funcType FuncTypeB := by
  have hv := vec_parses valType_parses fun _ _ h => ValTypeB.ne_nil h
  constructor
  · intro bs ft v n h
    obtain ⟨f, v₁, n₁, hb, hk⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, rest₁, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hb
    cases h₀ : Nat.beq b.toNat 0x60
    · simp only [h₀, Bool.cond_false] at hk
      simp only [Bool.cond_eq_ite] at hk
      split at hk <;> cases hk
    · have hb : b = 0x60 := UInt8.toNat_inj.1 (beq_true.1 h₀)
      subst hb
      simp only [h₀, Bool.cond_true] at hk
      obtain ⟨ps, v₂, n₂, hp, hk⟩ := Res.bind_eq_ok.1 hk
      obtain ⟨b₁, rest₂, rfl, hps, rfl, rfl⟩ := hv.sound hp
      obtain ⟨rs, b₂, rest, rfl, hr, rfl, rfl, rfl⟩ := hv.map_sound hk
      exact ⟨[0x60] ++ b₁ ++ b₂, rest, by simp, ⟨b₁, b₂, hps, hr, rfl⟩, rfl, rfl⟩
  · rintro ft _ rest ⟨b₁, b₂, hp, hr, rfl⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append, funcType, byte,
      List.length_cons, land_pack_cons, shiftRight_pack_cons, Res.bind_ok]
    change (vec valType (pack (b₁ ++ (b₂ ++ rest))) (b₁ ++ (b₂ ++ rest)).length).bind _ = _
    rw [hv.complete (b₂ ++ rest) hp, Res.bind_ok, hv.complete rest hr, Res.bind_ok]

theorem tableType_parses : Parses tableType TableTypeB := by
  exact (refType_parses.bind fun t => limits_parses.map fun l => TableType.mk l t).congr
    fun t bs => by
      constructor
      · rintro ⟨rt, b₁, b₂, hr, ⟨l, hl, rfl⟩, rfl⟩
        exact ⟨b₁, b₂, hr, hl, rfl⟩
      · rintro ⟨b₁, b₂, hr, hl, rfl⟩
        exact ⟨t.elem, b₁, b₂, hr, ⟨t.limits, hl, rfl⟩, rfl⟩

theorem globalType_parses : Parses globalType GlobalTypeB := by
  constructor
  · intro bs gt v n h
    obtain ⟨t, v₁, n₁, ht, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b₁, rest₁, rfl, hvt, rfl, rfl⟩ := valType_parses.sound ht
    obtain ⟨m, v₂, n₂, hm, h₂⟩ := Res.bind_eq_ok.1 h₁
    obtain ⟨_, rest, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hm
    simp only [Bool.cond_eq_ite, Nat.beq_eq] at h₂
    split at h₂
    · rename_i hb
      have he : b = 0 := UInt8.toNat_inj.1 hb
      subst he
      cases h₂
      exact ⟨b₁ ++ [0], rest, by simp, ⟨b₁, hvt, rfl⟩, rfl, rfl⟩
    · split at h₂
      · rename_i hb
        have he : b = 1 := UInt8.toNat_inj.1 hb
        subst he
        cases h₂
        exact ⟨b₁ ++ [1], rest, by simp, ⟨b₁, hvt, rfl⟩, rfl, rfl⟩
      · cases h₂
  · rintro ⟨m, t⟩ _ rest ⟨b, ht, rfl⟩
    cases m <;>
      (simp only [globalType, List.append_assoc]
       rw [valType_parses.complete _ ht, Res.bind_ok]
       simp only [List.singleton_append, byte, List.length_cons, land_pack_cons,
         shiftRight_pack_cons, Res.bind_ok]
       rfl)

theorem import_parses : Parses import_ ImportB := by
  constructor
  · intro bs im v n h
    obtain ⟨md, v₁, n₁, hmd, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b₁, rest₁, rfl, hmdB, rfl, rfl⟩ := name_parses.sound hmd
    obtain ⟨nm, v₂, n₂, hnm, h₂⟩ := Res.bind_eq_ok.1 h₁
    obtain ⟨b₂, rest₂, rfl, hnmB, rfl, rfl⟩ := name_parses.sound hnm
    obtain ⟨k, v₃, n₃, hk, h₃⟩ := Res.bind_eq_ok.1 h₂
    obtain ⟨_, rest₃, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hk
    obtain ⟨d, v₄, n₄, hd, h₄⟩ := Res.bind_eq_ok.1 h₃
    cases h₄
    simp only [Bool.cond_eq_ite, Nat.beq_eq] at hd
    repeat' split at hd
    all_goals first
      | (cases hd; done)
      | (rename_i hb
         have he : b = 0 := UInt8.toNat_inj.1 hb
         subst he
         obtain ⟨x, bd, rest, rfl, hx, rfl, rfl, rfl⟩ := u32_parses.map_sound hd
         exact ⟨b₁ ++ b₂ ++ (0 :: bd), rest, by simp,
           ⟨b₁, b₂, 0 :: bd, hmdB, hnmB, ⟨bd, hx, rfl⟩, rfl⟩, rfl, rfl⟩)
      | (rename_i hb
         have he : b = 1 := UInt8.toNat_inj.1 hb
         subst he
         obtain ⟨t, bd, rest, rfl, ht, rfl, rfl, rfl⟩ := tableType_parses.map_sound hd
         exact ⟨b₁ ++ b₂ ++ (1 :: bd), rest, by simp,
           ⟨b₁, b₂, 1 :: bd, hmdB, hnmB, ⟨bd, ht, rfl⟩, rfl⟩, rfl, rfl⟩)
      | (rename_i hb
         have he : b = 2 := UInt8.toNat_inj.1 hb
         subst he
         obtain ⟨t, bd, rest, rfl, ht, rfl, rfl, rfl⟩ := limits_parses.map_sound hd
         exact ⟨b₁ ++ b₂ ++ (2 :: bd), rest, by simp,
           ⟨b₁, b₂, 2 :: bd, hmdB, hnmB, ⟨bd, ht, rfl⟩, rfl⟩, rfl, rfl⟩)
      | (rename_i hb
         have he : b = 3 := UInt8.toNat_inj.1 hb
         subst he
         obtain ⟨t, bd, rest, rfl, ht, rfl, rfl, rfl⟩ := globalType_parses.map_sound hd
         exact ⟨b₁ ++ b₂ ++ (3 :: bd), rest, by simp,
           ⟨b₁, b₂, 3 :: bd, hmdB, hnmB, ⟨bd, ht, rfl⟩, rfl⟩, rfl, rfl⟩)
  · rintro ⟨md, nm, d⟩ _ rest ⟨b₁, b₂, b₃, hmd, hnm, hd, rfl⟩
    cases d <;> obtain ⟨bd, hv, rfl⟩ := hd
    all_goals
      simp only [import_, List.append_assoc]
      rw [name_parses.complete _ hmd, Res.bind_ok, name_parses.complete _ hnm, Res.bind_ok]
      simp only [List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok]
      first
        | rw [u32_parses.complete rest hv]; rfl
        | rw [tableType_parses.complete rest hv]; rfl
        | rw [limits_parses.complete rest hv]; rfl
        | rw [globalType_parses.complete rest hv]; rfl

theorem export_parses : Parses export_ ExportB := by
  constructor
  · intro bs ex v n h
    obtain ⟨nm, v₁, n₁, hnm, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b₁, rest₁, rfl, hnmB, rfl, rfl⟩ := name_parses.sound hnm
    obtain ⟨k, v₂, n₂, hk, h₂⟩ := Res.bind_eq_ok.1 h₁
    obtain ⟨_, rest₂, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hk
    obtain ⟨x, v₃, n₃, hx, h₃⟩ := Res.bind_eq_ok.1 h₂
    obtain ⟨bd, rest, rfl, hxB, rfl, rfl⟩ := u32_parses.sound hx
    simp only [Bool.cond_eq_ite, Nat.beq_eq] at h₃
    repeat' split at h₃
    all_goals first
      | (cases h₃; done)
      | (rename_i hb
         have he : b = 0 := UInt8.toNat_inj.1 hb
         subst he
         cases h₃
         exact ⟨b₁ ++ (0 :: bd), rest, by simp,
           ⟨b₁, 0 :: bd, hnmB, ⟨bd, hxB, rfl⟩, rfl⟩, rfl, rfl⟩)
      | (rename_i hb
         have he : b = 1 := UInt8.toNat_inj.1 hb
         subst he
         cases h₃
         exact ⟨b₁ ++ (1 :: bd), rest, by simp,
           ⟨b₁, 1 :: bd, hnmB, ⟨bd, hxB, rfl⟩, rfl⟩, rfl, rfl⟩)
      | (rename_i hb
         have he : b = 2 := UInt8.toNat_inj.1 hb
         subst he
         cases h₃
         exact ⟨b₁ ++ (2 :: bd), rest, by simp,
           ⟨b₁, 2 :: bd, hnmB, ⟨bd, hxB, rfl⟩, rfl⟩, rfl, rfl⟩)
      | (rename_i hb
         have he : b = 3 := UInt8.toNat_inj.1 hb
         subst he
         cases h₃
         exact ⟨b₁ ++ (3 :: bd), rest, by simp,
           ⟨b₁, 3 :: bd, hnmB, ⟨bd, hxB, rfl⟩, rfl⟩, rfl, rfl⟩)
  · rintro ⟨nm, d⟩ _ rest ⟨b₁, b₂, hnm, hd, rfl⟩
    cases d <;> obtain ⟨bd, hx, rfl⟩ := hd
    all_goals
      simp only [export_, List.append_assoc]
      rw [name_parses.complete _ hnm, Res.bind_ok]
      simp only [List.cons_append, byte, List.length_cons, land_pack_cons,
        shiftRight_pack_cons, Res.bind_ok]
      rw [u32_parses.complete rest hx, Res.bind_ok]
      rfl

theorem global_parses : Parses global GlobalB := by
  exact (globalType_parses.bind fun t => expr_parses.map fun e => Global.mk t e).congr
    fun g bs => by
      constructor
      · rintro ⟨t, b₁, b₂, ht, ⟨e, he, rfl⟩, rfl⟩
        exact ⟨b₁, b₂, ht, he, rfl⟩
      · rintro ⟨b₁, b₂, ht, he, rfl⟩
        exact ⟨g.type, b₁, b₂, ht, ⟨g.init, he, rfl⟩, rfl⟩

theorem localsRun_parses : Parses localsRun LocalsB := by
  exact (u32_parses.bind fun c => valType_parses.map fun t => (c, t)).congr
    fun g bs => by
      constructor
      · rintro ⟨c, b₁, b₂, hc, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨b₁, b₂, hc, ht, rfl⟩
      · rintro ⟨b₁, b₂, hc, ht, rfl⟩
        exact ⟨g.1, b₁, b₂, hc, ⟨g.2, ht, rfl⟩, rfl⟩

theorem Vec.ne_nil {α : Type} {R : α → List UInt8 → Prop} {xs : List α}
    {bs : List UInt8} (h : Vec R xs bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, hu, _, rfl⟩ := h
  simp [List.append_eq_nil_iff, ULeb.ne_nil hu]

theorem ExprB.ne_nil {e : Expr} {bs : List UInt8} (h : ExprB e bs) : bs ≠ [] := by
  obtain ⟨pre, _, rfl⟩ := h
  simp

theorem LimitsB.ne_nil {l : Limits} {bs : List UInt8} (h : LimitsB l bs) : bs ≠ [] := by
  rcases l with ⟨a, m⟩
  cases m with
  | none => obtain ⟨b, _, rfl⟩ := h; simp
  | some => obtain ⟨b₁, b₂, _, _, rfl⟩ := h; simp

theorem FuncTypeB.ne_nil {t : FuncType} {bs : List UInt8} (h : FuncTypeB t bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, _, _, rfl⟩ := h
  simp

theorem TableTypeB.ne_nil {t : TableType} {bs : List UInt8} (h : TableTypeB t bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, _, hl, rfl⟩ := h
  simp [List.append_eq_nil_iff, LimitsB.ne_nil hl]

theorem GlobalTypeB.ne_nil {t : GlobalType} {bs : List UInt8} (h : GlobalTypeB t bs) :
    bs ≠ [] := by
  obtain ⟨b, _, rfl⟩ := h
  simp

theorem ImportDescB.ne_nil {d : ImportDesc} {bs : List UInt8} (h : ImportDescB d bs) :
    bs ≠ [] := by
  cases d <;> obtain ⟨b, _, rfl⟩ := h <;> simp

theorem ImportB.ne_nil {im : Import} {bs : List UInt8} (h : ImportB im bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, b₃, _, _, hd, rfl⟩ := h
  simp [List.append_eq_nil_iff, ImportDescB.ne_nil hd]

theorem ExportDescB.ne_nil {d : ExportDesc} {bs : List UInt8} (h : ExportDescB d bs) :
    bs ≠ [] := by
  cases d <;> obtain ⟨b, _, rfl⟩ := h <;> simp

theorem ExportB.ne_nil {ex : Export} {bs : List UInt8} (h : ExportB ex bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, _, hd, rfl⟩ := h
  simp [List.append_eq_nil_iff, ExportDescB.ne_nil hd]

theorem GlobalB.ne_nil {g : Global} {bs : List UInt8} (h : GlobalB g bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, ht, _, rfl⟩ := h
  simp [List.append_eq_nil_iff, GlobalTypeB.ne_nil ht]

theorem ElemB.ne_nil {e : Elem} {bs : List UInt8} (h : ElemB e bs) : bs ≠ [] := by
  cases h with
  | e0 hf _ _ | e1 hf _ _ | e2 hf _ _ _ _ | e3 hf _ _ =>
    simp [List.append_eq_nil_iff, ULeb.ne_nil hf]
  | e4 hf _ _ | e5 hf _ _ | e6 hf _ _ _ _ | e7 hf _ _ =>
    simp [List.append_eq_nil_iff, ULeb.ne_nil hf]

theorem DataB.ne_nil {d : Data} {bs : List UInt8} (h : DataB d bs) : bs ≠ [] := by
  cases h with
  | d0 hf _ _ | d1 hf _ | d2 hf _ _ _ =>
    simp [List.append_eq_nil_iff, ULeb.ne_nil hf]

theorem LocalsB.ne_nil {g : Nat × ValType} {bs : List UInt8} (h : LocalsB g bs) : bs ≠ [] := by
  obtain ⟨b₁, b₂, hu, _, rfl⟩ := h
  simp [List.append_eq_nil_iff, ULeb.ne_nil hu]

theorem CodeB.ne_nil {c : List (Nat × ValType) × Expr} {bs : List UInt8} (h : CodeB c bs) :
    bs ≠ [] := by
  obtain ⟨bsz, bl, be, _, _, _, hu, rfl⟩ := h
  simp [List.append_eq_nil_iff, ULeb.ne_nil hu]

theorem codeBody_parses : Parses codeBody (fun c bs => ∃ bl be,
    Vec LocalsB c.1 bl ∧ ExprB c.2 be ∧ (c.1.map Prod.fst).sum < 2 ^ 32 ∧ bs = bl ++ be) := by
  have hv := vec_parses localsRun_parses fun _ _ h => LocalsB.ne_nil h
  constructor
  · intro bs c v n h
    obtain ⟨ls, v₁, n₁, hl, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨bl, rest₁, rfl, hlB, rfl, rfl⟩ := hv.sound hl
    cases hs : Nat.blt (ls.map Prod.fst).sum (2 ^ 32)
    · simp [hs] at h₁
    · simp only [hs, Bool.cond_true] at h₁
      obtain ⟨e, be, rest, rfl, heB, rfl, rfl, rfl⟩ := expr_parses.map_sound h₁
      exact ⟨bl ++ be, rest, by simp, ⟨bl, be, hlB, heB, blt_true.1 hs, rfl⟩, rfl, rfl⟩
  · rintro ⟨ls, e⟩ _ rest ⟨bl, be, hl, he, hs, rfl⟩
    simp only [codeBody, List.append_assoc]
    rw [hv.complete (be ++ rest) hl, Res.bind_ok, blt_true.2 hs, Bool.cond_true,
      expr_parses.complete rest he, Res.bind_ok]

theorem code_parses : Parses code CodeB := by
  exact (u32_parses.bind fun k => sub_parses codeBody_parses k).congr fun c bs => by
    constructor
    · rintro ⟨k, bsz, _, hk, ⟨hlen, bl, be, hl, he, hs, rfl⟩, rfl⟩
      exact ⟨bsz, bl, be, hl, he, hs, hlen ▸ hk, by simp⟩
    · rintro ⟨bsz, bl, be, hl, he, hs, hk, rfl⟩
      exact ⟨(bl ++ be).length, bsz, bl ++ be, hk,
        ⟨rfl, bl, be, hl, he, hs, rfl⟩, by simp⟩

theorem dataPayload_parses (md : DataMode) :
    Parses (fun v n => (u32 v n).bind fun k v n => (leNat k v n).bind fun bs v n =>
      .ok (Data.mk (leBytes k bs) md) v n)
      (fun d bs => ∃ init, Vec Byte init bs ∧ d = Data.mk init md) := by
  exact (u32_parses.bind fun k => (leNat_parses k).map fun bs =>
    Data.mk (leBytes k bs) md).congr fun d bs => by
      constructor
      · rintro ⟨k, b₁, b₂, hk, ⟨v, ⟨hlen, rfl⟩, rfl⟩, rfl⟩
        subst k
        rw [leBytes_pack]
        exact ⟨b₂, ⟨b₁, b₂, hk, seq_byte_iff.2 rfl, rfl⟩, rfl⟩
      · rintro ⟨init, ⟨b₁, b₂, hk, hs, rfl⟩, rfl⟩
        have he := seq_byte_iff.1 hs
        subst b₂
        exact ⟨init.length, b₁, init, hk,
          ⟨pack init, ⟨rfl, rfl⟩, by rw [leBytes_pack]⟩, rfl⟩

theorem data_parses : Parses data DataB := by
  constructor
  · intro bs d v n h
    obtain ⟨f, v₁, n₁, hf, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨bf, rest₁, rfl, hfB, rfl, rfl⟩ := u32_parses.sound hf
    obtain ⟨md, v₂, n₂, hm, h₂⟩ := Res.bind_eq_ok.1 h₁
    simp only [Bool.cond_eq_ite, Nat.beq_eq] at hm
    split at hm
    · rename_i hf0
      subst f
      obtain ⟨off, be, rest₂, rfl, he, rfl, rfl, rfl⟩ := expr_parses.map_sound hm
      obtain ⟨bv, rest, rfl, ⟨init, hv, rfl⟩, rfl, rfl⟩ := (dataPayload_parses _).sound h₂
      exact ⟨bf ++ be ++ bv, rest, by simp, .d0 hfB he hv, rfl, rfl⟩
    · split at hm
      · rename_i hf1
        subst f
        cases hm
        obtain ⟨bv, rest, rfl, ⟨init, hv, rfl⟩, rfl, rfl⟩ := (dataPayload_parses _).sound h₂
        exact ⟨bf ++ bv, rest, by simp, .d1 hfB hv, rfl, rfl⟩
      · split at hm
        · rename_i hf2
          subst f
          obtain ⟨x, v₃, n₃, hx, h₃⟩ := Res.bind_eq_ok.1 hm
          obtain ⟨bx, rest₂, rfl, hxB, rfl, rfl⟩ := u32_parses.sound hx
          obtain ⟨off, be, rest₃, rfl, he, rfl, rfl, rfl⟩ := expr_parses.map_sound h₃
          obtain ⟨bv, rest, rfl, ⟨init, hv, rfl⟩, rfl, rfl⟩ := (dataPayload_parses _).sound h₂
          exact ⟨bf ++ bx ++ be ++ bv, rest, by simp, .d2 hfB hxB he hv, rfl, rfl⟩
        · cases hm
  · intro d pre rest h
    cases h with
    | @d0 off init bf be bv hf he hv =>
      simp only [data, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change ((expr (pack (be ++ (bv ++ rest))) (be ++ (bv ++ rest)).length).bind _).bind _ = _
      rw [expr_parses.complete _ he, Res.bind_ok, Res.bind_ok]
      exact (dataPayload_parses _).complete rest ⟨init, hv, rfl⟩
    | @d1 init bf bv hf hv =>
      simp only [data, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      exact (dataPayload_parses _).complete rest ⟨init, hv, rfl⟩
    | @d2 x off init bf bx be bv hf hx he hv =>
      simp only [data, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change ((u32 (pack (bx ++ (be ++ (bv ++ rest))))
        (bx ++ (be ++ (bv ++ rest))).length).bind _).bind _ = _
      rw [u32_parses.complete _ hx, Res.bind_ok, expr_parses.complete _ he,
        Res.bind_ok, Res.bind_ok]
      exact (dataPayload_parses _).complete rest ⟨init, hv, rfl⟩

theorem elemKind_parses : Parses elemKind ElemKindB := by
  constructor
  · intro bs t v n h
    obtain ⟨b, v₁, n₁, hb, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, rest, rfl, ⟨b, rfl, rfl⟩, rfl, rfl⟩ := byte_parses.sound hb
    cases h₀ : Nat.beq b.toNat 0
    · simp [h₀] at h₁
    · simp only [h₀, Bool.cond_true, Res.ok.injEq] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      have he : b = 0 := UInt8.toNat_inj.1 (beq_true.1 h₀)
      subst he
      exact ⟨[0], rest, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
  · rintro t _ rest ⟨rfl, rfl⟩
    simp only [elemKind, List.cons_append, List.nil_append, byte, List.length_cons,
      land_pack_cons, shiftRight_pack_cons, Res.bind_ok]
    rfl

theorem elem_parses : Parses elem ElemB := by
  have hvu := vec_parses u32_parses fun _ _ h => ULeb.ne_nil h
  have hvi := hvu.map funcInits
  have hve := vec_parses expr_parses fun _ _ h => ExprB.ne_nil h
  constructor
  · intro bs e v n h
    obtain ⟨f, v₁, n₁, hf, h₁⟩ := Res.bind_eq_ok.1 h
    obtain ⟨bf, rest₁, rfl, hfB, rfl, rfl⟩ := u32_parses.sound hf
    cases hbound : Nat.blt 7 f
    · simp only [hbound, Bool.cond_false] at h₁
      have hfCases : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by
        have := blt_false.1 hbound
        omega
      rcases hfCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨md, v₂, n₂, hm, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨off, be, rest₂, rfl, he, rfl, rfl, rfl⟩ := expr_parses.map_sound hm
        obtain ⟨es, bv, rest, rfl, ⟨ys, hv, rfl⟩, rfl, rfl, rfl⟩ := hvi.map_sound h₂
        exact ⟨bf ++ be ++ bv, rest, by simp, .e0 hfB he hv, rfl, rfl⟩
      · change (elemKind (pack rest₁) rest₁.length).bind _ = _ at h₁
        obtain ⟨t, v₂, n₂, ht, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨bk, rest₂, rfl, htB, rfl, rfl⟩ := elemKind_parses.sound ht
        obtain ⟨es, bv, rest, rfl, ⟨ys, hv, rfl⟩, rfl, rfl, rfl⟩ := hvi.map_sound h₂
        exact ⟨bf ++ bk ++ bv, rest, by simp, .e1 hfB htB hv, rfl, rfl⟩
      · obtain ⟨md, v₂, n₂, hm, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨x, v₃, n₃, hx, h₃⟩ := Res.bind_eq_ok.1 hm
        obtain ⟨bx, rest₂, rfl, hxB, rfl, rfl⟩ := u32_parses.sound hx
        obtain ⟨off, be, rest₃, rfl, he, rfl, rfl, rfl⟩ := expr_parses.map_sound h₃
        obtain ⟨t, v₄, n₄, ht, h₄⟩ := Res.bind_eq_ok.1 h₂
        obtain ⟨bk, rest₄, rfl, htB, rfl, rfl⟩ := elemKind_parses.sound ht
        obtain ⟨es, bv, rest, rfl, ⟨ys, hv, rfl⟩, rfl, rfl, rfl⟩ := hvi.map_sound h₄
        exact ⟨bf ++ bx ++ be ++ bk ++ bv, rest, by simp, .e2 hfB hxB he htB hv, rfl, rfl⟩
      · change (elemKind (pack rest₁) rest₁.length).bind _ = _ at h₁
        obtain ⟨t, v₂, n₂, ht, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨bk, rest₂, rfl, htB, rfl, rfl⟩ := elemKind_parses.sound ht
        obtain ⟨es, bv, rest, rfl, ⟨ys, hv, rfl⟩, rfl, rfl, rfl⟩ := hvi.map_sound h₂
        exact ⟨bf ++ bk ++ bv, rest, by simp, .e3 hfB htB hv, rfl, rfl⟩
      · obtain ⟨md, v₂, n₂, hm, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨off, be, rest₂, rfl, he, rfl, rfl, rfl⟩ := expr_parses.map_sound hm
        obtain ⟨es, bv, rest, rfl, hv, rfl, rfl, rfl⟩ := hve.map_sound h₂
        exact ⟨bf ++ be ++ bv, rest, by simp, .e4 hfB he hv, rfl, rfl⟩
      · change (refType (pack rest₁) rest₁.length).bind _ = _ at h₁
        obtain ⟨t, v₂, n₂, ht, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨bt, rest₂, rfl, htB, rfl, rfl⟩ := refType_parses.sound ht
        obtain ⟨es, bv, rest, rfl, hv, rfl, rfl, rfl⟩ := hve.map_sound h₂
        exact ⟨bf ++ bt ++ bv, rest, by simp, .e5 hfB htB hv, rfl, rfl⟩
      · obtain ⟨md, v₂, n₂, hm, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨x, v₃, n₃, hx, h₃⟩ := Res.bind_eq_ok.1 hm
        obtain ⟨bx, rest₂, rfl, hxB, rfl, rfl⟩ := u32_parses.sound hx
        obtain ⟨off, be, rest₃, rfl, he, rfl, rfl, rfl⟩ := expr_parses.map_sound h₃
        obtain ⟨t, v₄, n₄, ht, h₄⟩ := Res.bind_eq_ok.1 h₂
        obtain ⟨bt, rest₄, rfl, htB, rfl, rfl⟩ := refType_parses.sound ht
        obtain ⟨es, bv, rest, rfl, hv, rfl, rfl, rfl⟩ := hve.map_sound h₄
        exact ⟨bf ++ bx ++ be ++ bt ++ bv, rest, by simp, .e6 hfB hxB he htB hv, rfl, rfl⟩
      · change (refType (pack rest₁) rest₁.length).bind _ = _ at h₁
        obtain ⟨t, v₂, n₂, ht, h₂⟩ := Res.bind_eq_ok.1 h₁
        obtain ⟨bt, rest₂, rfl, htB, rfl, rfl⟩ := refType_parses.sound ht
        obtain ⟨es, bv, rest, rfl, hv, rfl, rfl, rfl⟩ := hve.map_sound h₂
        exact ⟨bf ++ bt ++ bv, rest, by simp, .e7 hfB htB hv, rfl, rfl⟩
    · simp [hbound] at h₁
  · intro e pre rest h
    cases h with
    | @e0 off ys bf be bv hf he hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change ((expr (pack (be ++ (bv ++ rest))) (be ++ (bv ++ rest)).length).bind _).bind _ = _
      rw [expr_parses.complete _ he, Res.bind_ok, Res.bind_ok]
      change ((vec u32 (pack (bv ++ rest)) (bv ++ rest).length).bind _).bind _ = _
      rw [hvu.complete rest hv]
      rfl
    | @e1 t ys bf bk bv hf ht hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change (elemKind (pack (bk ++ (bv ++ rest))) (bk ++ (bv ++ rest)).length).bind _ = _
      rw [elemKind_parses.complete _ ht, Res.bind_ok, hvu.complete rest hv]
      rfl
    | @e2 x off t ys bf bx be bk bv hf hx he ht hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change ((u32 (pack (bx ++ (be ++ (bk ++ (bv ++ rest)))))
        (bx ++ (be ++ (bk ++ (bv ++ rest)))).length).bind _).bind _ = _
      rw [u32_parses.complete _ hx, Res.bind_ok, expr_parses.complete _ he,
        Res.bind_ok, Res.bind_ok]
      change (elemKind (pack (bk ++ (bv ++ rest))) (bk ++ (bv ++ rest)).length).bind _ = _
      rw [elemKind_parses.complete _ ht, Res.bind_ok, hvu.complete rest hv]
      rfl
    | @e3 t ys bf bk bv hf ht hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change (elemKind (pack (bk ++ (bv ++ rest))) (bk ++ (bv ++ rest)).length).bind _ = _
      rw [elemKind_parses.complete _ ht, Res.bind_ok, hvu.complete rest hv]
      rfl
    | @e4 off es bf be bv hf he hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change ((expr (pack (be ++ (bv ++ rest))) (be ++ (bv ++ rest)).length).bind _).bind _ = _
      rw [expr_parses.complete _ he, Res.bind_ok, Res.bind_ok]
      change (vec expr (pack (bv ++ rest)) (bv ++ rest).length).bind _ = _
      rw [hve.complete rest hv]
      rfl
    | @e5 t es bf bt bv hf ht hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change (refType (pack (bt ++ (bv ++ rest))) (bt ++ (bv ++ rest)).length).bind _ = _
      rw [refType_parses.complete _ ht, Res.bind_ok, hve.complete rest hv]
      rfl
    | @e6 x off t es bf bx be bt bv hf hx he ht hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change ((u32 (pack (bx ++ (be ++ (bt ++ (bv ++ rest)))))
        (bx ++ (be ++ (bt ++ (bv ++ rest)))).length).bind _).bind _ = _
      rw [u32_parses.complete _ hx, Res.bind_ok, expr_parses.complete _ he,
        Res.bind_ok, Res.bind_ok]
      change (refType (pack (bt ++ (bv ++ rest))) (bt ++ (bv ++ rest)).length).bind _ = _
      rw [refType_parses.complete _ ht, Res.bind_ok, hve.complete rest hv]
      rfl
    | @e7 t es bf bt bv hf ht hv =>
      simp only [elem, List.append_assoc]
      rw [u32_parses.complete _ hf, Res.bind_ok]
      change (refType (pack (bt ++ (bv ++ rest))) (bt ++ (bv ++ rest)).length).bind _ = _
      rw [refType_parses.complete _ ht, Res.bind_ok, hve.complete rest hv]
      rfl

end FVA.Wasm.Decode
