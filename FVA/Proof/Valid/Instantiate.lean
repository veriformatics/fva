import FVA.Proof.Valid.InstantiateCode

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

namespace InitProof

theorem listExtends_trans {α : Type} {R : α → α → Prop} {xs ys zs : List α}
    (h₁ : ListExtends R xs ys) (h₂ : ListExtends R ys zs)
    (ht : ∀ a b c, R a b → R b c → R a c) : ListExtends R xs zs := by
  intro i a ha
  obtain ⟨b, hb, hab⟩ := h₁ i a ha
  obtain ⟨c, hc, hbc⟩ := h₂ i b hb
  exact ⟨c, hc, ht a b c hab hbc⟩

theorem extends_trans {s₀ s₁ s₂ : Store} (h₁ : s₀.Extends s₁) (h₂ : s₁.Extends s₂) :
    s₀.Extends s₂ := by
  refine ⟨listExtends_trans h₁.1 h₂.1 (fun _ _ _ => Eq.trans),
    listExtends_trans h₁.2.1 h₂.2.1 ?_,
    listExtends_trans h₁.2.2.1 h₂.2.2.1 ?_,
    listExtends_trans h₁.2.2.2.1 h₂.2.2.2.1 ?_,
    listExtends_trans h₁.2.2.2.2.1 h₂.2.2.2.2.1 ?_,
    listExtends_trans h₁.2.2.2.2.2 h₂.2.2.2.2.2 ?_⟩
  · intro a b c hab hbc
    exact ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, Nat.le_trans hab.2.2 hbc.2.2⟩
  · intro a b c hab hbc
    exact ⟨hbc.1.trans hab.1, Nat.le_trans hab.2 hbc.2⟩
  · intro a b c hab hbc
    refine ⟨hbc.1.trans hab.1, ?_⟩
    rcases hab.2 with hv | he
    · exact .inl hv
    · rcases hbc.2 with hv | he'
      · exact .inl (by simpa only [hab.1] using hv)
      · exact .inr (he'.trans he)
  · intro a b c hab hbc
    refine ⟨hbc.1.trans hab.1, ?_⟩
    rcases hbc.2 with he' | he'
    · rcases hab.2 with he | he
      · exact .inl (he'.trans he)
      · exact .inr (he'.trans he)
    · exact .inr he'
  · intro a b c hab hbc
    rcases hbc with he' | he'
    · rcases hab with he | he
      · exact .inl (he'.trans he)
      · exact .inr (he'.trans he)
    · exact .inr he'

theorem preservation_path (pres : Preservation) {H : HostSem} (hh : TypeSoundHost H)
    {c c' : Config} {ts : List ValType} (hc : ConfigOK c ts) (steps : Steps H c c') :
    c.store.Extends c'.store ∧ ConfigOK c' ts := by
  induction steps with
  | refl => exact ⟨Store.Extends.refl _, hc⟩
  | tail h step ih =>
    obtain ⟨hext, htyped⟩ := pres H _ _ ts hh ih.2 step
    exact ⟨extends_trans ih.1 hext, htyped⟩

end InitProof

/-- Instantiation is noncircular: restricted initializers establish allocation validity;
the typed initialization code then inherits preservation along its successful execution. -/
theorem instantiationOK (pres : Preservation) : InstantiationOK := by
  intro H m s s' imports inst hv hh hs hi
  obtain ⟨him, gvals, erefs, s₁, halloc, hg, he, hsteps⟩ := hi
  have hs₁ := congrArg Prod.fst halloc
  have hinst₁ := congrArg Prod.snd halloc
  dsimp only at hs₁ hinst₁
  subst s₁ inst
  obtain ⟨hgv, hev⟩ := InitProof.alloc_values hv him hs gvals erefs hg he
  have hstore := InitProof.alloc_store hv him hs gvals erefs hgv hev
  obtain ⟨C, hinst, hctx⟩ := InitProof.alloc_instance hv him gvals erefs hg.length_eq he.length_eq
  have hcfg : ConfigOK
      ⟨(allocModule s m imports gvals erefs).1,
        ⟨[], (allocModule s m imports gvals erefs).2⟩, (initCode m).map .plain⟩ [] :=
    ⟨hstore, C, InitProof.empty_frame hinst,
      ASeqT.plain ((InitProof.initCode_typed hv).transport hctx)⟩
  obtain ⟨hext, hfinal⟩ := InitProof.preservation_path pres hh hcfg hsteps
  refine ⟨hfinal.1, InitProof.extends_trans (InitProof.alloc_extends _ _ _ _ _) hext, ?_⟩
  obtain ⟨D, hframe, _⟩ := hfinal.2
  obtain ⟨D₀, ts, hinst', _, _⟩ := hframe
  exact ⟨D₀, hinst'⟩

end FVA.Wasm.Valid
