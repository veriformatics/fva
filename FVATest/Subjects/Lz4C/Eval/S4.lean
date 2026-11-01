import FVATest.Subjects.Lz4C.Eval.S3

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem match_code : matchLoop = wcLoop 17 2 3 [.br 1] := by kernel_rfl

theorem main_tail : body4.drop 1 = [] := by kernel_rfl

theorem s4 : MatchWildS4 := by
  intro C H st inst ls a ma mem q m e hdl hsl hel hcall hfun hm hmem hqe hd hs hsize
  have hk := chunks_spec hqe
  change Until H _ _ ((ctx5 C).fill ⟨st, ⟨ls, inst⟩, [.plain matchLoop]⟩)
  rw [match_code]
  apply (wc_until H (ctx5 C) st inst ls a ma mem 17 2 3 q m e (chunks q e) [.br 1] []
    (by decide) (by decide) (by decide) hdl hsl hel hcall hfun hm hmem hd hs hsize
    hk.1 hk.2.1 hk.2.2).trans
  intro c hc
  subst c
  change Until H _ _ ((ctx4 C).fill ⟨_, _,
    .label 0 [mainLoop] [.label 0 [wcLoop 17 2 3 [.br 1]] [.plain (.br 1)]] ::
      (body4.drop 1).map .plain⟩)
  rw [main_tail]
  wasm_eval 1 [block_simp]
  · simp [TraceOK, AccessOK]
  · exact .done rfl

#print axioms s4

end Subjects.Lz4C.Eval
