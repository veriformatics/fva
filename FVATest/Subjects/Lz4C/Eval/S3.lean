import FVATest.Subjects.Lz4C.Eval.Wild

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem lit_code : litLoop = wcLoop 3 4 17 [] := by kernel_rfl

theorem lit_entry_code : (body7.drop 2).map AInstr.plain =
    .plain litLoop :: (body7.drop 3).map .plain := by kernel_rfl

theorem s3 : LitWildS3 := by
  intro C H st inst ls a ma mem q m e hdl hsl hel hcall hfun hm hmem hqe hd hs hsize
  have hk := chunks_spec hqe
  change Until H _ _ ((ctx7 C).fill ⟨st, ⟨ls, inst⟩, (body7.drop 2).map .plain⟩)
  rw [lit_entry_code, lit_code]
  apply (wc_until H (ctx7 C) st inst ls a ma mem 3 4 17 q m e (chunks q e) []
    ((body7.drop 3).map .plain) (by decide) (by decide) (by decide)
    hdl hsl hel hcall hfun hm hmem hd hs hsize hk.1 hk.2.1 hk.2.2).trans
  intro c hc
  subst c
  wasm_eval 1 [block_simp]
  · simp [TraceOK, AccessOK]
  · exact .done rfl

#print axioms s3

end Subjects.Lz4C.Eval
