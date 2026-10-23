import FVA.Proof.Valid.Sequence

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

namespace InvokeProof

theorem emptyInstance (s : Store) : ModuleInstT s {} {} := by
  constructor <;> simp_all

theorem emptyFrame (s : Store) : FrameT s ⟨[], {}⟩ {} :=
  ⟨{}, [], emptyInstance s, .nil, rfl⟩

end InvokeProof

/-- Calling a typed address in a valid store starts with a typed argument stack. -/
theorem invocationOK : InvocationOK := by
  intro s a fi args hs ha hargs
  refine ⟨hs, {}, InvokeProof.emptyFrame s, ?_⟩
  exact ASeqT.snoc (t₀ := []) (ASeqT.values hargs) (Matches.refl _) (.invoke ha)

end FVA.Wasm.Valid
