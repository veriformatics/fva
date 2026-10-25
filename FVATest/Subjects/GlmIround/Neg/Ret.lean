import FVATest.Subjects.GlmIround.Proof
/-! E2: the return value is pinned to the real run. Claiming `iround belowHalf = 0` (the correct
answer, but not what the shipped code returns) must not prove — the module returns 1. -/
open FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.GlmIround
example : Returns Lifted.module "iround" [.f64 belowHalf] [.i32 0] := by
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  rintro H s inst hinst
  obtain ⟨h1, h2⟩ := Prod.mk.inj (instance_alloc rfl rfl rfl rfl hinst)
  subst h1; subst h2
  refine ⟨0, by decide +kernel, ⟨_, rfl, .cons ⟨⟩ .nil⟩, ?_⟩
  refine (must_returned_of_runDet_get (P := fun _ _ => True) (vs := [.i32 0]) (n := 50)
    runSome (by kernel_rfl) trivial).mono ?_
  rintro (⟨s', vs⟩ | s') h
  · exact h.1
  · exact h
