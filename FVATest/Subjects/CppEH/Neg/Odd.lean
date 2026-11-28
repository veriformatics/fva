import FVATest.Subjects.CppEH.Proof
/-! Negative: the odd result is pinned. Claiming `x ^^^ 0xa5a5a5a4` (one bit off; witness x = 1:
2779096484 vs 2779096485) along the same proof path must not prove: the chain's final value is
`x ^^^ 0xa5a5a5a5`, and the closing equation differs. -/
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi FVA.Wasm.Num Subjects.CppEH
example (x : BitVec 32) (hx : x.toNat % 2 = 1) :
    SysMust ((world Lifted.module 0).restrict (E Lifted.module 0)) true
      (fun o => ∃ τ s, o = .returned τ s [.i32 (x ^^^ 0xa5a5a5a4)])
      (start, (MState.ofInvoke inst.1 133 [.i32 x]).abs) :=
  odd x hx (fun σ s => ⟨σ, s, rfl⟩)
