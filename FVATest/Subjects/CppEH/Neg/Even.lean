import FVATest.Subjects.CppEH.Proof
/-! Negative: the even result is pinned. Claiming `x` itself (witness x = 0: 1 vs 0) along the
same proof path must not prove: the chain's final value is `x ||| 1`, and the closing equation
differs. -/
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi FVA.Wasm.Num Subjects.CppEH
example (x : BitVec 32) (hx : x.toNat % 2 = 0) :
    SysMust ((world Lifted.module 0).restrict (E Lifted.module 0)) true
      (fun o => ∃ τ s, o = .returned τ s [.i32 x])
      (start, (MState.ofInvoke inst.1 133 [.i32 x]).abs) :=
  even x hx (fun σ s => ⟨σ, s, rfl⟩)
