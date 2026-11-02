import FVATest.Subjects.GlmIround.Proof
import FVA.Proof.Lib.Walk

/-! D55: `wasm_step1` on T7's call. On concrete inputs it evaluates the steps simp leaves open
(the `f64.add` and `i32.trunc_sat_f64_s` of `iround`), so `wasm_run []` reaches the result; on
a symbolic input it names the instruction whose step needs a fact. -/

namespace Subjects.GlmCall

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Subjects.GlmIround

set_option maxRecDepth 100000

theorem iround_steps (H : HostSem) :
    Must H (fun o => ∃ s, o = .returned s [.i32 1]) (invokeConfig alloc.1 0 [.f64 belowHalf]) := by
  unfold invokeConfig
  wasm_run []
  exact Must.done (o := .returned _ [.i32 1]) ⟨rfl, rfl⟩ ⟨_, rfl⟩

/--
error: wasm_step1: the next step at `AInstr.invoke 0` is not computed: give the facts its branch
needs (memory reads, locals, conditions) as lemmas, or state the call on concrete inputs (then the
step is evaluated)
-/
#guard_msgs (whitespace := lax) in
example (H : HostSem) (x : BitVec 64) :
    Must H (fun _ => True) (invokeConfig alloc.1 0 [.f64 x]) := by
  unfold invokeConfig
  wasm_step1 []

end Subjects.GlmCall
