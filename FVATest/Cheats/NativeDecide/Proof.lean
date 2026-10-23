import FVATest.Cheats.NativeDecide.Spec

/-! Cheat NativeDecide: proofs. -/

namespace Cheats.NativeDecide

theorem small_holds : small := by unfold small; native_decide

end Cheats.NativeDecide
