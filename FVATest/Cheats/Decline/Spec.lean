import FVA.Spec.ClaimAttr

/-! Cheat Decline (D61). -/

namespace Cheats.Decline

/-- A false arithmetic fact: what the cheat's proof claims. No lifted module (so also `[vacuous]`
and `[link]`): a `decode_eq` in the export makes lean4lean decline on the decoder's string
literals before it reaches the proof. -/
@[fva_claim]
def holds : Prop := (1 : Nat) = 2

end Cheats.Decline
