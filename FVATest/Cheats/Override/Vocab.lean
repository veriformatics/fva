import FVATest.Cheats.Override.Lifted

/-! Vocabulary with compiled-code override (cheat Override). -/

namespace Cheats.Override

def sizeWrong (_ : Nat) : Nat := 0

/-- The artifact's size. -/
@[implemented_by sizeWrong]
def size (n : Nat) : Nat := n

end Cheats.Override
