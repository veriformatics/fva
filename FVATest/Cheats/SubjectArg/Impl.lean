/-! A Lean-native subject whose instances reach the spec only as a subject function's input
(`pick`) or as a `Decidable` instance (a subsingleton): no `[subject]` issue. -/

namespace Cheats.SubjectArg

structure Box where
  v : Nat

instance : Inhabited Box := ⟨⟨7⟩⟩

def pick (α : Type) [Inhabited α] : α := default

def Box.isZero (b : Box) : Prop := b.v = 0

instance : DecidablePred Box.isZero := fun b => inferInstanceAs (Decidable (b.v = 0))

end Cheats.SubjectArg
