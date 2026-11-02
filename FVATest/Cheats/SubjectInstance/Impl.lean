/-! A Lean-native subject (declared with `--subject`) whose instance and coercion decide what the
spec's `≤` and cast mean: an order where everything is below everything, a cast to 0. -/

namespace Cheats.SubjectInstance

structure Box where
  v : Nat

instance : LE Box := ⟨fun _ _ => True⟩

/-- Cast to `Nat`: always 0. -/
@[coe] def Box.toNat (_ : Box) : Nat := 0

instance : Coe Box Nat := ⟨Box.toNat⟩

def Box.grow (b : Box) : Box := ⟨b.v + 1⟩

end Cheats.SubjectInstance
