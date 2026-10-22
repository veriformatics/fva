import FVA.Proof.Numerics.Basic

/-!
# The NaN class of a result, decided (contract U4 D6)

`nans F zs` is the canonical class when every NaN operand is canonical, else the arithmetic
class; `nanMember` decides membership, so a chooser or a test can check an allowed NaN result
without the spec's classical `if`.
-/

namespace FVA.Wasm.Num

open FVal

/-- Every NaN in `zs` has the canonical payload. -/
def allCanonical (F : FloatFormat) (zs : List FVal) : Bool :=
  zs.all fun
    | .nan _ n => n == F.canon
    | _ => true

/-- `v ∈ nans F zs`, decided. -/
def nanMember (F : FloatFormat) (zs : List FVal) : FVal → Bool
  | .nan _ n => bif allCanonical F zs then n == F.canon
    else decide (F.canon ≤ n) && decide (n < 2 ^ F.M)
  | _ => false

theorem allCanonical_iff (F : FloatFormat) (zs : List FVal) :
    allCanonical F zs = true ↔ ∀ z ∈ zs, ∀ s n, z = nan s n → n = F.canon := by
  unfold allCanonical
  rw [List.all_eq_true]
  constructor
  · intro h z hz s n hzn
    have := h z hz
    subst hzn
    simpa using this
  · intro h z hz
    cases z with
    | nan s n => simpa using h _ hz s n rfl
    | _ => rfl

theorem mem_nans_iff (F : FloatFormat) (zs : List FVal) (v : FVal) :
    v ∈ nans F zs ↔ nanMember F zs v = true := by
  unfold nans
  by_cases h : ∀ z ∈ zs, ∀ s n, z = nan s n → n = F.canon
  · have hb := (allCanonical_iff F zs).2 h
    simp only [eq_true h, ↓reduceIte]
    cases v with
    | nan s n => cases s <;> simp [nanMember, hb]
    | _ => simp [nanMember]
  · have hb : allCanonical F zs = false := by
      rw [← Bool.not_eq_true, allCanonical_iff]; exact h
    simp only [eq_false h, ↓reduceIte]
    cases v with
    | nan s n => cases s <;> simp [nanMember, hb]
    | _ => simp [nanMember]

end FVA.Wasm.Num
