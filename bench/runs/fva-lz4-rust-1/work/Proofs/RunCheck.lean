import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs.Samples

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

def resultCheck (es : List AInstr) (r : BitVec 32) : Bool :=
  match es with
  | [e] => decide (toVal e = some (.i32 r))
  | _ => false

theorem resultCheck_sound {es : List AInstr} {r : BitVec 32}
    (h : resultCheck es r = true) : es = vals [.i32 r] := by
  cases es with
  | nil => simp [resultCheck] at h
  | cons e es =>
    cases es with
    | cons a tail => simp [resultCheck] at h
    | nil =>
      have hv : toVal e = some (.i32 r) := of_decide_eq_true h
      rw [eq_instr_of_toVal hv]
      rfl

end Proofs.Samples
