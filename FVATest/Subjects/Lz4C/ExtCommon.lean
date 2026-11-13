import FVATest.Subjects.Lz4C.Ext
import FVA.Proof.Lib.Arith

/-! Facts both checkpoint-1 routes step with: the loop head, `i32` arithmetic on `ofNat` values,
local updates, one-byte reads (proof support; outside the review surface). -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

/-- The loop head: the loop's label holding its whole body, frame `f`. -/
noncomputable def head (C : Context) (s : Store) (f : Frame) : Config :=
  (ctx9 C).fill ⟨s, f, [.label 0 [.loop .empty extBody] (extBody.map .plain)]⟩

theorem getElem?_set_of_ne {α : Type} {l : List α} {i k : Nat} {v : α} (h : k ≠ i) :
    (l.set k v)[i]? = l[i]? := List.getElem?_set_ne h

end Subjects.Lz4C
