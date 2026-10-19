import Semantics
import Artifact
import Arithmetic
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace SatAdd
private theorem execution (a b : Word) : invoke artifact a b = some (result a b) := by
  change some (if ((if b.slt 0 then 1 else 0 : Word) ^^^
      (if (a+b).slt a then 1 else 0 : Word)) = 0 then a+b
    else (a+b).sshiftRight 31 ^^^ 2147483648) = some (result a b)
  dsimp only [result]
  cases (a+b).slt a <;> cases b.slt 0 <;> rfl

theorem artifact_correct : Requirements artifact := by
  intro a b
  refine ⟨result a b, execution a b, ?_⟩
  have h := result_correct a b
  constructor
  · intro hs
    split at h <;> (try split at h) <;> omega
  constructor
  · intro hs
    split at h <;> (try split at h) <;> omega
  · intro hs
    split at h <;> (try split at h) <;> omega
end SatAdd
#print axioms SatAdd.artifact_correct
