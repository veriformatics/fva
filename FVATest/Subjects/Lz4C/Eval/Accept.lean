import FVATest.Subjects.Lz4C.Eval.S5
import FVATest.Subjects.Lz4C.Eval.SegB
import FVATest.Subjects.Lz4C.Eval.SegC
import FVATest.Subjects.Lz4C.Eval.SegD

/-! Engine C's theorems against the frozen statements (`Copy.lean`, `Short.lean`, `Seg.lean`). -/

namespace Subjects.Lz4C.Eval

example : MemcpyS1 := s1
example : MemmoveS2 := s2
example : LitWildS3 := s3
example : MatchWildS4 := s4
example : ShortcutS5 := s5
example : SegB := segB
example : SegC := segC
example : SegD := segD

#print axioms s1
#print axioms s2
#print axioms s3
#print axioms s4
#print axioms s5
#print axioms segB
#print axioms segC
#print axioms segD

end Subjects.Lz4C.Eval
