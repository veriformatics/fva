import FVATest.Subjects.Lz4C.Top
import FVATest.Subjects.Lz4C.Cut.Entry
import FVATest.Subjects.Lz4C.Cut.ErrRet
import FVATest.Subjects.Lz4C.Cut.ExtB
import FVATest.Subjects.Lz4C.Eval.Accept

/-! R1–R3 (`Spec.lean`) on the shipped `lz4-c.wasm`: `Top`'s composition of the cutpoint proofs
(`Cut/*` by stepping, `Eval/*` by engine C). Proof side; never read. -/

namespace Subjects.Lz4C

theorem r1_holds : r1 :=
  Top.r1_of Cut.entry Eval.s5 Cut.segA Eval.segB Eval.segC Eval.segD Cut.errRet

theorem r2_holds : r2 :=
  Top.r2_of Cut.entry Eval.s5 Cut.segA Eval.segB Eval.segC Eval.segD Cut.errRet

theorem r3_holds : r3 :=
  Top.r3_of Cut.entry Eval.s5 Cut.segA Eval.segB Eval.segC Eval.segD Cut.errRet

end Subjects.Lz4C
