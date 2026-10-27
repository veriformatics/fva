import Proofs.Calc.Q0
import Proofs.Calc.Q1
import Proofs.Calc.Q2
import Proofs.Calc.Q3
import Proofs.Calc.Q4
import Proofs.Calc.Q5
import Proofs.Calc.Q6
import Proofs.Calc.Trim0
import Proofs.Calc.Trim1
import Proofs.Calc.Trim2
import Proofs.Calc.Trim4
import Proofs.Calc.Trim5
import Proofs.Calc.Trim6

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem reference_eq : reference Data.counts = 3 := by
  unfold reference
  rw [show List.range 7 = [0, 1, 2, 3, 4, 5, 6] by decide]
  norm_num [List.foldl_cons, List.foldl_nil, uq_0, uq_1, uq_2, uq_3, uq_4, uq_5, uq_6]

end Proofs
