import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Num

/-- Select a structured instruction's body, or the requested arm of an if. -/
def child (arm : Bool) (i : Option Instr) : List Instr :=
  match i with
  | some (.block _ b) | some (.loop _ b) => b
  | some (.if_ _ t e) => if arm then t else e
  | _ => []

/-- The arithmetic and store in the actual calc_cpm_raw inner-loop else arm.
The function index is 160 = 74 imported functions + defined function 86. -/
noncomputable def cellCode : List Instr :=
  let b := (Lifted.module.funcs[86]?).map Func.body |>.getD []
  let b := child true b[14]?
  let b := child true b[0]?
  let b := child true b[3]?
  let b := child true b[16]?
  let b := child true b[18]?
  (child false b[3]?).take 13

/-- A binary64 value specified by its exact IEEE bit pattern. -/
def dbl (bits : Nat) : FVal := ofBits f64fmt (BitVec.ofNat 64 bits)

/-- The shipped export's cell update loads c, multiplies by exactly 1,000,000,
loads L, divides by L, and stores the result, in that order. This is a structural
claim, not a theorem that the complete function reaches this code. -/
def artifact_arithmetic : Prop :=
  { name := "calc_cpm_raw", desc := ExportDesc.func 160 : Export } ∈ Lifted.module.exports ∧
  cellCode = [
    .localGet 5, .localGet 5, .load .f64 ⟨3, 0⟩,
    .fconst .w64 0x412e848000000000, .fbinop .w64 .mul,
    .localGet 11, .localGet 0, .iconst .w32 3,
    .ibinop .w32 .shl, .ibinop .w32 .add, .load .f64 ⟨3, 0⟩,
    .fbinop .w64 .div, .store .f64 ⟨3, 0⟩]

/-- R1 failure mechanism: c=L=2^1020 are finite positive doubles and the exact
CPM is 1,000,000. Multiplication first overflows to +infinity, which division
preserves. Thus no finite absolute or relative rounding-error bound holds on
R1's unrestricted domain. Reachability in the complete function is demonstrated
by verification/check.R against the unchanged artifact, not proved here. -/
def overflow_witness : Prop :=
  artifact_arithmetic ∧
  (dbl 0x7fb0000000000000).IsNum ∧
  0 < (dbl 0x7fb0000000000000).toReal f64fmt ∧
  (dbl 0x7fb0000000000000).toReal f64fmt /
    (dbl 0x7fb0000000000000).toReal f64fmt * 1000000 = 1000000 ∧
  fmul f64fmt (dbl 0x7fb0000000000000) (dbl 0x412e848000000000) = {.inf false} ∧
  fdiv f64fmt (.inf false) (dbl 0x7fb0000000000000) = {.inf false}

/-- R2 failure mechanism: correctly rounded (10*10^6)/36 and (10/36)*10^6
are adjacent doubles, with the artifact CPM strictly below the R cutoff.
Both samples have exactly 10 reads and the total 20 exceeds 15; the unchanged
R filter rejects this gene (demonstrated in verification/check.R). This theorem
checks the four IEEE operations, their unique results, and their strict order;
it is not a formal semantics or proof of the R interpreter. -/
def threshold_witness : Prop :=
  artifact_arithmetic ∧
  fmul f64fmt (dbl 0x4024000000000000) (dbl 0x412e848000000000) =
    {dbl 0x416312d000000000} ∧
  fdiv f64fmt (dbl 0x416312d000000000) (dbl 0x4042000000000000) =
    {dbl 0x4110f4471c71c71c} ∧
  fdiv f64fmt (dbl 0x4024000000000000) (dbl 0x4042000000000000) =
    {dbl 0x3fd1c71c71c71c72} ∧
  fmul f64fmt (dbl 0x3fd1c71c71c71c72) (dbl 0x412e848000000000) =
    {dbl 0x4110f4471c71c71d} ∧
  (dbl 0x4110f4471c71c71c).toReal f64fmt <
    (dbl 0x4110f4471c71c71d).toReal f64fmt

end Proofs
