import Proofs.Context
import FVA.Spec.Numerics.Float

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- Exact-rational model of the last two comparisons of filterByExpr.default.
Inputs are qualifying-sample count, required sample count, total count and minimum total.
This is a reviewed model, not a formal semantics of R; the R script checks both witnesses. -/
def filterDecision (qualifying required total minTotal : ℚ) : Bool :=
  decide (qualifying ≥ required - 1/100000000000000) &&
    decide (total ≥ minTotal - 1/100000000000000)

/-- Model of R's binary64 boundary comparison: actual CPM >= (10 / 18 * 1000000).
Constants are IEEE bit patterns: actual=0x4120f4471c71c71c, 10, 18, 1000000.
It runs in FVA's Wasm numeric semantics; translating R's operators is reviewed manually. -/
def cutoffComparison : Config :=
  ⟨{}, ⟨[], {}⟩, [.plain (.fconst .w64 0x4120f4471c71c71c),
    .plain (.fconst .w64 0x4024000000000000),
    .plain (.fconst .w64 0x4032000000000000), .plain (.fbinop .w64 .div),
    .plain (.fconst .w64 0x412e848000000000), .plain (.fbinop .w64 .mul),
    .plain (.frelop .w64 .ge)]⟩

/-- R1 fails without a range restriction: the exact artifact's calc_cpm_raw, in the
explicit allocated context, writes +infinity for finite positive c=L=2^1023, although
the exact real CPM is 1000000. No finite absolute/relative rounding bound covers this.
Allocation/call execution is proved; LoaderReady and the complete R runtime are not. -/
def r1_counterexample : Prop :=
  CallReturns (fun _ _ _ _ => False) (inputStore huge huge) linked.2 "calc_cpm_raw"
    [.i32 32768, .i32 32800, .i32 32840, .i32 1]
    (fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧
      mem.read 32840 8 = 0x7ff0000000000000) ∧
  (ofBits f64fmt huge).IsNum ∧ 0 < (ofBits f64fmt huge).toReal f64fmt ∧
  (ofBits f64fmt huge).toReal f64fmt / (ofBits f64fmt huge).toReal f64fmt * 1000000 = 1000000

/-- R2's sample-only iff omits the documented total-count condition.
The artifact computes CPM=10 for count 10 and L=1000000; the reviewed filtering suffix
rejects the single-sample gene despite one qualifying sample. The shipped R is also tested. -/
def r2_total_witness : Prop :=
  CallReturns (fun _ _ _ _ => False)
    (inputStore 0x4024000000000000 0x412e848000000000) linked.2 "calc_cpm_raw"
    [.i32 32768, .i32 32800, .i32 32840, .i32 1]
    (fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧
      mem.read 32840 8 = 0x4024000000000000) ∧
  filterDecision 1 1 10 15 = false

/-- R2 also fails as an exact count-threshold rule at a rounding boundary, even when total
count passes: use two samples each with count 10 and L=18, min.count=10, required samples=2.
Each scalar artifact CPM is 0x4120f4471c71c71c; the modeled R cutoff comparison returns false.
The suffix rejects zero qualifying samples and total 20. Matrix replication/R execution are
checked by the test script, not proved by these scalar and suffix-model theorems. -/
def r2_rounding_witness : Prop :=
  CallReturns (fun _ _ _ _ => False)
    (inputStore 0x4024000000000000 0x4032000000000000) linked.2 "calc_cpm_raw"
    [.i32 32768, .i32 32800, .i32 32840, .i32 1]
    (fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧
      mem.read 32840 8 = 0x4120f4471c71c71c) ∧
  Must (fun _ _ _ _ => False)
    (fun | .returned _ vs => vs = [.i32 0] | .trapped _ => False) cutoffComparison ∧
  filterDecision 0 2 20 15 = false

end Proofs
