import Proofs.Fixture

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec

/-- The shipped export is function index 160, whose defined body is index 86
(74 function imports). The row helper is defined body 133, index 207. -/
def artifact_binding : Prop :=
  (Lifted.module.imports.filter (fun i => match i.desc with
    | .func _ => true | _ => false)).length = 74 ∧
  Lifted.module.exports.contains ⟨"calc_cpm_raw", .func 160⟩ = true ∧
  Lifted.module.funcs[86]? = some Lifted.func86 ∧
  Lifted.module.funcs[133]? = some Lifted.func133 ∧
  Lifted.module.types[17]? = some ⟨[.num .i32, .num .i32, .num .i32, .num .i32], []⟩ ∧
  Lifted.module.types[4]? = some ⟨[.num .i32, .num .i32, .num .i32], []⟩ ∧
  Lifted.func86.type = 17 ∧ Lifted.func133.type = 4

/-- R1 counterexample: in the explicit linked-state fixture, the actual shipped
function on finite positive c=L=2^1023 writes positive infinity (0x7ff0000000000000).
This is total correctness of the call in that fixture, not a universal loader claim. -/
def r1_overflow : Prop :=
  Num.ofBits Num.f64fmt 0x7fe0000000000000 = .normal false 0 1023 ∧
  0 < (2 : ℝ)^1023 ∧
  (2 : ℝ)^1023 / (2 : ℝ)^1023 * 1000000 = 1000000 ∧
  ∀ H : HostSem,
    CallReturns H (fixtureStore 0x7fe0000000000000 0x7fe0000000000000)
      fixtureInstance "calc_cpm_raw" fixtureArgs
      (fun s vs => vs = [] ∧ outputBits s = 0x7ff0000000000000)

/-- R2 numeric witness: shipped CPM for count 10, library 18 has bits
0x4120f4471c71c71c in the explicit linked-state fixture. -/
def r2_cpm_bits : Prop :=
  ∀ H : HostSem,
    CallReturns H (fixtureStore 0x4024000000000000 0x4032000000000000)
      fixtureInstance "calc_cpm_raw" fixtureArgs
      (fun s vs => vs = [] ∧ outputBits s = 0x4120f4471c71c71c)

/-- R2 rounding failure even with total count 20 >= 15: the artifact result
is strictly less than the cutoff from the documented operation order. The
artifact's absolute error relative to exact 10/18*1e6 is 1/19327352832.
The cutoff expression is a Wasm binary64 model of these two R operations;
the R execution itself is checked by verification/filter.R. -/
def r2_rounding_gap : Prop :=
  r2_cpm_bits ∧
  (∀ H : HostSem, Must H (fun
    | .returned _ vs => vs = [.f64 0x4120f4471c71c71d]
    | .trapped _ => False) cutoffConfig) ∧
  Num.FVal.toReal Num.f64fmt (Num.ofBits Num.f64fmt 0x4120f4471c71c71c) =
    (10 : ℝ) / 18 * 1000000 - 1 / 19327352832 ∧
  Num.FVal.toReal Num.f64fmt (Num.ofBits Num.f64fmt 0x4120f4471c71c71c) <
    Num.FVal.toReal Num.f64fmt (Num.ofBits Num.f64fmt 0x4120f4471c71c71d)

end Proofs
