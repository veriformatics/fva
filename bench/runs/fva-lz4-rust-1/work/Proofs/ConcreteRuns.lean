import Proofs.Spec
import Proofs.Execution
import Proofs.RunCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Samples

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

noncomputable def call (e : Example) : Config :=
  invokeConfig (Execution.freshStore.withBytes 131072 e.input) 7
    [.i32 131072, .i32 262144, .i32 (BitVec.ofNat 32 e.input.length),
      .i32 (BitVec.ofNat 32 e.cap)]

noncomputable def runCheck (e : Example) : Bool :=
  match runDet 10000 (call e) with
  | none => false
  | some c => resultCheck c.instrs e.result &&
    match c.store.mems[0]? with
    | none => false
    | some mem => decide
      ((List.range e.output.length).map (fun i => mem.byte (262144 + i)) = e.output)

def domainCheck (e : Example) : Bool := decide
  (131072 + e.input.length ≤ 262144 ∧ 262144 + e.cap ≤ 2097152 ∧
    (e.result.toNat < 2147483648 → e.result.toNat = e.output.length ∧ e.output.length ≤ e.cap))

theorem domains_checked : examples.all domainCheck = true := by kernel_rfl

theorem runs_checked : examples.all runCheck = true := by kernel_rfl


end Proofs.Samples
