-- Generated proof certificates; every equation is kernel checked.
import Proofs.Cases
import Proofs.Composition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Certificates
open Wasm Verification
namespace C0
def testcase : Case := ⟨[],32,4294967295,131072,1048576,165⟩
def s0 : State := start Artifact.functions (initial testcase) 131072 1048576 0 32
def s8 : State := { fn := 0, pc := 8, locals := [131072,1048576,0,32,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [0,32], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s16 : State := { fn := 0, pc := 580, locals := [131072,1048576,0,32,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [], labels := [], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s17 : State := { fn := 0, pc := 581, locals := [131072,1048576,0,32,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [4294967295], labels := [], calls := [], mem := initial testcase, trace := ([] : List Access) }
theorem a0 : advance Artifact.functions 8 s0 = some s8 := by rfl
theorem a8 : advance Artifact.functions 8 s8 = some s16 := by rfl
theorem a16 : advance Artifact.functions 1 s16 = some s17 := by rfl
theorem execution : execute testcase = some (4294967295,s17) := by
  change run Artifact.functions 1000 s0 = some (4294967295,s17)
  have h17 : run Artifact.functions 983 s17 = some (4294967295,s17) := by rfl
  have h16 : run Artifact.functions 984 s16 = some (4294967295,s17) :=
    run_of_advance Artifact.functions 1 983 s16 s17 (4294967295,s17) a16 h17
  have h8 : run Artifact.functions 992 s8 = some (4294967295,s17) :=
    run_of_advance Artifact.functions 8 984 s8 s16 (4294967295,s17) a8 h16
  have h0 : run Artifact.functions 1000 s0 = some (4294967295,s17) :=
    run_of_advance Artifact.functions 8 992 s0 s8 (4294967295,s17) a0 h8
  exact h0
theorem checked : checks testcase = true := by
  unfold checks
  rw [execution]
  rfl
end C0
end Certificates
