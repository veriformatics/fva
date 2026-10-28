-- Generated proof certificates; every equation is kernel checked.
import Proofs.Cases
import Proofs.Composition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Certificates
open Wasm Verification
namespace C3
def testcase : Case := ⟨[1],0,4294967295,131072,1048576,165⟩
def s0 : State := start Artifact.functions (initial testcase) 131072 1048576 1 0
def s8 : State := { fn := 0, pc := 8, locals := [131072,1048576,1,0,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [0,0], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s16 : State := { fn := 0, pc := 16, locals := [131072,1048576,1,0,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [0], labels := [⟨11,23,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def t1 : List Access := ⟨false,131072,1⟩::([] : List Access)
def s22 : State := { fn := 0, pc := 22, locals := [131072,1048576,1,0,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [4294967295], labels := [⟨11,23,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
theorem a0 : advance Artifact.functions 8 s0 = some s8 := by rfl
theorem a8 : advance Artifact.functions 8 s8 = some s16 := by rfl
theorem a16 : advance Artifact.functions 6 s16 = some s22 := by rfl
theorem execution : execute testcase = some (4294967295,s22) := by
  change run Artifact.functions 1000 s0 = some (4294967295,s22)
  have h22 : run Artifact.functions 978 s22 = some (4294967295,s22) := by rfl
  have h16 : run Artifact.functions 984 s16 = some (4294967295,s22) :=
    run_of_advance Artifact.functions 6 978 s16 s22 (4294967295,s22) a16 h22
  have h8 : run Artifact.functions 992 s8 = some (4294967295,s22) :=
    run_of_advance Artifact.functions 8 984 s8 s16 (4294967295,s22) a8 h16
  have h0 : run Artifact.functions 1000 s0 = some (4294967295,s22) :=
    run_of_advance Artifact.functions 8 992 s0 s8 (4294967295,s22) a0 h8
  exact h0
theorem checked : checks testcase = true := by
  unfold checks
  rw [execution]
  rfl
end C3
end Certificates
