-- Generated proof certificates; every equation is kernel checked.
import Proofs.Cases
import Proofs.Composition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Certificates
open Wasm Verification
namespace C2
def testcase : Case := ⟨[0],32,0,131072,1048576,165⟩
def s0 : State := start Artifact.functions (initial testcase) 131072 1048576 1 32
def s8 : State := { fn := 0, pc := 8, locals := [131072,1048576,1,32,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [0,32], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s16 : State := { fn := 0, pc := 27, locals := [131072,1048576,1,32,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s24 : State := { fn := 0, pc := 35, locals := [131072,1048576,1,32,4294967295,1048608,1048576,0,0,0,0,0,0,0,0,0,0,0,0], stack := [131072], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s32 : State := { fn := 0, pc := 43, locals := [131072,1048576,1,32,4294967295,1048608,1048576,131073,131057,0,0,0,0,0,0,0,0,0,0], stack := [4294967291,1048608], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s40 : State := { fn := 0, pc := 51, locals := [131072,1048576,1,32,4294967295,1048608,1048576,131073,131057,1048603,1048601,0,0,0,0,0,0,0,0], stack := [4294967292,131073], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s48 : State := { fn := 0, pc := 59, locals := [131072,1048576,1,32,4294967295,1048608,1048576,131073,131057,1048603,1048601,131069,131065,0,0,0,0,0,0], stack := [4294967284,1048608], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s56 : State := { fn := 0, pc := 67, locals := [131072,1048576,1,32,131072,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,0,0,0,0], stack := [], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s64 : State := { fn := 0, pc := 75, locals := [131072,1048576,1,1048576,131072,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,0,0,0,0], stack := [1,131072], labels := [⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def t1 : List Access := ⟨false,131072,1⟩::([] : List Access)
def s72 : State := { fn := 0, pc := 83, locals := [131072,1048576,1,1048576,131072,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,0,0], stack := [0], labels := [⟨81,174,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s80 : State := { fn := 0, pc := 91, locals := [131072,1048576,0,1048576,131072,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,0,0], stack := [], labels := [⟨91,98,0,false⟩,⟨81,174,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s88 : State := { fn := 0, pc := 252, locals := [131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,0,0], stack := [], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s96 : State := { fn := 0, pc := 260, locals := [131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,1048576,0], stack := [], labels := [⟨253,267,0,false⟩,⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s104 : State := { fn := 0, pc := 268, locals := [131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,1048576,131073], stack := [], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s112 : State := { fn := 0, pc := 276, locals := [131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,1048576,131073], stack := [1048608,1048576], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s120 : State := { fn := 2, pc := 2, locals := [1048576,131073,0,0,0,0,0], stack := [], labels := [⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,1048576,131073],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t1 }
def s128 : State := { fn := 2, pc := 199, locals := [1048576,131073,0,0,0,0,0], stack := [1048576], labels := [], calls := [⟨0,282,[131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,1048576,131073],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t1 }
def s133 : State := { fn := 0, pc := 286, locals := [131072,1048576,0,1048576,131073,1048608,1048576,131073,131057,1048603,1048601,131069,131065,1048596,131058,131073,0,1048576,131073], stack := [0], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
theorem a0 : advance Artifact.functions 8 s0 = some s8 := by rfl
theorem a8 : advance Artifact.functions 8 s8 = some s16 := by rfl
theorem a16 : advance Artifact.functions 8 s16 = some s24 := by rfl
theorem a24 : advance Artifact.functions 8 s24 = some s32 := by rfl
theorem a32 : advance Artifact.functions 8 s32 = some s40 := by rfl
theorem a40 : advance Artifact.functions 8 s40 = some s48 := by rfl
theorem a48 : advance Artifact.functions 8 s48 = some s56 := by rfl
theorem a56 : advance Artifact.functions 8 s56 = some s64 := by rfl
theorem a64 : advance Artifact.functions 8 s64 = some s72 := by rfl
theorem a72 : advance Artifact.functions 8 s72 = some s80 := by rfl
theorem a80 : advance Artifact.functions 8 s80 = some s88 := by rfl
theorem a88 : advance Artifact.functions 8 s88 = some s96 := by rfl
theorem a96 : advance Artifact.functions 8 s96 = some s104 := by rfl
theorem a104 : advance Artifact.functions 8 s104 = some s112 := by rfl
theorem a112 : advance Artifact.functions 8 s112 = some s120 := by rfl
theorem a120 : advance Artifact.functions 8 s120 = some s128 := by rfl
theorem a128 : advance Artifact.functions 5 s128 = some s133 := by rfl
theorem execution : execute testcase = some (0,s133) := by
  change run Artifact.functions 1000 s0 = some (0,s133)
  have h133 : run Artifact.functions 867 s133 = some (0,s133) := by rfl
  have h128 : run Artifact.functions 872 s128 = some (0,s133) :=
    run_of_advance Artifact.functions 5 867 s128 s133 (0,s133) a128 h133
  have h120 : run Artifact.functions 880 s120 = some (0,s133) :=
    run_of_advance Artifact.functions 8 872 s120 s128 (0,s133) a120 h128
  have h112 : run Artifact.functions 888 s112 = some (0,s133) :=
    run_of_advance Artifact.functions 8 880 s112 s120 (0,s133) a112 h120
  have h104 : run Artifact.functions 896 s104 = some (0,s133) :=
    run_of_advance Artifact.functions 8 888 s104 s112 (0,s133) a104 h112
  have h96 : run Artifact.functions 904 s96 = some (0,s133) :=
    run_of_advance Artifact.functions 8 896 s96 s104 (0,s133) a96 h104
  have h88 : run Artifact.functions 912 s88 = some (0,s133) :=
    run_of_advance Artifact.functions 8 904 s88 s96 (0,s133) a88 h96
  have h80 : run Artifact.functions 920 s80 = some (0,s133) :=
    run_of_advance Artifact.functions 8 912 s80 s88 (0,s133) a80 h88
  have h72 : run Artifact.functions 928 s72 = some (0,s133) :=
    run_of_advance Artifact.functions 8 920 s72 s80 (0,s133) a72 h80
  have h64 : run Artifact.functions 936 s64 = some (0,s133) :=
    run_of_advance Artifact.functions 8 928 s64 s72 (0,s133) a64 h72
  have h56 : run Artifact.functions 944 s56 = some (0,s133) :=
    run_of_advance Artifact.functions 8 936 s56 s64 (0,s133) a56 h64
  have h48 : run Artifact.functions 952 s48 = some (0,s133) :=
    run_of_advance Artifact.functions 8 944 s48 s56 (0,s133) a48 h56
  have h40 : run Artifact.functions 960 s40 = some (0,s133) :=
    run_of_advance Artifact.functions 8 952 s40 s48 (0,s133) a40 h48
  have h32 : run Artifact.functions 968 s32 = some (0,s133) :=
    run_of_advance Artifact.functions 8 960 s32 s40 (0,s133) a32 h40
  have h24 : run Artifact.functions 976 s24 = some (0,s133) :=
    run_of_advance Artifact.functions 8 968 s24 s32 (0,s133) a24 h32
  have h16 : run Artifact.functions 984 s16 = some (0,s133) :=
    run_of_advance Artifact.functions 8 976 s16 s24 (0,s133) a16 h24
  have h8 : run Artifact.functions 992 s8 = some (0,s133) :=
    run_of_advance Artifact.functions 8 984 s8 s16 (0,s133) a8 h16
  have h0 : run Artifact.functions 1000 s0 = some (0,s133) :=
    run_of_advance Artifact.functions 8 992 s0 s8 (0,s133) a0 h8
  exact h0
theorem checked : checks testcase = true := by
  unfold checks
  rw [execution]
  rfl
end C2
end Certificates
