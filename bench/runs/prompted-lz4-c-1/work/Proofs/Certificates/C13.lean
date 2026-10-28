-- Generated proof certificates; every equation is kernel checked.
import Proofs.Cases
import Proofs.Composition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Certificates
open Wasm Verification
namespace C13
def testcase : Case := ⟨[3,1,0,80,66,67,68,69,70],64,4294967292,131072,1048576,165⟩
def s0 : State := start Artifact.functions (initial testcase) 131072 1048576 9 64
def s8 : State := { fn := 0, pc := 8, locals := [131072,1048576,9,64,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [0,64], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s16 : State := { fn := 0, pc := 27, locals := [131072,1048576,9,64,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s24 : State := { fn := 0, pc := 35, locals := [131072,1048576,9,64,4294967295,1048640,1048608,0,0,0,0,0,0,0,0,0,0,0,0], stack := [131072], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s32 : State := { fn := 0, pc := 43, locals := [131072,1048576,9,64,4294967295,1048640,1048608,131081,131065,0,0,0,0,0,0,0,0,0,0], stack := [4294967291,1048640], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s40 : State := { fn := 0, pc := 51, locals := [131072,1048576,9,64,4294967295,1048640,1048608,131081,131065,1048635,1048633,0,0,0,0,0,0,0,0], stack := [4294967292,131081], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s48 : State := { fn := 0, pc := 59, locals := [131072,1048576,9,64,4294967295,1048640,1048608,131081,131065,1048635,1048633,131077,131073,0,0,0,0,0,0], stack := [4294967284,1048640], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s56 : State := { fn := 0, pc := 67, locals := [131072,1048576,9,64,131072,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,0,0,0,0], stack := [], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s64 : State := { fn := 0, pc := 75, locals := [131072,1048576,9,1048576,131072,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,0,0,0,0], stack := [1,131072], labels := [⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def t1 : List Access := ⟨false,131072,1⟩::([] : List Access)
def s72 : State := { fn := 0, pc := 83, locals := [131072,1048576,9,1048576,131072,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,0,0,0], stack := [3], labels := [⟨81,174,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s80 : State := { fn := 0, pc := 91, locals := [131072,1048576,0,1048576,131072,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,0,0], stack := [], labels := [⟨91,98,0,false⟩,⟨81,174,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s88 : State := { fn := 0, pc := 252, locals := [131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,0,0], stack := [], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s96 : State := { fn := 0, pc := 260, locals := [131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,0], stack := [], labels := [⟨253,267,0,false⟩,⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s104 : State := { fn := 0, pc := 289, locals := [131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073], stack := [], labels := [⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s112 : State := { fn := 1, pc := 4, locals := [1048576,131073,8,0,0,0,0], stack := [], labels := [⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t1 }
def s120 : State := { fn := 1, pc := 12, locals := [1048576,131073,8,0,0,0,0], stack := [8], labels := [⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t1 }
def s128 : State := { fn := 1, pc := 20, locals := [1048576,131073,8,0,0,8,0], stack := [0], labels := [⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t1 }
def s136 : State := { fn := 1, pc := 28, locals := [1048576,131073,1048576,0,0,8,0], stack := [0,131073,1048576], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t1 }
def t2 : List Access := ⟨false,131073,1⟩::t1
def m3 : Mem := store (initial testcase) 1048576 1 1
def t3 : List Access := ⟨true,1048576,1⟩::t2
def s144 : State := { fn := 1, pc := 36, locals := [1048576,131073,1048576,0,0,8,131073], stack := [131073,1048577], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m3, trace := t3 }
def t4 : List Access := ⟨false,131074,1⟩::t3
def m5 : Mem := store (m3) 1048577 0 1
def t5 : List Access := ⟨true,1048577,1⟩::t4
def s152 : State := { fn := 1, pc := 44, locals := [1048576,131073,1048576,0,0,8,131073], stack := [131073,1048578], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m5, trace := t5 }
def t6 : List Access := ⟨false,131075,1⟩::t5
def m7 : Mem := store (m5) 1048578 80 1
def t7 : List Access := ⟨true,1048578,1⟩::t6
def s160 : State := { fn := 1, pc := 52, locals := [1048576,131073,1048576,0,0,8,131073], stack := [131073,1048579], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m7, trace := t7 }
def t8 : List Access := ⟨false,131076,1⟩::t7
def m9 : Mem := store (m7) 1048579 66 1
def t9 : List Access := ⟨true,1048579,1⟩::t8
def s168 : State := { fn := 1, pc := 60, locals := [1048576,131073,1048576,0,0,8,131073], stack := [4,8], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m9, trace := t9 }
def s176 : State := { fn := 1, pc := 27, locals := [1048576,131073,1048580,0,4,8,131073], stack := [131073,1048580], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m9, trace := t9 }
def t10 : List Access := ⟨false,131077,1⟩::t9
def m11 : Mem := store (m9) 1048580 67 1
def t11 : List Access := ⟨true,1048580,1⟩::t10
def s184 : State := { fn := 1, pc := 35, locals := [1048576,131073,1048580,0,4,8,131077], stack := [1048581], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m11, trace := t11 }
def t12 : List Access := ⟨false,131078,1⟩::t11
def m13 : Mem := store (m11) 1048581 68 1
def t13 : List Access := ⟨true,1048581,1⟩::t12
def s192 : State := { fn := 1, pc := 43, locals := [1048576,131073,1048580,0,4,8,131077], stack := [1048582], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m13, trace := t13 }
def t14 : List Access := ⟨false,131079,1⟩::t13
def m15 : Mem := store (m13) 1048582 69 1
def t15 : List Access := ⟨true,1048582,1⟩::t14
def s200 : State := { fn := 1, pc := 51, locals := [1048576,131073,1048580,0,4,8,131077], stack := [1048583], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m15, trace := t15 }
def t16 : List Access := ⟨false,131080,1⟩::t15
def m17 : Mem := store (m15) 1048583 70 1
def t17 : List Access := ⟨true,1048583,1⟩::t16
def s208 : State := { fn := 1, pc := 59, locals := [1048576,131073,1048580,0,4,8,131077], stack := [4,4,8], labels := [⟨22,63,0,true⟩,⟨11,67,0,false⟩,⟨1,95,0,false⟩], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m17, trace := t17 }
def s216 : State := { fn := 1, pc := 96, locals := [1048576,131073,1048580,0,8,8,131077], stack := [], labels := [], calls := [⟨0,293,[131072,1048576,0,1048576,131073,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073],[],[⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m17, trace := t17 }
def s224 : State := { fn := 0, pc := 299, locals := [131072,1048576,0,1048576,131081,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073], stack := [1048576], labels := [⟨289,305,0,true⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := m17, trace := t17 }
def s232 : State := { fn := 0, pc := 307, locals := [131072,1048576,0,1048584,131081,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,131073,3,1048576,131073], stack := [3], labels := [⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := m17, trace := t17 }
def s240 : State := { fn := 0, pc := 315, locals := [131072,1048576,0,1048584,131075,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,3,3,1048576,131073], stack := [1048576], labels := [⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := m17, trace := t17 }
def t18 : List Access := ⟨false,131073,2⟩::t17
def s248 : State := { fn := 0, pc := 323, locals := [131072,1048576,1048575,1048584,131075,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,3,3,1048576,1], stack := [15,3], labels := [⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := m17, trace := t18 }
def s256 : State := { fn := 0, pc := 575, locals := [131072,1048576,1048575,1048584,131075,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,3,3,1048576,1], stack := [4294967295,131075], labels := [⟨3,579,0,false⟩], calls := [], mem := m17, trace := t18 }
def s262 : State := { fn := 0, pc := 581, locals := [131072,1048576,1048575,1048584,4294967292,1048640,1048608,131081,131065,1048635,1048633,131077,131073,1048628,131066,3,3,1048576,1], stack := [4294967292], labels := [], calls := [], mem := m17, trace := t18 }
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
theorem a128 : advance Artifact.functions 8 s128 = some s136 := by rfl
theorem a136 : advance Artifact.functions 8 s136 = some s144 := by rfl
theorem a144 : advance Artifact.functions 8 s144 = some s152 := by rfl
theorem a152 : advance Artifact.functions 8 s152 = some s160 := by rfl
theorem a160 : advance Artifact.functions 8 s160 = some s168 := by rfl
theorem a168 : advance Artifact.functions 8 s168 = some s176 := by rfl
theorem a176 : advance Artifact.functions 8 s176 = some s184 := by rfl
theorem a184 : advance Artifact.functions 8 s184 = some s192 := by rfl
theorem a192 : advance Artifact.functions 8 s192 = some s200 := by rfl
theorem a200 : advance Artifact.functions 8 s200 = some s208 := by rfl
theorem a208 : advance Artifact.functions 8 s208 = some s216 := by rfl
theorem a216 : advance Artifact.functions 8 s216 = some s224 := by rfl
theorem a224 : advance Artifact.functions 8 s224 = some s232 := by rfl
theorem a232 : advance Artifact.functions 8 s232 = some s240 := by rfl
theorem a240 : advance Artifact.functions 8 s240 = some s248 := by rfl
theorem a248 : advance Artifact.functions 8 s248 = some s256 := by rfl
theorem a256 : advance Artifact.functions 6 s256 = some s262 := by rfl
theorem execution : execute testcase = some (4294967292,s262) := by
  change run Artifact.functions 1000 s0 = some (4294967292,s262)
  have h262 : run Artifact.functions 738 s262 = some (4294967292,s262) := by rfl
  have h256 : run Artifact.functions 744 s256 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 6 738 s256 s262 (4294967292,s262) a256 h262
  have h248 : run Artifact.functions 752 s248 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 744 s248 s256 (4294967292,s262) a248 h256
  have h240 : run Artifact.functions 760 s240 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 752 s240 s248 (4294967292,s262) a240 h248
  have h232 : run Artifact.functions 768 s232 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 760 s232 s240 (4294967292,s262) a232 h240
  have h224 : run Artifact.functions 776 s224 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 768 s224 s232 (4294967292,s262) a224 h232
  have h216 : run Artifact.functions 784 s216 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 776 s216 s224 (4294967292,s262) a216 h224
  have h208 : run Artifact.functions 792 s208 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 784 s208 s216 (4294967292,s262) a208 h216
  have h200 : run Artifact.functions 800 s200 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 792 s200 s208 (4294967292,s262) a200 h208
  have h192 : run Artifact.functions 808 s192 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 800 s192 s200 (4294967292,s262) a192 h200
  have h184 : run Artifact.functions 816 s184 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 808 s184 s192 (4294967292,s262) a184 h192
  have h176 : run Artifact.functions 824 s176 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 816 s176 s184 (4294967292,s262) a176 h184
  have h168 : run Artifact.functions 832 s168 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 824 s168 s176 (4294967292,s262) a168 h176
  have h160 : run Artifact.functions 840 s160 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 832 s160 s168 (4294967292,s262) a160 h168
  have h152 : run Artifact.functions 848 s152 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 840 s152 s160 (4294967292,s262) a152 h160
  have h144 : run Artifact.functions 856 s144 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 848 s144 s152 (4294967292,s262) a144 h152
  have h136 : run Artifact.functions 864 s136 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 856 s136 s144 (4294967292,s262) a136 h144
  have h128 : run Artifact.functions 872 s128 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 864 s128 s136 (4294967292,s262) a128 h136
  have h120 : run Artifact.functions 880 s120 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 872 s120 s128 (4294967292,s262) a120 h128
  have h112 : run Artifact.functions 888 s112 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 880 s112 s120 (4294967292,s262) a112 h120
  have h104 : run Artifact.functions 896 s104 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 888 s104 s112 (4294967292,s262) a104 h112
  have h96 : run Artifact.functions 904 s96 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 896 s96 s104 (4294967292,s262) a96 h104
  have h88 : run Artifact.functions 912 s88 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 904 s88 s96 (4294967292,s262) a88 h96
  have h80 : run Artifact.functions 920 s80 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 912 s80 s88 (4294967292,s262) a80 h88
  have h72 : run Artifact.functions 928 s72 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 920 s72 s80 (4294967292,s262) a72 h80
  have h64 : run Artifact.functions 936 s64 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 928 s64 s72 (4294967292,s262) a64 h72
  have h56 : run Artifact.functions 944 s56 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 936 s56 s64 (4294967292,s262) a56 h64
  have h48 : run Artifact.functions 952 s48 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 944 s48 s56 (4294967292,s262) a48 h56
  have h40 : run Artifact.functions 960 s40 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 952 s40 s48 (4294967292,s262) a40 h48
  have h32 : run Artifact.functions 968 s32 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 960 s32 s40 (4294967292,s262) a32 h40
  have h24 : run Artifact.functions 976 s24 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 968 s24 s32 (4294967292,s262) a24 h32
  have h16 : run Artifact.functions 984 s16 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 976 s16 s24 (4294967292,s262) a16 h24
  have h8 : run Artifact.functions 992 s8 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 984 s8 s16 (4294967292,s262) a8 h16
  have h0 : run Artifact.functions 1000 s0 = some (4294967292,s262) :=
    run_of_advance Artifact.functions 8 992 s0 s8 (4294967292,s262) a0 h8
  exact h0
theorem checked : checks testcase = true := by
  unfold checks
  rw [execution]
  rfl
end C13
end Certificates
