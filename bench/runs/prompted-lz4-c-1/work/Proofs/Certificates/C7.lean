-- Generated proof certificates; every equation is kernel checked.
import Proofs.Cases
import Proofs.Composition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Certificates
open Wasm Verification
namespace C7
def testcase : Case := ⟨[240,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],15,15,131072,1048576,165⟩
def s0 : State := start Artifact.functions (initial testcase) 131072 1048576 17 15
def s8 : State := { fn := 0, pc := 8, locals := [131072,1048576,17,15,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [0,15], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s16 : State := { fn := 0, pc := 27, locals := [131072,1048576,17,15,4294967295,0,0,0,0,0,0,0,0,0,0,0,0,0,0], stack := [], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s24 : State := { fn := 0, pc := 35, locals := [131072,1048576,17,15,4294967295,1048591,1048559,0,0,0,0,0,0,0,0,0,0,0,0], stack := [131072], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s32 : State := { fn := 0, pc := 43, locals := [131072,1048576,17,15,4294967295,1048591,1048559,131089,131073,0,0,0,0,0,0,0,0,0,0], stack := [4294967291,1048591], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s40 : State := { fn := 0, pc := 51, locals := [131072,1048576,17,15,4294967295,1048591,1048559,131089,131073,1048586,1048584,0,0,0,0,0,0,0,0], stack := [4294967292,131089], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s48 : State := { fn := 0, pc := 59, locals := [131072,1048576,17,15,4294967295,1048591,1048559,131089,131073,1048586,1048584,131085,131081,0,0,0,0,0,0], stack := [4294967284,1048591], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s56 : State := { fn := 0, pc := 67, locals := [131072,1048576,17,15,131072,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,0,0,0,0], stack := [], labels := [⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def s64 : State := { fn := 0, pc := 75, locals := [131072,1048576,17,1048576,131072,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,0,0,0,0], stack := [1,131072], labels := [⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := ([] : List Access) }
def t1 : List Access := ⟨false,131072,1⟩::([] : List Access)
def s72 : State := { fn := 0, pc := 83, locals := [131072,1048576,17,1048576,131072,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,0,0,0], stack := [240], labels := [⟨81,174,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s80 : State := { fn := 0, pc := 176, locals := [131072,1048576,15,1048576,131072,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,0,0], stack := [], labels := [⟨176,183,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def s88 : State := { fn := 0, pc := 188, locals := [131072,1048576,15,1048576,131072,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,0,0], stack := [131074], labels := [⟨185,195,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t1 }
def t2 : List Access := ⟨false,131073,1⟩::t1
def s96 : State := { fn := 0, pc := 200, locals := [131072,1048576,131074,1048576,131072,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,0,0], stack := [0], labels := [⟨198,207,0,false⟩,⟨197,234,0,false⟩,⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t2 }
def s104 : State := { fn := 0, pc := 236, locals := [131072,1048576,131074,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,0,0], stack := [0], labels := [⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t2 }
def s112 : State := { fn := 0, pc := 244, locals := [131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,0,0], stack := [], labels := [⟨80,250,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t2 }
def s120 : State := { fn := 0, pc := 252, locals := [131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,0,0], stack := [], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t2 }
def s128 : State := { fn := 0, pc := 268, locals := [131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0], stack := [], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t2 }
def s136 : State := { fn := 0, pc := 276, locals := [131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0], stack := [1048591,1048591], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := initial testcase, trace := t2 }
def s144 : State := { fn := 2, pc := 2, locals := [1048576,131074,15,0,0,0,0], stack := [], labels := [⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t2 }
def s152 : State := { fn := 2, pc := 10, locals := [1048576,131074,15,0,0,0,0], stack := [15], labels := [⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t2 }
def s160 : State := { fn := 2, pc := 18, locals := [1048576,131074,15,15,3,0,0], stack := [], labels := [⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t2 }
def s168 : State := { fn := 2, pc := 26, locals := [1048576,131074,15,15,3,131073,1048575], stack := [], labels := [⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t2 }
def s176 : State := { fn := 2, pc := 34, locals := [1048576,131074,15,15,3,131073,1048575], stack := [15,131073,1048590], labels := [⟨29,46,0,true⟩,⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := initial testcase, trace := t2 }
def t3 : List Access := ⟨false,131088,1⟩::t2
def m4 : Mem := store (initial testcase) 1048590 14 1
def t4 : List Access := ⟨true,1048590,1⟩::t3
def s184 : State := { fn := 2, pc := 42, locals := [1048576,131074,15,14,3,131073,1048575], stack := [3], labels := [⟨29,46,0,true⟩,⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m4, trace := t4 }
def s192 : State := { fn := 2, pc := 33, locals := [1048576,131074,15,14,2,131073,1048575], stack := [131073,1048589], labels := [⟨29,46,0,true⟩,⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m4, trace := t4 }
def t5 : List Access := ⟨false,131087,1⟩::t4
def m6 : Mem := store (m4) 1048589 13 1
def t6 : List Access := ⟨true,1048589,1⟩::t5
def s200 : State := { fn := 2, pc := 41, locals := [1048576,131074,15,13,2,131073,1048575], stack := [], labels := [⟨29,46,0,true⟩,⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m6, trace := t6 }
def s208 : State := { fn := 2, pc := 32, locals := [1048576,131074,15,13,1,131073,1048575], stack := [1048588], labels := [⟨29,46,0,true⟩,⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m6, trace := t6 }
def t7 : List Access := ⟨false,131086,1⟩::t6
def m8 : Mem := store (m6) 1048588 12 1
def t8 : List Access := ⟨true,1048588,1⟩::t7
def s216 : State := { fn := 2, pc := 40, locals := [1048576,131074,15,13,1,131073,1048575], stack := [12], labels := [⟨29,46,0,true⟩,⟨12,47,0,false⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m8, trace := t8 }
def s224 : State := { fn := 2, pc := 48, locals := [1048576,131074,15,12,0,131073,1048575], stack := [], labels := [⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m8, trace := t8 }
def s232 : State := { fn := 2, pc := 56, locals := [1048576,131074,15,12,0,131073,131070], stack := [], labels := [⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m8, trace := t8 }
def s240 : State := { fn := 2, pc := 64, locals := [1048576,1048572,15,12,0,131073,131070], stack := [1048584], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m8, trace := t8 }
def s248 : State := { fn := 2, pc := 72, locals := [1048576,1048572,15,12,1048584,131082,131070], stack := [3,131082,1048587], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m8, trace := t8 }
def t9 : List Access := ⟨false,131085,1⟩::t8
def m10 : Mem := store (m8) 1048587 11 1
def t10 : List Access := ⟨true,1048587,1⟩::t9
def s256 : State := { fn := 2, pc := 80, locals := [1048576,1048572,15,12,1048584,131082,131070], stack := [2,131082,1048586], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m10, trace := t10 }
def t11 : List Access := ⟨false,131084,1⟩::t10
def m12 : Mem := store (m10) 1048586 10 1
def t12 : List Access := ⟨true,1048586,1⟩::t11
def s264 : State := { fn := 2, pc := 88, locals := [1048576,1048572,15,12,1048584,131082,131070], stack := [1,131082,1048585], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m12, trace := t12 }
def t13 : List Access := ⟨false,131083,1⟩::t12
def m14 : Mem := store (m12) 1048585 9 1
def t14 : List Access := ⟨true,1048585,1⟩::t13
def t15 : List Access := ⟨false,131082,1⟩::t14
def m16 : Mem := store (m14) 1048584 8 1
def t16 : List Access := ⟨true,1048584,1⟩::t15
def s272 : State := { fn := 2, pc := 96, locals := [1048576,1048572,15,12,1048584,131082,131070], stack := [12], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m16, trace := t16 }
def s280 : State := { fn := 2, pc := 65, locals := [1048576,1048572,15,8,1048580,131082,131070], stack := [1048580], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m16, trace := t16 }
def s288 : State := { fn := 2, pc := 73, locals := [1048576,1048572,15,8,1048580,131078,131070], stack := [131081,1048583], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m16, trace := t16 }
def t17 : List Access := ⟨false,131081,1⟩::t16
def m18 : Mem := store (m16) 1048583 7 1
def t18 : List Access := ⟨true,1048583,1⟩::t17
def s296 : State := { fn := 2, pc := 81, locals := [1048576,1048572,15,8,1048580,131078,131070], stack := [131080,1048582], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m18, trace := t18 }
def t19 : List Access := ⟨false,131080,1⟩::t18
def m20 : Mem := store (m18) 1048582 6 1
def t20 : List Access := ⟨true,1048582,1⟩::t19
def s304 : State := { fn := 2, pc := 89, locals := [1048576,1048572,15,8,1048580,131078,131070], stack := [131079,1048581], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m20, trace := t20 }
def t21 : List Access := ⟨false,131079,1⟩::t20
def m22 : Mem := store (m20) 1048581 5 1
def t22 : List Access := ⟨true,1048581,1⟩::t21
def t23 : List Access := ⟨false,131078,1⟩::t22
def m24 : Mem := store (m22) 1048580 4 1
def t24 : List Access := ⟨true,1048580,1⟩::t23
def s312 : State := { fn := 2, pc := 97, locals := [1048576,1048572,15,8,1048580,131078,131070], stack := [4294967292,8], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m24, trace := t24 }
def s320 : State := { fn := 2, pc := 66, locals := [1048576,1048572,15,4,1048576,131078,131070], stack := [3,1048576], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m24, trace := t24 }
def t25 : List Access := ⟨false,131077,1⟩::t24
def s328 : State := { fn := 2, pc := 74, locals := [1048576,1048572,15,4,1048576,131074,131070], stack := [3,1048579], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m24, trace := t25 }
def m26 : Mem := store (m24) 1048579 3 1
def t26 : List Access := ⟨true,1048579,1⟩::t25
def t27 : List Access := ⟨false,131076,1⟩::t26
def s336 : State := { fn := 2, pc := 82, locals := [1048576,1048572,15,4,1048576,131074,131070], stack := [2,1048578], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m26, trace := t27 }
def m28 : Mem := store (m26) 1048578 2 1
def t28 : List Access := ⟨true,1048578,1⟩::t27
def t29 : List Access := ⟨false,131075,1⟩::t28
def s344 : State := { fn := 2, pc := 90, locals := [1048576,1048572,15,4,1048576,131074,131070], stack := [1,1048577], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m28, trace := t29 }
def m30 : Mem := store (m28) 1048577 1 1
def t30 : List Access := ⟨true,1048577,1⟩::t29
def t31 : List Access := ⟨false,131074,1⟩::t30
def m32 : Mem := store (m30) 1048576 0 1
def t32 : List Access := ⟨true,1048576,1⟩::t31
def s352 : State := { fn := 2, pc := 98, locals := [1048576,1048572,15,4,1048576,131074,131070], stack := [0], labels := [⟨61,101,0,true⟩,⟨2,102,0,false⟩,⟨1,197,0,false⟩], calls := [⟨0,282,[131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0],[],[⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩]⟩], mem := m32, trace := t32 }
def s360 : State := { fn := 0, pc := 285, locals := [131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0], stack := [1048576,1048591], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := m32, trace := t32 }
def s361 : State := { fn := 0, pc := 286, locals := [131072,1048576,15,1048576,131074,1048591,1048559,131089,131073,1048586,1048584,131085,131081,1048579,131074,131073,240,1048591,0], stack := [15], labels := [⟨252,287,0,false⟩,⟨79,320,0,false⟩,⟨78,385,0,false⟩,⟨73,560,0,true⟩,⟨72,561,0,false⟩,⟨71,567,0,false⟩,⟨70,572,0,false⟩,⟨3,579,0,false⟩], calls := [], mem := m32, trace := t32 }
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
theorem a256 : advance Artifact.functions 8 s256 = some s264 := by rfl
theorem a264 : advance Artifact.functions 8 s264 = some s272 := by rfl
theorem a272 : advance Artifact.functions 8 s272 = some s280 := by rfl
theorem a280 : advance Artifact.functions 8 s280 = some s288 := by rfl
theorem a288 : advance Artifact.functions 8 s288 = some s296 := by rfl
theorem a296 : advance Artifact.functions 8 s296 = some s304 := by rfl
theorem a304 : advance Artifact.functions 8 s304 = some s312 := by rfl
theorem a312 : advance Artifact.functions 8 s312 = some s320 := by rfl
theorem a320 : advance Artifact.functions 8 s320 = some s328 := by rfl
theorem a328 : advance Artifact.functions 8 s328 = some s336 := by rfl
theorem a336 : advance Artifact.functions 8 s336 = some s344 := by rfl
theorem a344 : advance Artifact.functions 8 s344 = some s352 := by rfl
theorem a352 : advance Artifact.functions 8 s352 = some s360 := by rfl
theorem a360 : advance Artifact.functions 1 s360 = some s361 := by rfl
theorem execution : execute testcase = some (15,s361) := by
  change run Artifact.functions 1000 s0 = some (15,s361)
  have h361 : run Artifact.functions 639 s361 = some (15,s361) := by rfl
  have h360 : run Artifact.functions 640 s360 = some (15,s361) :=
    run_of_advance Artifact.functions 1 639 s360 s361 (15,s361) a360 h361
  have h352 : run Artifact.functions 648 s352 = some (15,s361) :=
    run_of_advance Artifact.functions 8 640 s352 s360 (15,s361) a352 h360
  have h344 : run Artifact.functions 656 s344 = some (15,s361) :=
    run_of_advance Artifact.functions 8 648 s344 s352 (15,s361) a344 h352
  have h336 : run Artifact.functions 664 s336 = some (15,s361) :=
    run_of_advance Artifact.functions 8 656 s336 s344 (15,s361) a336 h344
  have h328 : run Artifact.functions 672 s328 = some (15,s361) :=
    run_of_advance Artifact.functions 8 664 s328 s336 (15,s361) a328 h336
  have h320 : run Artifact.functions 680 s320 = some (15,s361) :=
    run_of_advance Artifact.functions 8 672 s320 s328 (15,s361) a320 h328
  have h312 : run Artifact.functions 688 s312 = some (15,s361) :=
    run_of_advance Artifact.functions 8 680 s312 s320 (15,s361) a312 h320
  have h304 : run Artifact.functions 696 s304 = some (15,s361) :=
    run_of_advance Artifact.functions 8 688 s304 s312 (15,s361) a304 h312
  have h296 : run Artifact.functions 704 s296 = some (15,s361) :=
    run_of_advance Artifact.functions 8 696 s296 s304 (15,s361) a296 h304
  have h288 : run Artifact.functions 712 s288 = some (15,s361) :=
    run_of_advance Artifact.functions 8 704 s288 s296 (15,s361) a288 h296
  have h280 : run Artifact.functions 720 s280 = some (15,s361) :=
    run_of_advance Artifact.functions 8 712 s280 s288 (15,s361) a280 h288
  have h272 : run Artifact.functions 728 s272 = some (15,s361) :=
    run_of_advance Artifact.functions 8 720 s272 s280 (15,s361) a272 h280
  have h264 : run Artifact.functions 736 s264 = some (15,s361) :=
    run_of_advance Artifact.functions 8 728 s264 s272 (15,s361) a264 h272
  have h256 : run Artifact.functions 744 s256 = some (15,s361) :=
    run_of_advance Artifact.functions 8 736 s256 s264 (15,s361) a256 h264
  have h248 : run Artifact.functions 752 s248 = some (15,s361) :=
    run_of_advance Artifact.functions 8 744 s248 s256 (15,s361) a248 h256
  have h240 : run Artifact.functions 760 s240 = some (15,s361) :=
    run_of_advance Artifact.functions 8 752 s240 s248 (15,s361) a240 h248
  have h232 : run Artifact.functions 768 s232 = some (15,s361) :=
    run_of_advance Artifact.functions 8 760 s232 s240 (15,s361) a232 h240
  have h224 : run Artifact.functions 776 s224 = some (15,s361) :=
    run_of_advance Artifact.functions 8 768 s224 s232 (15,s361) a224 h232
  have h216 : run Artifact.functions 784 s216 = some (15,s361) :=
    run_of_advance Artifact.functions 8 776 s216 s224 (15,s361) a216 h224
  have h208 : run Artifact.functions 792 s208 = some (15,s361) :=
    run_of_advance Artifact.functions 8 784 s208 s216 (15,s361) a208 h216
  have h200 : run Artifact.functions 800 s200 = some (15,s361) :=
    run_of_advance Artifact.functions 8 792 s200 s208 (15,s361) a200 h208
  have h192 : run Artifact.functions 808 s192 = some (15,s361) :=
    run_of_advance Artifact.functions 8 800 s192 s200 (15,s361) a192 h200
  have h184 : run Artifact.functions 816 s184 = some (15,s361) :=
    run_of_advance Artifact.functions 8 808 s184 s192 (15,s361) a184 h192
  have h176 : run Artifact.functions 824 s176 = some (15,s361) :=
    run_of_advance Artifact.functions 8 816 s176 s184 (15,s361) a176 h184
  have h168 : run Artifact.functions 832 s168 = some (15,s361) :=
    run_of_advance Artifact.functions 8 824 s168 s176 (15,s361) a168 h176
  have h160 : run Artifact.functions 840 s160 = some (15,s361) :=
    run_of_advance Artifact.functions 8 832 s160 s168 (15,s361) a160 h168
  have h152 : run Artifact.functions 848 s152 = some (15,s361) :=
    run_of_advance Artifact.functions 8 840 s152 s160 (15,s361) a152 h160
  have h144 : run Artifact.functions 856 s144 = some (15,s361) :=
    run_of_advance Artifact.functions 8 848 s144 s152 (15,s361) a144 h152
  have h136 : run Artifact.functions 864 s136 = some (15,s361) :=
    run_of_advance Artifact.functions 8 856 s136 s144 (15,s361) a136 h144
  have h128 : run Artifact.functions 872 s128 = some (15,s361) :=
    run_of_advance Artifact.functions 8 864 s128 s136 (15,s361) a128 h136
  have h120 : run Artifact.functions 880 s120 = some (15,s361) :=
    run_of_advance Artifact.functions 8 872 s120 s128 (15,s361) a120 h128
  have h112 : run Artifact.functions 888 s112 = some (15,s361) :=
    run_of_advance Artifact.functions 8 880 s112 s120 (15,s361) a112 h120
  have h104 : run Artifact.functions 896 s104 = some (15,s361) :=
    run_of_advance Artifact.functions 8 888 s104 s112 (15,s361) a104 h112
  have h96 : run Artifact.functions 904 s96 = some (15,s361) :=
    run_of_advance Artifact.functions 8 896 s96 s104 (15,s361) a96 h104
  have h88 : run Artifact.functions 912 s88 = some (15,s361) :=
    run_of_advance Artifact.functions 8 904 s88 s96 (15,s361) a88 h96
  have h80 : run Artifact.functions 920 s80 = some (15,s361) :=
    run_of_advance Artifact.functions 8 912 s80 s88 (15,s361) a80 h88
  have h72 : run Artifact.functions 928 s72 = some (15,s361) :=
    run_of_advance Artifact.functions 8 920 s72 s80 (15,s361) a72 h80
  have h64 : run Artifact.functions 936 s64 = some (15,s361) :=
    run_of_advance Artifact.functions 8 928 s64 s72 (15,s361) a64 h72
  have h56 : run Artifact.functions 944 s56 = some (15,s361) :=
    run_of_advance Artifact.functions 8 936 s56 s64 (15,s361) a56 h64
  have h48 : run Artifact.functions 952 s48 = some (15,s361) :=
    run_of_advance Artifact.functions 8 944 s48 s56 (15,s361) a48 h56
  have h40 : run Artifact.functions 960 s40 = some (15,s361) :=
    run_of_advance Artifact.functions 8 952 s40 s48 (15,s361) a40 h48
  have h32 : run Artifact.functions 968 s32 = some (15,s361) :=
    run_of_advance Artifact.functions 8 960 s32 s40 (15,s361) a32 h40
  have h24 : run Artifact.functions 976 s24 = some (15,s361) :=
    run_of_advance Artifact.functions 8 968 s24 s32 (15,s361) a24 h32
  have h16 : run Artifact.functions 984 s16 = some (15,s361) :=
    run_of_advance Artifact.functions 8 976 s16 s24 (15,s361) a16 h24
  have h8 : run Artifact.functions 992 s8 = some (15,s361) :=
    run_of_advance Artifact.functions 8 984 s8 s16 (15,s361) a8 h16
  have h0 : run Artifact.functions 1000 s0 = some (15,s361) :=
    run_of_advance Artifact.functions 8 992 s0 s8 (15,s361) a0 h8
  exact h0
theorem checked : checks testcase = true := by
  unfold checks
  rw [execution]
  rfl
end C7
end Certificates
