import Machine
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
open Wasm
namespace Verification

theorem subtract_wrap {a b : Nat} (h : b ≤ a) (ha : a < 2^32) :
    (a+2^32-b) % 2^32 = a-b := by
  have he : a+2^32-b = (a-b)+2^32 := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem mid_prefix (n lo hi oldMid oldFlag : Nat) :
    let m := ((hi-lo)/2 + lo) % 2^32
    steps code 8 (boundary n lo hi oldMid oldFlag) =
      some (.live 37 [lo,n,m,hi,oldMid,oldFlag] [m,hi,m] [23]) := by
  rfl


theorem square_prefix (n lo hi m oldMid oldFlag : Nat) :
    let e := m % 2^32
    let flag := if n < (e*e) % 2^64 then 1 else 0
    steps code 7 (.live 37 [lo,n,m,hi,oldMid,oldFlag] [m,hi,m] [23]) =
      some (.live 48 [lo,n,m,hi,e,flag] [flag,hi,m] [23]) := by
  rfl


theorem loop_prefix (n lo hi oldMid oldFlag : Nat) :
    let m := ((hi-lo)/2 + lo) % 2^32
    let e := m % 2^32
    let flag := if n < (e*e) % 2^64 then 1 else 0
    steps code 15 (boundary n lo hi oldMid oldFlag) =
      some (.live 48 [lo,n,m,hi,e,flag] [flag,hi,m] [23]) := by
  rw [show 15 = 8+7 from rfl, steps_add, mid_prefix]
  exact square_prefix n lo hi _ oldMid oldFlag


theorem upper_tail (n lo hi m : Nat) :
    let w := (m+2^32-lo) % 2^32
    steps code 9 (.live 48 [lo,n,m,hi,m,1] [1,hi,m] [23]) =
      some (.live 63 [lo,n,w,m,m,1] [w] [23]) := by rfl

theorem lower_tail (n lo hi m : Nat) :
    let w := (hi+2^32-m) % 2^32
    steps code 9 (.live 48 [lo,n,m,hi,m,0] [0,hi,m] [23]) =
      some (.live 63 [m,n,w,hi,m,0] [w] [23]) := by rfl

theorem branch_tail (n lo hi w m flag : Nat) :
    steps code 3 (.live 63 [lo,n,w,hi,m,flag] [w] [23]) =
      some (.live (if 1 < w then 23 else 68) [lo,n,w,hi,m,flag] [] [23]) := by
  by_cases h : 1 < w <;>
    simp [steps, at_63, at_65, at_66, h]

end Verification
