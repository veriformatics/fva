import Chunks
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
open Wasm
namespace Verification

theorem of_steps {k : Nat} {a b : Config} (h : steps code k a = some b) : Runs code a b := by
  induction k generalizing a with
  | zero => simp only [steps, Option.some.injEq] at h; subst a; exact .refl b
  | succ k ih =>
    simp only [steps] at h
    cases he : step code a with
    | none => simp [he] at h
    | some c =>
      rw [he] at h
      exact .next he (ih h)

theorem runs_trans {a b c : Config} (h : Runs code a b) (k : Runs code b c) :
    Runs code a c := by
  induction h with
  | refl => exact k
  | next hs _ ih => exact .next hs (ih k)

theorem prefix_nowrap (n lo hi oldMid oldFlag m : Nat) (he : (hi-lo)/2+lo = m)
    (hm : m < 2^32) (hs : m*m < 2^64) :
    Runs code (boundary n lo hi oldMid oldFlag)
      (.live 48 [lo,n,m,hi,m,if n < m*m then 1 else 0]
        [if n < m*m then 1 else 0,hi,m] [23]) := by
  apply of_steps (k := 15)
  rw [loop_prefix, he]
  simp only [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hs]

theorem upper_complete (n lo hi m : Nat) (hl : lo ≤ m) (hm : m < 2^32) :
    Runs code (.live 48 [lo,n,m,hi,m,1] [1,hi,m] [23])
      (.live (if 1 < m-lo then 23 else 68) [lo,n,m-lo,m,m,1] [] [23]) := by
  have ht := of_steps (upper_tail n lo hi m)
  rw [subtract_wrap hl hm] at ht
  exact runs_trans ht (of_steps (branch_tail n lo m (m-lo) m 1))

theorem lower_complete (n lo hi m : Nat) (hm : m ≤ hi) (hh : hi < 2^32) :
    Runs code (.live 48 [lo,n,m,hi,m,0] [0,hi,m] [23])
      (.live (if 1 < hi-m then 23 else 68) [m,n,hi-m,hi,m,0] [] [23]) := by
  have ht := of_steps (lower_tail n lo hi m)
  rw [subtract_wrap hm hh] at ht
  exact runs_trans ht (of_steps (branch_tail n m hi (hi-m) m 0))

theorem iteration (n lo hi oldMid oldFlag : Nat)
    (hlo : lo < hi) (hhi : hi ≤ 65536) (hw : 1 < hi-lo) :
    let m := (hi-lo)/2 + lo
    let l := if n < m*m then lo else m
    let h := if n < m*m then m else hi
    Runs code (boundary n lo hi oldMid oldFlag)
      (.live (if 1 < h-l then 23 else 68)
        [l,n,h-l,h,m,if n < m*m then 1 else 0] [] [23]) := by
  dsimp only
  generalize hm : (hi-lo)/2 + lo = m
  have hmlo : lo < m := by omega
  have hmhi : m < hi := by omega
  have hm32 : m < 2^32 := by omega
  have hsq : m*m < 2^64 := by
    have h := Nat.mul_self_le_mul_self (Nat.le_of_lt (Nat.lt_of_lt_of_le hmhi hhi))
    omega
  have hp := prefix_nowrap n lo hi oldMid oldFlag m hm hm32 hsq
  by_cases hc : n < m*m
  · simp only [hc, ite_true] at hp ⊢
    exact runs_trans hp (upper_complete n lo hi m (Nat.le_of_lt hmlo) hm32)
  · simp only [hc, ite_false] at hp ⊢
    exact runs_trans hp (lower_complete n lo hi m (Nat.le_of_lt hmhi) (by omega))

end Verification
