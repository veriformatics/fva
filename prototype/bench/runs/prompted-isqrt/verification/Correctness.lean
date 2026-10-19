import Trace
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
open Wasm
namespace Verification

theorem exit_loop (n lo hi m flag : Nat) :
    Runs code (.live 68 [lo,n,hi-lo,hi,m,flag] [] [23]) (.done lo) := by
  apply of_steps (k := 3)
  rfl

theorem interval_sqrt {n lo hi : Nat} (hlt : lo < hi)
    (hw : ¬ 1 < hi-lo) (hl : lo*lo ≤ n) (hh : n < hi*hi) :
    IsSqrt n lo := by
  constructor
  · exact hl
  · intro s hs
    have he : hi = lo+1 := by omega
    have hbound : s < hi := by
      by_cases h : s < hi
      · exact h
      have hmul := Nat.mul_self_le_mul_self (show hi ≤ s by omega)
      omega
    omega

theorem loop_terminates (width : Nat) :
    ∀ n lo hi oldMid oldFlag : Nat,
    hi-lo = width → lo < hi → hi ≤ 65536 → 1 < width →
    lo*lo ≤ n → n < hi*hi →
    ∃ r, Runs code (boundary n lo hi oldMid oldFlag) (.done r) ∧
      IsSqrt n r := by
  induction width using Nat.strongRecOn with
  | ind width ih =>
    intro n lo hi oldMid oldFlag he hlo hhi hw hlow hhigh
    let m := (hi-lo)/2 + lo
    let l := if n < m*m then lo else m
    let h := if n < m*m then m else hi
    let flag := if n < m*m then 1 else 0
    have hmlo : lo < m := by dsimp [m]; omega
    have hmhi : m < hi := by dsimp [m]; omega
    have hb : l < h ∧ h ≤ 65536 ∧ l*l ≤ n ∧ n < h*h ∧ h-l < width := by
      by_cases hc : n < m*m
      · simp only [l, h, ite_eq_left hc]
        exact ⟨hmlo, by omega, hlow, hc, by omega⟩
      · simp only [l, h, ite_eq_right hc]
        exact ⟨hmhi, hhi, by omega, hhigh, by omega⟩
    have hit := iteration n lo hi oldMid oldFlag hlo hhi (by omega)
    change Runs code (boundary n lo hi oldMid oldFlag)
      (.live (if 1 < h-l then 23 else 68) [l,n,h-l,h,m,flag] [] [23]) at hit
    by_cases hd : 1 < h-l
    · have hit' : Runs code (boundary n lo hi oldMid oldFlag)
          (boundary n l h m flag) := by simpa [hd, boundary] using hit
      obtain ⟨r,hr,hs⟩ := ih (h-l) hb.2.2.2.2 n l h m flag rfl
        hb.1 hb.2.1 hd hb.2.2.1 hb.2.2.2.1
      exact ⟨r, runs_trans hit' hr, hs⟩
    · have hit' : Runs code (boundary n lo hi oldMid oldFlag)
          (.live 68 [l,n,h-l,h,m,flag] [] [23]) := by simpa [hd] using hit
      exact ⟨l, runs_trans hit' (exit_loop n l h m flag),
        interval_sqrt hb.1 hd hb.2.2.1 hb.2.2.2.1⟩

theorem invocation_exists (n : Nat) (hn : n < 2^32) :
    ∃ r, invoke Artifact.bytes n r ∧ IsSqrt n r := by
  obtain ⟨r,hr,hs⟩ := loop_terminates 65536 n 0 65536 0 0 rfl
    (by decide) (by decide) (by decide) (by omega) (by simpa using hn)
  have hh : Artifact.bytes.take 58 = envelope ∧ Artifact.bytes.length = 130 := by decide
  refine ⟨r, ?_, hs⟩
  exact ⟨hh.1, hh.2, hn, runs_trans (of_steps (initialize_state n hn)) hr⟩

theorem done_preserved {r : Nat} {c : Config} (h : Runs code (.done r) c) : c = .done r := by
  have go : ∀ {a b : Config}, Runs code a b → ∀ (r : Nat), a = .done r → b = .done r := by
    intro a b h
    induction h with
    | refl a => intro r he; exact he
    | @next a b c hs ht ih =>
      intro r he
      have hb : Config.done r = b := by
        simpa only [he, step.eq_def, Option.some.injEq] using hs
      exact ih r hb.symm
  exact go h r rfl

theorem results_unique {c : Config} {r s : Nat}
    (hr : Runs code c (.done r)) (hs : Runs code c (.done s)) : r = s := by
  have go : ∀ {a b : Config}, Runs code a b → ∀ {r : Nat}, b = .done r →
      ∀ {s : Nat}, Runs code a (.done s) → r = s := by
    intro a b h
    induction h with
    | refl a =>
      intro r he s hs
      rw [he] at hs
      exact (Config.done.inj (done_preserved hs)).symm
    | @next a b c hab hbc ih =>
      intro r he s hs
      cases hs with
      | refl =>
        have hb : Config.done s = b := by
          simpa only [step.eq_def, Option.some.injEq] using hab
        rw [← hb] at hbc
        exact Config.done.inj (he.symm.trans (done_preserved hbc))
      | next hax hxs =>
        have hx := Option.some.inj (hab.symm.trans hax)
        cases hx
        exact ih he hxs
  exact go hr rfl hs

end Verification
