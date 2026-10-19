import Toy.Lifted
import Toy.Def
import FVA

/-! Proofs for `Toy.Spec` — AI-written, never reviewed; the Lean kernel checks them. -/

namespace Toy.Proof
open FVA.Wasm

theorem clamp_ok (x lo hi : BitVec 32) : ∃ fuel, invoke Lifted.clamp fuel [.i32 x, .i32 lo, .i32 hi] =
    some [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)] := by
  refine ⟨20, ?_⟩
  wasm_sim [Lifted.clamp]
  simp only [BitVec.slt_iff_toInt_lt]
  have := @BitVec.toInt_inj 32 x hi
  by_cases h1 : x.toInt < lo.toInt <;> by_cases h2 : x.toInt < hi.toInt <;>
    by_cases h3 : hi.toInt < x.toInt <;>
    simp only [h1, h2, h3, ite_true, ite_false, not_true_eq_false] <;>
    first | rfl | omega | (rw [this.mp (by omega)])

theorem sumBelow_succ (m : Nat) : sumBelow (m + 1) = m + m * (m - 1) / 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumBelow, ih]
    have e : (m + 1) * (m + 1 - 1) = m * (m - 1) + 2 * m := by cases m <;> grind
    rw [e, Nat.add_mul_div_left _ _ (by decide)]
    omega

theorem sumBelow_eq (k : Nat) (hk : 1 ≤ k) : sumBelow k = (k - 1) + (k - 1) * (k - 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using sumBelow_succ m

theorem sum_to_ok (n : BitVec 32) : ∃ fuel, invoke Lifted.sum_to fuel [.i32 n] = some [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))] := by
  refine ⟨40, ?_⟩
  by_cases h : n = 0
  · subst h; wasm_sim [Lifted.sum_to]; rfl
  · wasm_sim [Lifted.sum_to, h]
    simp only [Option.some.injEq, List.cons.injEq, Val.i32.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    have hk : 1 ≤ n.toNat := by
      have : n.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      omega
    have hlt := n.isLt
    simp only [wasm_arith, Nat.reducePow, Nat.reduceMod, Nat.pow_one]
    generalize n.toNat = k at *
    rw [sumBelow_eq k hk]
    have h1 : (k + 4294967295) % 4294967296 = k - 1 := by omega
    rw [h1]
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; decide
    · have h3 : (k + 4294967294) % 4294967296 = k - 2 := by omega
      have hm : (k - 1) * (k - 2) < 18446744073709551616 :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ (by omega : k - 1 < 4294967296)) (Nat.le_of_lt_succ (by omega : k - 2 < 4294967296))) (by decide)
      rw [h3, Nat.mod_eq_of_lt (by omega : k - 1 < 18446744073709551616),
        Nat.mod_eq_of_lt (by omega : k - 2 < 18446744073709551616), Nat.mod_eq_of_lt hm]
      omega

def gcdLoop : Instr := .loop 0 [.localGet 0, .localGet 1, .localTee 2, .i32Bin .remU, .localSet 1,
  .localGet 2, .localSet 0, .localGet 1, .brIf 0]

theorem gcd_comm_rec (a b : Nat) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]

theorem gcd_loop : ∀ n (F : Nat) (a b t : BitVec 32), b.toNat = n → b ≠ 0 → 3 * n + 20 ≤ F →
    ∃ ls, exec F [gcdLoop, .localGet 2] ⟨[], [.i32 a, .i32 b, .i32 t]⟩ =
      .done ⟨[.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))], ls⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro F a b t hn hb hF
  obtain ⟨g, rfl⟩ : ∃ g, F = g + 20 := ⟨F - 20, by omega⟩
  rw [gcdLoop, show g + 20 = (g + 19) + 1 from rfl, exec_loop]
  wasm_step [hb]
  have hm : (a % b).toNat = a.toNat % b.toNat := Arith.toNat_umod a b
  have hbpos : 0 < b.toNat := by
    have : b.toNat ≠ 0 := fun e => hb (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  by_cases hr : a % b = 0
  · refine ⟨[.i32 b, .i32 (a % b), .i32 b], ?_⟩
    simp only [hr, not_true_eq_false, ite_false, wasm_exec]
    congr
    apply BitVec.eq_of_toNat_eq
    rw [Arith.toNat_ofNat, gcd_comm_rec, ← hm, hr]
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.gcd_zero_right]
    exact (Nat.mod_eq_of_lt b.isLt).symm
  · simp only [hr, not_false_eq_true, ite_true]
    have hlt : (a % b).toNat < n := by rw [hm, ← hn]; exact Nat.mod_lt _ hbpos
    obtain ⟨ls, h⟩ := ih _ hlt (g + 19) b (a % b) b rfl hr (by omega)
    refine ⟨ls, ?_⟩
    rw [← gcdLoop, h, hm, ← gcd_comm_rec]

theorem gcd_ok (a b : BitVec 32) : ∃ fuel, invoke Lifted.gcd fuel [.i32 a, .i32 b] =
    some [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))] := by
  by_cases hb : b = 0
  · refine ⟨10, ?_⟩
    subst hb
    wasm_sim [Lifted.gcd]
    congr
    apply BitVec.eq_of_toNat_eq
    rw [Arith.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl, Nat.gcd_zero_right]
    exact (Nat.mod_eq_of_lt a.isLt).symm
  · obtain ⟨ls, h⟩ := gcd_loop _ (3 * b.toNat + 21) a b 0 rfl hb (by omega)
    refine ⟨3 * b.toNat + 22, ?_⟩
    wasm_step [Lifted.gcd, hb]
    rw [← gcdLoop, h]
    rfl

theorem clamp_spec (x lo hi : BitVec 32) :
    Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
      [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)] :=
  returns_of_invoke rfl (clamp_ok x lo hi)

theorem gcd_spec (a b : BitVec 32) :
    Returns Lifted.module "gcd" [.i32 a, .i32 b] [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))] :=
  returns_of_invoke rfl (gcd_ok a b)

theorem sum_to_spec (n : BitVec 32) :
    Returns Lifted.module "sum_to" [.i32 n] [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))] :=
  returns_of_invoke rfl (sum_to_ok n)

end Toy.Proof
