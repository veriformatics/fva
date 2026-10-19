import Isqrt.Spec
import FVA

namespace Isqrt.Proof
open FVA.Wasm

/-! Proofs use Lean's standard library and FVA only. The interval argument is
connected to the lifted instruction list by `loop_unfold`, not assumed as a model
of the C program. -/

abbrev b32 (n : Nat) : BitVec 32 := BitVec.ofNat 32 n
abbrev b64 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

def loopCode : Instr := .loop 0 [
  .localGet 2, .i32Const 1, .i32Bin .shrU, .localGet 0, .i32Bin .add,
  .localTee 2, .localGet 3, .localGet 2, .i64ExtendI32U, .localTee 4,
  .localGet 4, .i64Bin .mul, .localGet 1, .i64Rel .gtU, .localTee 5,
  .select, .localTee 3, .localGet 0, .localGet 2, .localGet 5, .select,
  .localTee 0, .i32Bin .sub, .localTee 2, .i32Const 1, .i32Rel .gtU,
  .brIf 0]

def Inv (n lo hi : Nat) : Prop :=
  lo < hi ∧ hi ≤ 65536 ∧ lo * lo ≤ n ∧ n < hi * hi

theorem midpoint_bounds {lo hi : Nat} (h : lo + 1 < hi) :
    lo < lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 < hi := by omega

theorem inv_step {n lo hi : Nat} (h : Inv n lo hi) (hg : lo + 1 < hi) :
    let m := lo + (hi - lo) / 2
    let lo' := if n < m * m then lo else m
    let hi' := if n < m * m then m else hi
    Inv n lo' hi' ∧ hi' - lo' < hi - lo := by
  have hb := midpoint_bounds hg
  dsimp
  rcases h with ⟨hlt, hhi, hlo, hn⟩
  by_cases hc : n < (lo + (hi - lo) / 2) * (lo + (hi - lo) / 2)
  · simp only [hc, ite_true]
    exact ⟨⟨hb.1, by omega, hlo, hc⟩, by omega⟩
  · simp only [hc, ite_false]
    exact ⟨⟨hb.2, hhi, by omega, hn⟩, by omega⟩

theorem inv_exit {n lo hi : Nat} (h : Inv n lo hi) (hg : hi - lo ≤ 1) :
    lo * lo ≤ n ∧ ∀ s : Nat, s * s ≤ n → s ≤ lo := by
  rcases h with ⟨hlt, hhi, hlo, hn⟩
  refine ⟨hlo, ?_⟩
  intro s hs
  by_cases hc : s ≤ lo
  · exact hc
  have hle : hi ≤ s := by omega
  have hm := Nat.mul_le_mul hle hle
  omega

theorem nat32 {x : Nat} (h : x < 4294967296) : (b32 x).toNat = x := by
  rw [Arith.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem nat64 {x : Nat} (h : x < 18446744073709551616) : (b64 x).toNat = x := by
  rw [Arith.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mid_machine {lo hi : Nat} (hl : lo < hi) (hh : hi ≤ 65536) :
    (b32 (hi - lo) >>> 1) + b32 lo = b32 (lo + (hi - lo) / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hlo : lo < 4294967296 := by omega
  have hd : hi - lo < 4294967296 := by omega
  simp only [Arith.toNat_add, Arith.toNat_ushiftRight, nat32 hlo, nat32 hd,
    Arith.toNat_ofNat, Nat.reducePow]
  rw [Nat.add_comm]

theorem sub_machine {lo hi : Nat} (hl : lo ≤ hi) (hh : hi ≤ 65536) :
    b32 hi - b32 lo = b32 (hi - lo) := by
  apply BitVec.eq_of_toNat_eq
  have hlo : lo < 4294967296 := by omega
  have hhi : hi < 4294967296 := by omega
  simp only [Arith.toNat_sub, nat32 hlo, nat32 hhi, Arith.toNat_ofNat, Nat.reducePow]
  omega

theorem extend_machine {m : Nat} (h : m < 4294967296) :
    (b32 m).setWidth 64 = b64 m := by
  apply BitVec.eq_of_toNat_eq
  rw [Arith.toNat_setWidth, nat32 h, Arith.toNat_ofNat]

theorem square_machine {m : Nat} (h : m ≤ 65536) :
    b64 m * b64 m = b64 (m * m) := by
  apply BitVec.eq_of_toNat_eq
  have hm : m < 18446744073709551616 := by omega
  simp only [Arith.toNat_mul, nat64 hm, Arith.toNat_ofNat]

theorem square_test {n m : Nat} (hn : n < 4294967296) (hm : m ≤ 65536) :
    ((b64 n).ult (b64 (m * m))) = decide (n < m * m) := by
  have hs : m * m < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hm hm) (by decide)
  simp only [BitVec.ult, nat64 (by omega : n < 18446744073709551616), nat64 hs]

theorem gap_test {d : Nat} (hd : d ≤ 65536) :
    ((1 : BitVec 32).ult (b32 d)) = decide (1 < d) := by
  simp only [BitVec.ult, nat32 (by omega : d < 4294967296)]
  rfl

/-- The compiler keeps the input in local 1, `lo` in 0, `hi - lo` in 2, and `hi`
in 3. Locals 4 and 5 are scratch values, overwritten before they are read. -/
abbrev locals (n lo hi : Nat) (scratch : BitVec 64) (flag : BitVec 32) : List Val :=
  [.i32 (b32 lo), .i64 (b64 n), .i32 (b32 (hi - lo)), .i32 (b32 hi),
   .i64 scratch, .i32 flag]

theorem loop_unfold (F n lo hi : Nat) (scratch : BitVec 64) (flag : BitVec 32)
    (hn : n < 4294967296) (hl : lo + 1 < hi) (hh : hi ≤ 65536) :
    let m := lo + (hi - lo) / 2
    let c := n < m * m
    let lo' := if c then lo else m
    let hi' := if c then m else hi
    let ls := locals n lo' hi' (b64 m) (if c then 1 else 0)
    exec (F + 40) [loopCode, .localGet 0] ⟨[], locals n lo hi scratch flag⟩ =
      if 1 < hi' - lo' then
        exec (F + 39) [loopCode, .localGet 0] ⟨[], ls⟩
      else .done ⟨[.i32 (b32 lo')], ls⟩ := by
  dsimp only
  rw [loopCode, exec_loop]
  wasm_step
  have hb := midpoint_bounds hl
  have hm : lo + (hi - lo) / 2 ≤ 65536 := by omega
  simp only [show (1 : BitVec 32).toNat % 32 = 1 from rfl,
    mid_machine (lo := lo) (hi := hi) (by omega) hh,
    extend_machine (m := lo + (hi - lo) / 2) (by omega), square_machine hm,
    square_test hn hm]
  by_cases hc : n < (lo + (hi - lo) / 2) * (lo + (hi - lo) / 2)
  · wasm_step [hc, show (1 : BitVec 32) ≠ 0 by decide]
    rw [sub_machine (lo := lo) (by omega) hm]
    wasm_step [gap_test (d := (lo + (hi - lo) / 2) - lo) (by omega),
      decide_eq_true_eq]
    by_cases hg : 1 < (lo + (hi - lo) / 2) - lo <;>
      wasm_step [hg, locals, show (1 : BitVec 32) ≠ 0 by decide]
  · wasm_step [hc]
    rw [sub_machine (lo := lo + (hi - lo) / 2) (by omega) hh]
    wasm_step [gap_test (d := hi - (lo + (hi - lo) / 2)) (by omega),
      decide_eq_true_eq]
    by_cases hg : 1 < hi - (lo + (hi - lo) / 2) <;>
      wasm_step [hg, locals, show (1 : BitVec 32) ≠ 0 by decide]

/-- A decreasing interval width gives a finite execution, not just partial correctness. -/
theorem loop_correct : ∀ d (F n lo hi : Nat) (scratch : BitVec 64) (flag : BitVec 32),
    hi - lo = d → Inv n lo hi → lo + 1 < hi → n < 4294967296 → d + 40 ≤ F →
    ∃ r ls, exec F [loopCode, .localGet 0] ⟨[], locals n lo hi scratch flag⟩ =
      .done ⟨[.i32 (b32 r)], ls⟩ ∧
      r < 65536 ∧ r * r ≤ n ∧ ∀ s : Nat, s * s ≤ n → s ≤ r := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro F n lo hi scratch flag hd hinv hgap hn hF
    obtain ⟨k, rfl⟩ : ∃ k, F = k + 40 := ⟨F - 40, by omega⟩
    let m := lo + (hi - lo) / 2
    let c := n < m * m
    let lo' := if c then lo else m
    let hi' := if c then m else hi
    let ls' := locals n lo' hi' (b64 m) (if c then 1 else 0)
    have hstep : Inv n lo' hi' ∧ hi' - lo' < d := by
      have h := inv_step hinv hgap
      have hs : hi' - lo' < hi - lo := h.2
      exact ⟨h.1, by omega⟩
    have hu := loop_unfold k n lo hi scratch flag hn hgap hinv.2.1
    change exec (k + 40) [loopCode, .localGet 0] ⟨[], locals n lo hi scratch flag⟩ =
      (if 1 < hi' - lo' then exec (k + 39) [loopCode, .localGet 0] ⟨[], ls'⟩
       else .done ⟨[.i32 (b32 lo')], ls'⟩) at hu
    rw [hu]
    by_cases hg : 1 < hi' - lo'
    · rw [ite_eq_left hg]
      exact ih (hi' - lo') hstep.2 (k + 39) n lo' hi' (b64 m)
        (if c then 1 else 0) rfl hstep.1 (by omega) hn (by omega)
    · rw [ite_eq_right hg]
      have he := inv_exit hstep.1 (by omega)
      have hr : lo' < 65536 := by
        have := hstep.1.1
        have := hstep.1.2.1
        omega
      exact ⟨lo', ls', rfl, hr, he⟩

theorem isqrt_correct (n : BitVec 32) :
    ∃ r : BitVec 32, invoke Lifted.isqrt 65585 [.i32 n] = some [.i32 r] ∧
      r.toNat * r.toNat ≤ n.toNat ∧
      ∀ s : Nat, s * s ≤ n.toNat → s ≤ r.toNat := by
  have hn : n.toNat < 4294967296 := n.isLt
  have hi : Inv n.toNat 0 65536 := ⟨by decide, by decide, by simp, by omega⟩
  obtain ⟨r, ls, he, hr, hlo, hmax⟩ :=
    loop_correct 65536 65576 n.toNat 0 65536 0 0 rfl hi (by decide) hn (by decide)
  refine ⟨b32 r, ?_, ?_, ?_⟩
  · have hw : n.setWidth 64 = b64 n.toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [Arith.toNat_setWidth, Arith.toNat_ofNat]
    wasm_step [Lifted.isqrt, hw]
    change (match exec 65576 [loopCode, .localGet 0]
        ⟨[], locals n.toNat 0 65536 0 0⟩ with
      | .done s | .ret s | .branch 0 s => some (s.stack.take 1).reverse
      | _ => none) = some [.i32 (b32 r)]
    rw [he]
    rfl
  · simpa only [nat32 (by omega : r < 4294967296)] using hlo
  · simpa only [nat32 (by omega : r < 4294967296)] using hmax

theorem correctness_holds : correctness := by
  intro n
  obtain ⟨r, he, hlo, hmax⟩ := isqrt_correct n
  exact ⟨r, returns_of_invoke rfl ⟨65585, he⟩, hlo, hmax⟩

theorem termination_holds : termination := by
  intro n
  obtain ⟨r, he, _⟩ := isqrt_correct n
  exact ⟨r, returns_of_invoke rfl ⟨65585, he⟩⟩

end Isqrt.Proof
