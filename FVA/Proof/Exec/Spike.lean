import FVA.Proof.Exec.Det

/-!
# Proof-route spike: a loop proven for every input

`sum n` = 1 + … + n by a `block`/`loop`/`br_if` loop over locals, proven to return
`n(n+1)/2 mod 2^32` for every `n` with `Must` (total correctness), by symbolic stepping with the
reference stepper + `must_of_step` and an induction over the loop's iterations.
-/

namespace FVA.Wasm.Exec.Ref.Spike

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

/-- Body: local 0 = n (parameter), local 1 = accumulator. -/
def sumBody : List Instr :=
  [.block .empty [.loop .empty [
      .localGet 0, .itestEqz .w32, .brIf 1,
      .localGet 1, .localGet 0, .ibinop .w32 .add, .localSet 1,
      .localGet 0, .iconst .w32 1, .ibinop .w32 .sub, .localSet 0,
      .br 0]],
   .localGet 1]

/-- The function: `(param i32) (result i32) (local i32)`. -/
def sumFunc : Func := { type := 0, locals := [(1, .num .i32)], body := sumBody }

/-- A store holding the function at address 0. -/
def store0 : Store := { funcs := [.wasm ⟨[.num .i32], [.num .i32]⟩ {} sumFunc] }

private theorem nvFrame (n f es) : toVal (.frame n f es) = none := rfl
private theorem nvLabel (n cont es) : toVal (.label n cont es) = none := rfl
private theorem nvInvoke (a) : toVal (.invoke a) = none := rfl
private theorem nvBlock (bt body) : toVal (.plain (.block bt body)) = none := rfl
private theorem nvLoop (bt body) : toVal (.plain (.loop bt body)) = none := rfl
private theorem nvGet (x) : toVal (.plain (.localGet x)) = none := rfl
private theorem nvSet (x) : toVal (.plain (.localSet x)) = none := rfl
private theorem nvBinary (w op) : toVal (.plain (.ibinop w op)) = none := rfl
private theorem nvTest (w) : toVal (.plain (.itestEqz w)) = none := rfl
private theorem nvBranch (l) : toVal (.plain (.br l)) = none := rfl
private theorem nvBranchIf (l) : toVal (.plain (.brIf l)) = none := rfl

private theorem lookup_func :
    store0.funcs[0]? = some (.wasm ⟨[.num .i32], [.num .i32]⟩ {} sumFunc) := rfl

private theorem toVal_one :
    toVal (.plain (.iconst .w32 1)) = some (.i32 1) := rfl

private theorem trap_val (v : Val) : isTrapOnly [v.instr] = false := isTrapOnly_vals [v]

attribute [local simp] nvFrame nvLabel nvInvoke nvBlock nvLoop nvGet nvSet nvBinary
  nvTest nvBranch nvBranchIf toVal_one toVal_instr trap_val

/-- Execute exactly this many no-choice steps, without exposing states in the proof script. -/
private def walk : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => bif uniqueStep c then
      match step c with
      | some d => walk k d
      | none => none
    else none

private theorem must_of_walk {H : HostSem} {Q : Outcome → Prop} {k : Nat} {c c' : Config}
    (h : walk k c = some c') (hc : Must H Q c') : Must H Q c := by
  induction k generalizing c with
  | zero => cases h; exact hc
  | succ k ih =>
    cases hu : uniqueStep c with
    | false => simp only [walk, hu, Bool.cond_false, reduceCtorEq] at h
    | true =>
      simp only [walk, hu, Bool.cond_true] at h
      cases hd : step c with
      | none => simp only [hd, reduceCtorEq] at h
      | some d =>
        simp only [hd] at h
        exact must_of_step hd hu (ih h)

/-- The loop instruction is extracted from the fixed function, not copied. -/
private def loopInstr : Instr :=
  match sumBody with
  | .block _ (i :: _) :: _ => i
  | _ => .nop

/-- Configuration immediately before entering or re-entering the loop. -/
private def loopEntry (n acc : BitVec 32) : Config :=
  ⟨store0, ⟨[], {}⟩, [.frame 1 ⟨[.i32 n, .i32 acc], {}⟩
    [.label 1 [] (.label 0 [] [.plain loopInstr] :: (sumBody.drop 1).map .plain)]]⟩

/-- The caller configuration after the function returns. -/
private def returned (acc : BitVec 32) : Config :=
  ⟨store0, ⟨[], {}⟩, [(Val.i32 acc).instr]⟩

private theorem start_walk (n : BitVec 32) :
    walk 2 (invokeConfig store0 0 [.i32 n]) = some (loopEntry n 0) := by
  simp [walk, loopEntry, loopInstr, lookup_func, sumFunc, sumBody, invokeConfig,
    uniqueStep, seqUnique, atUnique, instrUnique, step, seq, atInstr, instrStep,
    BlockType.expand, Func.localDefaults, ValType.default]

private theorem zero_walk (acc : BitVec 32) :
    walk 8 (loopEntry 0 acc) = some (returned acc) := by
  simp [walk, loopEntry, loopInstr, returned, sumBody,
    uniqueStep, seqUnique, atUnique, instrUnique, step, seq, atInstr, instrStep,
    BlockType.expand, numStep, numOut, ieqz, FVA.Wasm.Num.bool]

private theorem sub_one (k : Nat) (hk : k + 1 < 2 ^ 32) :
    isub (BitVec.ofNat 32 (k + 1)) 1 = BitVec.ofNat 32 k := by
  -- Symbolic cancellation keeps wide residues out of arithmetic normalization.
  change BitVec.ofNat 32 ((k + 1) % 2 ^ 32 + 2 ^ 32 - 1) = BitVec.ofNat 32 k
  rw [Nat.mod_eq_of_lt hk]
  have he : k + 1 + 2 ^ 32 - 1 = k + 2 ^ 32 := by omega
  rw [he]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

private theorem numeric_add (a b : BitVec 32) :
    numStep (.ibinop .w32 .add) [.i32 a, .i32 b] = some (some (.i32 (a + b))) := rfl

private theorem succ_walk (k : Nat) (hk : k + 1 < 2 ^ 32) (acc : BitVec 32) :
    walk 12 (loopEntry (BitVec.ofNat 32 (k + 1)) acc) =
      some (loopEntry (BitVec.ofNat 32 k) (acc + BitVec.ofNat 32 (k + 1))) := by
  have hz : numStep (.itestEqz .w32) [.i32 (BitVec.ofNat 32 (k + 1))] =
      some (some (.i32 (BitVec.ofNat 32 0))) := by
    change some (some (Val.i32 (ieqz (BitVec.ofNat 32 (k + 1))))) = _
    unfold ieqz FVA.Wasm.Num.bool
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    simp
  -- Match the simplifier's literal form, rather than an overloaded numeral.
  have hs : numStep (.ibinop .w32 .sub)
      [.i32 (BitVec.ofNat 32 (k + 1)), .i32 (BitVec.ofNat 32 1)] =
      some (some (.i32 (BitVec.ofNat 32 k))) := by
    change some (some (Val.i32 (isub (BitVec.ofNat 32 (k + 1)) 1))) = _
    rw [sub_one k hk]
  simp [walk, loopEntry, loopInstr, sumBody,
    uniqueStep, seqUnique, atUnique, instrUnique, step, seq, atInstr, instrStep,
    BlockType.expand, numOut, hz, hs, numeric_add]

private theorem tri_succ (k : Nat) :
    (k + 1) * (k + 2) / 2 = k + 1 + k * (k + 1) / 2 := by
  have he : (k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1) := by ring
  rw [he, Nat.add_mul_div_left _ _ (by decide)]
  omega

private theorem return_must (H : HostSem) (acc : BitVec 32) :
    Must H (fun o => o = .returned store0 [.i32 acc]) (returned acc) :=
  Must.done (o := .returned store0 [.i32 acc]) ⟨rfl, rfl⟩ rfl

private theorem loop_must (H : HostSem) (k : Nat) (acc : BitVec 32) (hk : k < 2 ^ 32) :
    Must H (fun o => o = .returned store0 [.i32 (acc + BitVec.ofNat 32 (k * (k + 1) / 2))])
      (loopEntry (BitVec.ofNat 32 k) acc) := by
  induction k generalizing acc with
  | zero => simpa using must_of_walk (zero_walk acc) (return_must H acc)
  | succ k ih =>
    have hm := ih (acc + BitVec.ofNat 32 (k + 1)) (by omega)
    have he : (acc + BitVec.ofNat 32 (k + 1)) + BitVec.ofNat 32 (k * (k + 1) / 2) =
        acc + BitVec.ofNat 32 ((k + 1) * (k + 2) / 2) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← tri_succ]
    rw [he] at hm
    exact must_of_walk (succ_walk k hk acc) hm

theorem sum_must (H : HostSem) (n : BitVec 32) :
    Must H (fun o => o = .returned store0 [.i32 (BitVec.ofNat 32 (n.toNat * (n.toNat + 1) / 2))])
      (invokeConfig store0 0 [.i32 n]) := by
  apply must_of_walk (start_walk n)
  simpa using loop_must H n.toNat 0 n.isLt

end FVA.Wasm.Exec.Ref.Spike
