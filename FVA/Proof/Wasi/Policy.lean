import FVA.Proof.Wasi.WfRun
import FVA.Proof.Wasi.World

/-!
# T3a: `E`'s values are W's explicit choices (U29a)

`run` reads each choice field as `ch.X.getD v`, `v` = `E`'s value. `ofE σ r b` materializes those
values (`none` where `E`'s call fails before the field matters: an empty stdin request, a transfer
at the size limit, no descriptor or serial number left). `run` at `ofE` = `run` at `E`'s choice
(`run_ofE`), and on a well-formed state `ofE` is admissible field by field (`ofE_ok`): `E` picks
inside the WITX envelope, so W's `none` branch adds no behavior beyond its explicit choices.
Requests decoded from memory carry u32 iovec lengths (`decode_iovs_u32`), `ofE_ok`'s premise.
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec

/-- `E`'s value of each field `run` reads for request `r`; random bytes `b`. -/
def ofE (σ : State) (r : Req) (b : Bytes) : Choice :=
  let x := r.args.getD
  let n₁ := firstLen r.iovs
  match r.call, σ.desc (x 0 0) with
  | .clockTimeGet, _ =>
    { time := if x 0 0 < 2 then some (σ.clocks.getD (x 0 0) 0) else none, bytes := b }
  | .fdRead, some ⟨.stream 0 _, _, _, _⟩ =>
    { count := if n₁ = 0 then none else some (min n₁ (min σ.stdin.length stdinChunk))
      bytes := b }
  | .fdRead, some ⟨.file n pos, _, _, _⟩ =>
    { count := if fileMax < pos + n₁ then none else some (min n₁ ((σ.data n).length - pos))
      bytes := b }
  | .fdWrite, some ⟨.stream (_ + 1) _, _, _, _⟩ => { count := some n₁, bytes := b }
  | .fdWrite, some ⟨.file n pos, fl, _, _⟩ =>
    let app := flag fl Fdflags.append
    let off := if app then (σ.data n).length else pos
    { count := if app ∧ fileMax ≤ off ∧ n₁ ≠ 0 then none
        else if !app ∧ fileMax < off + n₁ then none else some (min n₁ (fileMax - off))
      bytes := b }
  | .pathOpen, _ =>
    { fd := if σ.nextFd < 2 ^ 31 then some σ.nextFd else none
      ino := if σ.nextIno < 2 ^ 64 then some σ.nextIno else none
      rights := some (x 5 0, x 6 0), bytes := b }
  | .pathCreateDirectory, _ =>
    { ino := if σ.nextIno < 2 ^ 64 then some σ.nextIno else none, bytes := b }
  | .pathFilestatGet, _ => { stat := some ⟨1, 0, 0, 0, 0⟩, bytes := b }
  | _, _ => { bytes := b }

theorem clocks_set_getD (l : List Nat) (i : Nat) : l.set i (l.getD i 0) = l := by
  induction l generalizing i with
  | nil => rfl
  | cons t l ih => cases i <;> simp_all

/-- T3a: `run` at `E`'s materialized values = `run` at `E`'s choice. -/
theorem run_ofE (σ : State) (r : Req) (b : Bytes) :
    run σ r (ofE σ r b) = run σ r { bytes := b } := by
  rcases r with ⟨call, a, iovs, data, path⟩
  cases call
  case clockTimeGet =>
    by_cases hid : a.getD 0 0 < 2
    · simp only [run, ofE, hid, ↓reduceIte, clocks_set_getD]
    · simp only [run, ofE, hid, ↓reduceIte]
  case fdRead =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => simp only [run, hd]
    | some d =>
      rcases d with ⟨kind, fl, rb, ri⟩
      cases kind with
      | stream k t =>
        rcases k with _ | k
        · simp only [run, ofE, hd]
          split_ifs <;> simp_all
        · simp only [run, hd]
      | file n pos =>
        simp only [run, ofE, hd]
        split_ifs <;> simp_all
      | dir n p => simp only [run, hd]
  case fdWrite =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => simp only [run, hd]
    | some d =>
      rcases d with ⟨kind, fl, rb, ri⟩
      cases kind with
      | stream k t =>
        rcases k with _ | k
        · simp only [run, hd, ↓reduceIte]
        · simp only [run, ofE, hd, Option.getD_some, Option.getD_none]
      | file n pos =>
        simp only [run, ofE, hd]
        split_ifs <;> simp_all
      | dir n p => simp only [run, hd]
  case pathOpen =>
    by_cases hf : σ.nextFd < 2 ^ 31 <;> by_cases hi : σ.nextIno < 2 ^ 64
    all_goals
      have hn : (2 ^ 64 ≤ σ.nextIno) = ¬ σ.nextIno < 2 ^ 64 := propext Nat.not_lt.symm
      simp only [run, ofE, hf, hi, hn, ↓reduceIte, Option.getD_some, Option.getD_none,
        reduceCtorEq, and_false, not_true_eq_false, not_false_eq_true, and_true]
  case pathCreateDirectory =>
    by_cases hi : σ.nextIno < 2 ^ 64
    all_goals
      have hn : (2 ^ 64 ≤ σ.nextIno) = ¬ σ.nextIno < 2 ^ 64 := propext Nat.not_lt.symm
      simp only [run, ofE, hi, hn, ↓reduceIte, Option.getD_some, Option.getD_none, reduceCtorEq,
        and_false, not_true_eq_false, not_false_eq_true, and_true]
  all_goals rfl

@[simp] theorem ofE_err (σ : State) (r : Req) (b : Bytes) : (ofE σ r b).err = none := by
  unfold ofE; dsimp only; split <;> rfl

/-- T3a at `step` (U29b's host computes `step` at `E`'s choice). -/
theorem step_ofE (σ : State) (r : Req) (b : Bytes) :
    step σ r (ofE σ r b) = step σ r { bytes := b } := by
  simp only [step, ofE_err, run_ofE]

/-- The first non-empty length is at most the total. -/
theorem firstLen_le_sum (iovs : List (Nat × Nat)) : firstLen iovs ≤ (iovs.map (·.2)).sum := by
  induction iovs with
  | nil => simp [firstLen]
  | cons v iovs ih =>
    simp only [firstLen, List.map_cons, List.find?_cons, List.sum_cons] at ih ⊢
    split <;> simp_all

/-- A non-empty request has a non-empty first buffer. -/
theorem firstLen_pos (iovs : List (Nat × Nat)) (h : 0 < (iovs.map (·.2)).sum) :
    0 < firstLen iovs := by
  induction iovs with
  | nil => simp at h
  | cons v iovs ih =>
    simp only [firstLen, List.map_cons, List.find?_cons, List.sum_cons] at ih h ⊢
    split
    · rename_i hv; simp at hv; simp; omega
    · rename_i hv; simp at hv; simp only [hv, Nat.zero_add] at h; exact ih h

/-- u32 buffer lengths: a u32 first length. -/
theorem firstLen_lt {iovs : List (Nat × Nat)} (h : ∀ v ∈ iovs, v.2 < 2 ^ 32) :
    firstLen iovs < 2 ^ 32 := by
  induction iovs with
  | nil => simp [firstLen]
  | cons v iovs ih =>
    simp only [firstLen, List.map_cons, List.find?_cons] at ih ⊢
    have hv := h v (by simp)
    split
    · simpa using hv
    · exact ih fun w hw => h w (by simp [hw])

theorem getD_lt {l : List Nat} {B : Nat} (h : ∀ t ∈ l, t < B) (hB : 0 < B) (i : Nat) :
    l.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simpa
  | some t => simpa using h t (List.mem_of_getElem? hi)

/-- T3a: on a well-formed state `E`'s materialized values meet `ChoiceOK` field by field. -/
theorem ofE_ok {σ : State} (hw : σ.Wf) {r : Req} (hr : ∀ v ∈ r.iovs, v.2 < 2 ^ 32) (b : Bytes) :
    ChoiceOK σ r (ofE σ r b) := by
  rcases r with ⟨call, a, iovs, data, path⟩
  have h1 := firstLen_le_sum iovs
  have h2 : (iovs.map (·.2)).sum = 0 ∨ 0 < firstLen iovs := by
    rcases Nat.eq_zero_or_pos (iovs.map (·.2)).sum with h | h
    · exact .inl h
    · exact .inr (firstLen_pos iovs h)
  have h3 : firstLen iovs < 2 ^ 32 := firstLen_lt hr
  have hclk : ∀ t ∈ σ.clocks, t < 2 ^ 64 := hw.2.2.2.2.2.2.2.2.2.2.2.2
  cases call
  case clockTimeGet =>
    by_cases hid : a.getD 0 0 < 2
    · simp only [ofE, hid, ↓reduceIte]
      refine ⟨by simp, by simp, by simp, ?_, by simp, by simp, by simp⟩
      intro t ht
      obtain rfl := Option.some.inj ht
      exact ⟨getD_lt hclk (by decide) _, fun _ => Nat.le_refl _⟩
    · simp only [ofE, hid, ↓reduceIte]
      exact choiceOK_none _ _ b
  case fdRead =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => simp only [ofE, hd]; exact choiceOK_none _ _ b
    | some d =>
      rcases d with ⟨kind, fl, rb, ri⟩
      cases kind with
      | stream j t =>
        rcases j with _ | j
        · by_cases hz : firstLen iovs = 0
          · simp only [ofE, hd, hz, ↓reduceIte]; exact choiceOK_none _ _ b
          · simp only [ofE, hd, hz, ↓reduceIte]
            refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, by simp⟩
            intro k hk
            obtain rfl := Option.some.inj hk
            simp only [maxCount, hd, stdinChunk]
            omega
        · simp only [ofE, hd]; exact choiceOK_none _ _ b
      | file n pos =>
        simp only [ofE, hd]
        split
        · exact choiceOK_none _ _ b
        refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, by simp⟩
        intro k hk
        obtain rfl := Option.some.inj hk
        simp only [maxCount, hd]
        omega
      | dir n p => simp only [ofE, hd]; exact choiceOK_none _ _ b
  case fdWrite =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => simp only [ofE, hd]; exact choiceOK_none _ _ b
    | some d =>
      rcases d with ⟨kind, fl, rb, ri⟩
      cases kind with
      | stream j t =>
        rcases j with _ | j
        · simp only [ofE, hd]; exact choiceOK_none _ _ b
        · simp only [ofE, hd]
          refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, by simp⟩
          intro k hk
          obtain rfl := Option.some.inj hk
          simp only [maxCount, hd]
          omega
      | file n pos =>
        by_cases hap : flag fl Fdflags.append = true <;>
          simp only [ofE, hd, hap, ↓reduceIte, Bool.false_eq_true, Bool.not_true,
            Bool.not_false, true_and, false_and] <;> split_ifs
        all_goals try exact choiceOK_none _ _ b
        all_goals
          rename_i hlim
          refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, by simp⟩
          intro k hk
          obtain rfl := Option.some.inj hk
          simp only [maxCount, hd, hap, ↓reduceIte, Bool.false_eq_true, fileMax] at hlim ⊢
          omega
      | dir n p => simp only [ofE, hd]; exact choiceOK_none _ _ b
  case pathOpen =>
    simp only [ofE]
    refine ⟨by simp, by simp, ?_, by simp, ?_, ?_, by simp⟩
    · intro f hf
      split at hf
      · obtain rfl := Option.some.inj hf; exact ⟨by assumption, nextFd_fresh hw⟩
      · simp at hf
    · intro i hi
      dsimp only at hi
      split at hi
      · obtain rfl := Option.some.inj hi; exact ⟨by assumption, nextIno_fresh σ⟩
      · simp at hi
    · intro rb ri h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp [subset]
  case pathCreateDirectory =>
    simp only [ofE]
    refine ⟨by simp, by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i hi
    split at hi
    · obtain rfl := Option.some.inj hi; exact ⟨by assumption, nextIno_fresh σ⟩
    · simp at hi
  case pathFilestatGet =>
    simp only [ofE]
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro sc h
    obtain rfl := Option.some.inj h
    decide
  all_goals exact choiceOK_none _ _ b

theorem read_lt (m : MemInst) (ea k : Nat) : m.read ea k < 256 ^ k := by
  induction k generalizing ea with
  | zero => simp [MemInst.read]
  | succ k ih =>
    simp only [MemInst.read, Nat.pow_succ]
    have := ih (ea + 1)
    have hb : (m.byte ea).toNat < 256 := (m.byte ea).toNat_lt
    omega

/-- Decoded iovec lengths are u32. -/
theorem decode_iovs_u32 (c : Call) (m : MemInst) (a : List Nat) :
    ∀ v ∈ (decode c m a).iovs, v.2 < 2 ^ 32 := by
  intro v hv
  simp only [decode, iovecs] at hv
  split at hv
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    exact read_lt m _ 4
  · simp at hv

end FVA.Wasi
