import FVA.Proof.Exec.Det
import FVA.Proof.Lib.Attr

/-!
# Symbolic execution by unique reference-stepper steps (U8 L1)

`walk k c` = `k` steps of `Ref.step`, each the spec's only one (`uniqueStep`): no NaN result, no
growth, no host call, no pending trap choice. A walk carries `Must` back to its start
(`must_of_walk`) and is an execution of the spec (`steps_of_walk`), so a proof runs the program
symbolically while its control flow is fixed, then splits on the next branch condition.
`simp only [walk, wasm_step]` unfolds a walk over a concrete instruction list.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

theorem _root_.FVA.Wasm.Exec.Val.instr_inj {v w : Val} : v.instr = w.instr ↔ v = w := by
  constructor
  · intro h
    have := congrArg toVal h
    rwa [toVal_instr, toVal_instr, Option.some.injEq] at this
  · rintro rfl; rfl

/-- `k` unique steps from `c`. -/
def walk : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => bif uniqueStep c then (step c).bind (walk k) else none

@[simp] theorem walk_zero (c : Config) : walk 0 c = some c := rfl

theorem walk_add (a b : Nat) (c : Config) : walk (a + b) c = (walk a c).bind (walk b) := by
  induction a generalizing c with
  | zero => simp [walk]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [walk]
    cases uniqueStep c <;> simp only [Bool.cond_false, Bool.cond_true, Option.bind_none]
    cases step c <;> simp [ih]

/-- Splits a walk at its first `a` steps. -/
theorem walk_split {a b : Nat} {c m c' : Config} (h₁ : walk a c = some m)
    (h₂ : walk b m = some c') : walk (a + b) c = some c' := by
  rw [walk_add, h₁]; exact h₂

theorem must_of_walk {H : HostSem} {Q : Outcome → Prop} {k : Nat} {c c' : Config}
    (h : walk k c = some c') (hc : Must H Q c') : Must H Q c := by
  induction k generalizing c with
  | zero => cases h; exact hc
  | succ k ih =>
    cases hu : uniqueStep c with
    | false => simp only [walk, hu, Bool.cond_false, reduceCtorEq] at h
    | true =>
      simp only [walk, hu, Bool.cond_true] at h
      cases hd : step c with
      | none => simp only [hd, Option.bind_none, reduceCtorEq] at h
      | some d =>
        simp only [hd, Option.bind_some] at h
        exact must_of_step hd hu (ih h)

/-- A walk is an execution of the spec. -/
theorem steps_of_walk {H : HostSem} {k : Nat} {c c' : Config} (h : walk k c = some c') :
    Steps H c c' := by
  induction k generalizing c with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ k ih =>
    cases hu : uniqueStep c with
    | false => simp only [walk, hu, Bool.cond_false, reduceCtorEq] at h
    | true =>
      simp only [walk, hu, Bool.cond_true] at h
      cases hd : step c with
      | none => simp only [hd, Option.bind_none, reduceCtorEq] at h
      | some d =>
        simp only [hd, Option.bind_some] at h
        exact Relation.ReflTransGen.head (step_sound hd) (ih h)

theorem may_of_walk {H : HostSem} {Q : Outcome → Prop} {k : Nat} {c c' : Config}
    (h : walk k c = some c') (hm : May H Q c') : May H Q c := by
  obtain ⟨d, o, hs, hf, hq⟩ := hm
  exact ⟨d, o, (steps_of_walk h).trans hs, hf, hq⟩

/-- `must_of_step` with the successor left implicit, so a tactic computes it from the step. -/
theorem must_of_step' {H : HostSem} {Q : Outcome → Prop} {c : Config}
    (hu : uniqueStep c = true) (hs : (step c).isSome = true)
    (h : ∀ c', step c = some c' → Must H Q c') : Must H Q c := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hs
  exact must_of_step hc' hu (h c' hc')

/-- A walk that ends in a final configuration proves `Must` of its start. -/
theorem must_of_walk_final {H : HostSem} {Q : Outcome → Prop} {k : Nat} {c c' : Config}
    {o : Outcome} (h : walk k c = some c') (hf : Final c' o) (hq : Q o) : Must H Q c :=
  must_of_walk h (Must.done hf hq)

-- every non-constant instruction: `toVal (.plain i) = none` by `rfl` (generated per constructor of
-- `Instr`: `simp only` cannot discharge a catch-all match's side conditions)
@[wasm_step] theorem toVal_iunop {w} {op} : toVal (.plain (.iunop w op)) = none := id rfl
@[wasm_step] theorem toVal_ibinop {w} {op} : toVal (.plain (.ibinop w op)) = none := id rfl
@[wasm_step] theorem toVal_itestEqz {w} : toVal (.plain (.itestEqz w)) = none := id rfl
@[wasm_step] theorem toVal_irelop {w} {op} : toVal (.plain (.irelop w op)) = none := id rfl
@[wasm_step] theorem toVal_funop {w} {op} : toVal (.plain (.funop w op)) = none := id rfl
@[wasm_step] theorem toVal_fbinop {w} {op} : toVal (.plain (.fbinop w op)) = none := id rfl
@[wasm_step] theorem toVal_frelop {w} {op} : toVal (.plain (.frelop w op)) = none := id rfl
@[wasm_step] theorem toVal_cvtop {op} : toVal (.plain (.cvtop op)) = none := id rfl
@[wasm_step] theorem toVal_refIsNull : toVal (.plain (.refIsNull)) = none := id rfl
@[wasm_step] theorem toVal_refFunc {x} : toVal (.plain (.refFunc x)) = none := id rfl
@[wasm_step] theorem toVal_drop : toVal (.plain (.drop)) = none := id rfl
@[wasm_step] theorem toVal_select {ts} : toVal (.plain (.select ts)) = none := id rfl
@[wasm_step] theorem toVal_localGet {x} : toVal (.plain (.localGet x)) = none := id rfl
@[wasm_step] theorem toVal_localSet {x} : toVal (.plain (.localSet x)) = none := id rfl
@[wasm_step] theorem toVal_localTee {x} : toVal (.plain (.localTee x)) = none := id rfl
@[wasm_step] theorem toVal_globalGet {x} : toVal (.plain (.globalGet x)) = none := id rfl
@[wasm_step] theorem toVal_globalSet {x} : toVal (.plain (.globalSet x)) = none := id rfl
@[wasm_step] theorem toVal_tableGet {x} : toVal (.plain (.tableGet x)) = none := id rfl
@[wasm_step] theorem toVal_tableSet {x} : toVal (.plain (.tableSet x)) = none := id rfl
@[wasm_step] theorem toVal_tableSize {x} : toVal (.plain (.tableSize x)) = none := id rfl
@[wasm_step] theorem toVal_tableGrow {x} : toVal (.plain (.tableGrow x)) = none := id rfl
@[wasm_step] theorem toVal_tableFill {x} : toVal (.plain (.tableFill x)) = none := id rfl
@[wasm_step] theorem toVal_tableCopy {x} {y} : toVal (.plain (.tableCopy x y)) = none := id rfl
@[wasm_step] theorem toVal_tableInit {x} {y} : toVal (.plain (.tableInit x y)) = none := id rfl
@[wasm_step] theorem toVal_elemDrop {x} : toVal (.plain (.elemDrop x)) = none := id rfl
@[wasm_step] theorem toVal_load {t} {m} : toVal (.plain (.load t m)) = none := id rfl
@[wasm_step] theorem toVal_loadPacked {w} {p} {sx} {m} :
    toVal (.plain (.loadPacked w p sx m)) = none := id rfl
@[wasm_step] theorem toVal_store {t} {m} : toVal (.plain (.store t m)) = none := id rfl
@[wasm_step] theorem toVal_storePacked {w} {p} {m} :
    toVal (.plain (.storePacked w p m)) = none := id rfl
@[wasm_step] theorem toVal_memorySize : toVal (.plain (.memorySize)) = none := id rfl
@[wasm_step] theorem toVal_memoryGrow : toVal (.plain (.memoryGrow)) = none := id rfl
@[wasm_step] theorem toVal_memoryFill : toVal (.plain (.memoryFill)) = none := id rfl
@[wasm_step] theorem toVal_memoryCopy : toVal (.plain (.memoryCopy)) = none := id rfl
@[wasm_step] theorem toVal_memoryInit {x} : toVal (.plain (.memoryInit x)) = none := id rfl
@[wasm_step] theorem toVal_dataDrop {x} : toVal (.plain (.dataDrop x)) = none := id rfl
@[wasm_step] theorem toVal_unreachable : toVal (.plain (.unreachable)) = none := id rfl
@[wasm_step] theorem toVal_nop : toVal (.plain (.nop)) = none := id rfl
@[wasm_step] theorem toVal_block {bt} {body} : toVal (.plain (.block bt body)) = none := id rfl
@[wasm_step] theorem toVal_loop {bt} {body} : toVal (.plain (.loop bt body)) = none := id rfl
@[wasm_step] theorem toVal_if_ {bt} {thn} {els} : toVal (.plain (.if_ bt thn els)) = none := id rfl
@[wasm_step] theorem toVal_br {l} : toVal (.plain (.br l)) = none := id rfl
@[wasm_step] theorem toVal_brIf {l} : toVal (.plain (.brIf l)) = none := id rfl
@[wasm_step] theorem toVal_brTable {ls} {l} : toVal (.plain (.brTable ls l)) = none := id rfl
@[wasm_step] theorem toVal_return_ : toVal (.plain (.return_)) = none := id rfl
@[wasm_step] theorem toVal_call {x} : toVal (.plain (.call x)) = none := id rfl
@[wasm_step] theorem toVal_callIndirect {x} {y} :
    toVal (.plain (.callIndirect x y)) = none := id rfl

/-- A single value is no pending trap (the value may be a symbolic `if`). -/
@[wasm_step] theorem isTrapOnly_val (v : Val) : isTrapOnly [v.instr] = false := isTrapOnly_vals [v]

-- the instruction-list walkers, one propositional lemma per case: unfolding their equations
-- definitionally leaves `match toVal e` for the kernel, which then evaluates `toVal` on a
-- symbolic value through `Nat` arithmetic (recursion as deep as a constant like `4294967295`)
@[wasm_step] theorem seq_nil (s : Store) (f : Frame) (vs : List Val) : seq s f vs [] = .final := by
  rw [seq]
@[wasm_step] theorem seq_cons_none {s : Store} {f : Frame} {vs : List Val} {e : AInstr}
    (rest : List AInstr) (h : toVal e = none) : seq s f vs (e :: rest) = atInstr s f vs e rest := by
  rw [seq, h]
@[wasm_step] theorem seqUnique_nil (s : Store) (f : Frame) (vs : List Val) :
    seqUnique s f vs [] = true := by
  rw [seqUnique]
@[wasm_step] theorem seqUnique_cons_none {s : Store} {f : Frame} {vs : List Val} {e : AInstr}
    (rest : List AInstr) (h : toVal e = none) :
    seqUnique s f vs (e :: rest) = atUnique s f vs e := by
  rw [seqUnique, h]
@[wasm_step] theorem seqTraps_nil : seqTraps [] = false := by
  rw [seqTraps]
@[wasm_step] theorem seqTraps_cons_none {e : AInstr} (rest : List AInstr) (h : toVal e = none) :
    seqTraps (e :: rest) = atTrap e := by
  rw [seqTraps, h]

-- a value at the head (a stack entry `v.instr`, or a constant whose literal is in range): no
-- side condition with a fresh variable, so simp's discharger never has to invent `v`
@[wasm_step] theorem seq_cons_val (s : Store) (f : Frame) (vs : List Val) (v : Val)
    (rest : List AInstr) : seq s f vs (v.instr :: rest) = seq s f (v :: vs) rest := by
  rw [seq, toVal_instr]
@[wasm_step] theorem seqUnique_cons_val (s : Store) (f : Frame) (vs : List Val) (v : Val)
    (rest : List AInstr) : seqUnique s f vs (v.instr :: rest) = seqUnique s f (v :: vs) rest := by
  rw [seqUnique, toVal_instr]
@[wasm_step] theorem seqTraps_cons_val (v : Val) (rest : List AInstr) :
    seqTraps (v.instr :: rest) = seqTraps rest := by
  rw [seqTraps, toVal_instr]
@[wasm_step] theorem seq_cons_i32 (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (rest : List AInstr) (h : n < 2 ^ 32) :
    seq s f vs (.plain (.iconst .w32 n) :: rest) =
      seq s f (.i32 (BitVec.ofNat 32 n) :: vs) rest := by
  have : n < 4294967296 := h
  rw [seq]; simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem seq_cons_i64 (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (rest : List AInstr) (h : n < 2 ^ 64) :
    seq s f vs (.plain (.iconst .w64 n) :: rest) =
      seq s f (.i64 (BitVec.ofNat 64 n) :: vs) rest := by
  have : n < 18446744073709551616 := h
  rw [seq]; simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem seqUnique_cons_i32 (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (rest : List AInstr) (h : n < 2 ^ 32) :
    seqUnique s f vs (.plain (.iconst .w32 n) :: rest) =
      seqUnique s f (.i32 (BitVec.ofNat 32 n) :: vs) rest := by
  have : n < 4294967296 := h
  rw [seqUnique]; simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem seqUnique_cons_i64 (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (rest : List AInstr) (h : n < 2 ^ 64) :
    seqUnique s f vs (.plain (.iconst .w64 n) :: rest) =
      seqUnique s f (.i64 (BitVec.ofNat 64 n) :: vs) rest := by
  have : n < 18446744073709551616 := h
  rw [seqUnique]; simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem seqTraps_cons_i32 (n : Nat) (rest : List AInstr) (h : n < 2 ^ 32) :
    seqTraps (.plain (.iconst .w32 n) :: rest) = seqTraps rest := by
  have : n < 4294967296 := h
  rw [seqTraps]; simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem seqTraps_cons_i64 (n : Nat) (rest : List AInstr) (h : n < 2 ^ 64) :
    seqTraps (.plain (.iconst .w64 n) :: rest) = seqTraps rest := by
  have : n < 18446744073709551616 := h
  rw [seqTraps]; simp [toVal, Nat.blt_eq, this]

-- the non-value cases of the mutual walkers, likewise propositional
@[wasm_step] theorem atUnique_label (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (cont : List Instr) (body : List AInstr) :
    atUnique s f vs (.label n cont body) = seqUnique s f [] body := by unfold atUnique; rfl
@[wasm_step] theorem atUnique_frame (s : Store) (f : Frame) (vs : List Val) (n : Nat) (fi : Frame)
    (body : List AInstr) : atUnique s f vs (.frame n fi body) = seqUnique s fi [] body := by
  unfold atUnique; rfl
@[wasm_step] theorem atUnique_invoke (s : Store) (f : Frame) (vs : List Val) (a : Nat) :
    atUnique s f vs (.invoke a) = match s.funcs[a]? with
      | some (.host ..) => false
      | _ => true := by unfold atUnique; rfl
@[wasm_step] theorem atUnique_plain (s : Store) (f : Frame) (vs : List Val) (i : Instr) :
    atUnique s f vs (.plain i) = instrUnique i vs := by unfold atUnique; rfl
@[wasm_step] theorem atUnique_trap (s : Store) (f : Frame) (vs : List Val) :
    atUnique s f vs .trap = false := by unfold atUnique; rfl
@[wasm_step] theorem atTrap_trap : atTrap .trap = true := by unfold atTrap; rfl
@[wasm_step] theorem atTrap_label (n : Nat) (cont : List Instr) (body : List AInstr) :
    atTrap (.label n cont body) = seqTraps body := by unfold atTrap; rfl
@[wasm_step] theorem atTrap_frame (n : Nat) (fi : Frame) (body : List AInstr) :
    atTrap (.frame n fi body) = seqTraps body := by unfold atTrap; rfl
@[wasm_step] theorem atTrap_plain (i : Instr) : atTrap (.plain i) = false := by unfold atTrap; rfl
@[wasm_step] theorem atTrap_invoke (a : Nat) : atTrap (.invoke a) = false := by unfold atTrap; rfl
@[wasm_step] theorem atInstr_trap (s : Store) (f : Frame) (vs : List Val) (rest : List AInstr) :
    atInstr s f vs .trap rest =
      bif vs.isEmpty && rest.isEmpty then .final else .step s f [.trap] := by
  unfold atInstr; rfl
@[wasm_step] theorem atInstr_label (s : Store) (f : Frame) (vs : List Val) (n : Nat)
    (cont : List Instr) (body rest : List AInstr) :
    atInstr s f vs (.label n cont body) rest = match seq s f [] body with
      | .final =>
        .step s f (vals vs.reverse ++ (bif isTrapOnly body then [.trap] else body) ++ rest)
      | .step s' f' body' => .step s' f' (vals vs.reverse ++ [.label n cont body'] ++ rest)
      | .br 0 bvs => bif Nat.blt bvs.length n then .stuck
        else .step s f (vals vs.reverse ++ vals (bvs.take n).reverse ++ cont.map .plain ++ rest)
      | .br (k + 1) bvs => .br k bvs
      | .ret bvs => .ret bvs
      | .stuck => .stuck := by unfold atInstr; rfl
@[wasm_step] theorem atInstr_frame (s : Store) (f : Frame) (vs : List Val) (n : Nat) (fi : Frame)
    (body rest : List AInstr) :
    atInstr s f vs (.frame n fi body) rest = match seq s fi [] body with
      | .final => bif isTrapOnly body then .step s f (vals vs.reverse ++ [.trap] ++ rest)
        else bif Nat.beq body.length n then .step s f (vals vs.reverse ++ body ++ rest)
        else .stuck
      | .step s' fi' body' => .step s' f (vals vs.reverse ++ [.frame n fi' body'] ++ rest)
      | .ret bvs => bif Nat.blt bvs.length n then .stuck
        else .step s f (vals vs.reverse ++ vals (bvs.take n).reverse ++ rest)
      | .br _ _ => .stuck
      | .stuck => .stuck := by unfold atInstr; rfl
@[wasm_step] theorem atInstr_invoke (s : Store) (f : Frame) (vs : List Val) (a : Nat)
    (rest : List AInstr) :
    atInstr s f vs (.invoke a) rest = match s.funcs[a]? with
      | some (.wasm ft inst code) =>
        bif Nat.blt vs.length ft.params.length then .stuck
        else .step s f (vals (vs.drop ft.params.length).reverse ++
          [.frame ft.results.length ⟨(vs.take ft.params.length).reverse ++ code.localDefaults, inst⟩
            [.label ft.results.length [] (code.body.map .plain)]] ++ rest)
      | _ => .stuck := by unfold atInstr; rfl
@[wasm_step] theorem atInstr_br (s : Store) (f : Frame) (vs : List Val) (k : Nat)
    (rest : List AInstr) : atInstr s f vs (.plain (.br k)) rest = .br k vs := by unfold atInstr; rfl
@[wasm_step] theorem atInstr_return (s : Store) (f : Frame) (vs : List Val) (rest : List AInstr) :
    atInstr s f vs (.plain .return_) rest = .ret vs := by unfold atInstr; rfl
@[wasm_step] theorem atInstr_instr (s : Store) (f : Frame) (vs : List Val) {i : Instr}
    (rest : List AInstr) (hb : ∀ k, i ≠ .br k) (hr : i ≠ .return_) :
    atInstr s f vs (.plain i) rest = match instrStep s f i vs with
      | some (s', f', stk, out) => .step s' f' (vals stk.reverse ++ out ++ rest)
      | none => .stuck := by
  cases i <;> first | (exact absurd rfl (hb _)) | (exact absurd rfl hr) | (unfold atInstr; rfl)
attribute [wasm_step] reduceCtorEq ne_eq not_false_eq_true implies_true forall_const
  Instr.br.injEq
-- value comparisons (`select`, `br_if`, `if`): `==` as `decide`, settled by hypotheses or literals
@[wasm_step] theorem beq_decide' {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]
attribute [wasm_step] eq_self List.flatMap_cons List.flatMap_nil List.replicate_succ
  List.replicate_zero
-- `Nat.blt`/`Nat.beq` on lengths and indices: decided by the literal simprocs
@[wasm_step] theorem blt_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]
@[wasm_step] theorem beq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

-- constants with an in-range literal (the side condition closes by `decide` on a numeral)
@[wasm_step] theorem toVal_iconst32 {n : Nat} (h : n < 2 ^ 32) :
    toVal (.plain (.iconst .w32 n)) = some (.i32 (BitVec.ofNat 32 n)) := by
  have : n < 4294967296 := h
  simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem toVal_iconst64 {n : Nat} (h : n < 2 ^ 64) :
    toVal (.plain (.iconst .w64 n)) = some (.i64 (BitVec.ofNat 64 n)) := by
  have : n < 18446744073709551616 := h
  simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem toVal_fconst32 {n : Nat} (h : n < 2 ^ 32) :
    toVal (.plain (.fconst .w32 n)) = some (.f32 (BitVec.ofNat 32 n)) := by
  have : n < 4294967296 := h
  simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem toVal_fconst64 {n : Nat} (h : n < 2 ^ 64) :
    toVal (.plain (.fconst .w64 n)) = some (.f64 (BitVec.ofNat 64 n)) := by
  have : n < 18446744073709551616 := h
  simp [toVal, Nat.blt_eq, this]
@[wasm_step] theorem toVal_refNull (t : RefType) :
    toVal (.plain (.refNull t)) = some (.ref (.null t)) := id rfl

-- `isTrapOnly` by cases, never unfolded (its catch-all match would block a symbolic value)
@[wasm_step] theorem isTrapOnly_nil : isTrapOnly [] = false := id rfl
@[wasm_step] theorem isTrapOnly_trap : isTrapOnly [.trap] = true := id rfl
@[wasm_step] theorem isTrapOnly_cons₂ (a b : AInstr) (l : List AInstr) :
    isTrapOnly (a :: b :: l) = false := by
  cases a <;> rfl
@[wasm_step] theorem isTrapOnly_plain (i : Instr) : isTrapOnly [.plain i] = false := id rfl
@[wasm_step] theorem isTrapOnly_label (n : Nat) (c : List Instr) (b : List AInstr) :
    isTrapOnly [.label n c b] = false := id rfl
@[wasm_step] theorem isTrapOnly_frame (n : Nat) (f : Frame) (b : List AInstr) :
    isTrapOnly [.frame n f b] = false := id rfl
@[wasm_step] theorem isTrapOnly_invoke (a : Nat) : isTrapOnly [.invoke a] = false := id rfl

@[wasm_step] theorem toVal_invoke (a : Nat) : toVal (.invoke a) = none := id rfl
@[wasm_step] theorem toVal_label (n : Nat) (c : List Instr) (b : List AInstr) :
    toVal (.label n c b) = none := id rfl
@[wasm_step] theorem toVal_frame (n : Nat) (f : Frame) (b : List AInstr) :
    toVal (.frame n f b) = none := id rfl
@[wasm_step] theorem toVal_trap : toVal .trap = none := id rfl

attribute [wasm_step] walk uniqueStep instrUnique numUnique step runDet
  instrStep numStep toVal_instr isTrapOnly_vals
attribute [wasm_step] BlockType.expand Func.localDefaults ValType.default mem0 tableAt callTarget
  numOut iunop ibinop irelop NumType.val NumType.bytes PackSize.bits packedVal

-- the generic rewriting a step needs, so `simp only [wasm_step]` runs without the default set
-- (its arithmetic simp lemmas leave proof steps the kernel can only check by unfolding `Nat`
-- arithmetic on symbolic values, recursion as deep as a literal like `4294967295`)
attribute [wasm_step] List.map_cons List.map_nil List.cons_append List.nil_append List.append_nil
  List.reverse_cons List.reverse_nil List.singleton_append List.length_cons List.length_nil
  List.take_succ_cons List.take_zero List.drop_succ_cons List.drop_zero List.isEmpty_nil
  List.isEmpty_cons List.getElem?_cons_zero List.getElem?_cons_succ List.set_cons_zero
  List.set_cons_succ List.reverse_append List.append_assoc Bool.cond_true Bool.cond_false
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and Bool.not_true Bool.not_false
  Option.bind_some Option.bind_none Option.map_some Option.map_none Option.some.injEq
  Option.getD_some Option.getD_none Option.isSome_some ite_true ite_false Nat.blt_eq Nat.beq_eq
  decide_true decide_false
-- literal-only arithmetic (the kernel checks it with GMP)
attribute [wasm_step] Nat.reducePow Nat.reduceLT Nat.reduceGT Nat.reduceLeDiff Nat.reduceAdd
  Nat.reduceSub
  Nat.reduceMul Nat.reduceMod Nat.reduceDiv Nat.reduceBEq Nat.reduceBNe Nat.reduceEqDiff

/-- One unique step stated on the configuration's parts, never through `step`: a proof through
`step`'s `Option` result makes the kernel evaluate `Nat` arithmetic of symbolic payloads next to
large literals (recursion as deep as `4294967295`), while `seq`-level rewrites stay cheap. -/
theorem must_of_seq {H : HostSem} {Q : Outcome → Prop} {s : Store} {f : Frame}
    {l : List AInstr} {s' : Store} {f' : Frame} {l' : List AInstr}
    (hu : seqUnique s f [] l = true) (hs : seq s f [] l = .step s' f' l')
    (h : Must H Q ⟨s', f', l'⟩) : Must H Q ⟨s, f, l⟩ :=
  must_of_step (by simp only [step, hs]) (by simpa only [uniqueStep] using hu) h

open Lean Meta Elab Tactic in
/-- One unique reference step on a goal `Must H Q ⟨s, f, l⟩`: simp (`only [wasm_step, lemmas]`)
computes `seq s f [] l` to `.step s' f' l'` and shows uniqueness; the goal moves to
`Must H Q ⟨s', f', l'⟩` through `must_of_seq`. -/
elab "wasm_step1" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (H, Q, c) := ty.consumeMData.app3? ``Must
    | throwError "wasm_step1: the goal is no `Must`"
  let c ← whnfR c
  let some (s, f, l) := c.app3? ``Config.mk | throwError "wasm_step1: no literal configuration"
  let stx ← `(tactic| simp only [wasm_step, $xs,*])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let nil ← mkListLit (mkConst ``Val) []
  let (r, _) ← simp (← mkAppM ``seq #[s, f, nil, l]) ctx simprocs
  let out ← instantiateMVars r.expr
  let some (s', f', l') := (← whnfR out).consumeMData.app3? ``Out.step
    | throwError m!"wasm_step1: the next step is not computed: {out}"
  let hs ← r.getProof
  let hu ← mkFreshExprMVar (← mkEq (← mkAppM ``seqUnique #[s, f, nil, l]) (mkConst ``Bool.true))
  let rest ← evalTacticAt stx hu.mvarId!
  unless rest.isEmpty do throwError "wasm_step1: uniqueness of the step is not shown"
  let next ← mkFreshExprMVar (← mkAppM ``Must #[H, Q, ← mkAppM ``Config.mk #[s', f', l']])
  g.assign (← mkAppM ``must_of_seq #[hu, hs, next])
  replaceMainGoal [next.mvarId!]

/-- `wasm_run [lemmas]` on a goal `Must H Q c`: `wasm_step1` until `c` is final (or the next step
is a choice point or needs a fact the lemmas lack). -/
macro "wasm_run" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat wasm_step1 [$ls,*])

end FVA.Wasm.Exec.Ref
