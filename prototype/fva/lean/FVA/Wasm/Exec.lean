import FVA.Wasm.Semantics
import FVA.Wasm.Attr

/-!
# Symbolic execution lemmas — proof support, outside the trusted base

One `rfl` equation per instruction shape, so `simp only [wasm_exec]` steps lifted code
instruction by instruction without unfolding the whole `exec`/`step` match tree.
Fuel is written `f + 1`; proofs pick fuel `k + N` for a symbolic `k`.
-/

namespace FVA.Wasm


section
variable {f : Nat} {is : List Instr} {st : List Val} {ls : List Val}

attribute [wasm_exec] binOp relOp ofBool Val.type ValType.zero setLocal

@[wasm_exec] theorem exec_nil (s) : exec (f + 1) [] s = .done s := id rfl
@[wasm_exec] theorem exec_ret (s) : exec (f + 1) (.ret :: is) s = .ret s := id rfl
@[wasm_exec] theorem exec_br (d s) : exec (f + 1) (.br d :: is) s = .branch d s := id rfl
@[wasm_exec] theorem exec_brIf (d c) :
    exec (f + 1) (.brIf d :: is) ⟨.i32 c :: st, ls⟩ =
      if c ≠ 0 then .branch d ⟨st, ls⟩ else exec f is ⟨st, ls⟩ := id rfl
@[wasm_exec] theorem exec_ite (n t e c) :
    exec (f + 1) (.ite n t e :: is) ⟨.i32 c :: st, ls⟩ =
      exec f (.block n (if c ≠ 0 then t else e) :: is) ⟨st, ls⟩ := id rfl
@[wasm_exec] theorem exec_block (n body s) :
    exec (f + 1) (.block n body :: is) s =
      match exec f body ⟨[], s.locals⟩ with
      | .done s' | .branch 0 s' => exec f is ⟨s'.stack.take n ++ s.stack, s'.locals⟩
      | .branch (d + 1) s' => .branch d s'
      | o => o := id rfl
/-- Kept out of `wasm_exec`: `wasm_sim` unrolls loops, `wasm_step` leaves them for induction. -/
theorem exec_loop (n body s) :
    exec (f + 1) (.loop n body :: is) s =
      match exec f body ⟨[], s.locals⟩ with
      | .done s' => exec f is ⟨s'.stack.take n ++ s.stack, s'.locals⟩
      | .branch 0 s' => exec f (.loop n body :: is) ⟨s.stack, s'.locals⟩
      | .branch (d + 1) s' => .branch d s'
      | o => o := id rfl

@[wasm_exec] theorem exec_nop (s) : exec (f + 1) (.nop :: is) s = exec f is s := id rfl
@[wasm_exec] theorem exec_drop (v) : exec (f + 1) (.drop :: is) ⟨v :: st, ls⟩ = exec f is ⟨st, ls⟩ :=
  id rfl
@[wasm_exec] theorem exec_select (c v2 v1) :
    exec (f + 1) (.select :: is) ⟨.i32 c :: v2 :: v1 :: st, ls⟩ =
      exec f is ⟨(if c ≠ 0 then v1 else v2) :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_localGet (i) :
    exec (f + 1) (.localGet i :: is) ⟨st, ls⟩ =
      match ls[i]? with
      | some v => exec f is ⟨v :: st, ls⟩
      | none => .trap := by
  simp only [exec, step]; cases ls[i]? <;> rfl
@[wasm_exec] theorem exec_localSet (i v) :
    exec (f + 1) (.localSet i :: is) ⟨v :: st, ls⟩ =
      if i < ls.length then exec f is ⟨st, ls.set i v⟩ else .trap := by
  by_cases h : i < ls.length <;> simp [exec, step, setLocal, h]
@[wasm_exec] theorem exec_localTee (i v) :
    exec (f + 1) (.localTee i :: is) ⟨v :: st, ls⟩ =
      if i < ls.length then exec f is ⟨v :: st, ls.set i v⟩ else .trap := by
  by_cases h : i < ls.length <;> simp [exec, step, setLocal, h]
@[wasm_exec] theorem exec_i32Const (c) :
    exec (f + 1) (.i32Const c :: is) ⟨st, ls⟩ = exec f is ⟨.i32 c :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_i64Const (c) :
    exec (f + 1) (.i64Const c :: is) ⟨st, ls⟩ = exec f is ⟨.i64 c :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_i32Eqz (a) :
    exec (f + 1) (.i32Eqz :: is) ⟨.i32 a :: st, ls⟩ = exec f is ⟨ofBool (a == 0) :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_i32Bin (op b a) :
    exec (f + 1) (.i32Bin op :: is) ⟨.i32 b :: .i32 a :: st, ls⟩ =
      match binOp op a b with
      | some r => exec f is ⟨.i32 r :: st, ls⟩
      | none => .trap := by
  simp only [exec, step]; cases binOp op a b <;> rfl
@[wasm_exec] theorem exec_i64Bin (op b a) :
    exec (f + 1) (.i64Bin op :: is) ⟨.i64 b :: .i64 a :: st, ls⟩ =
      match binOp op a b with
      | some r => exec f is ⟨.i64 r :: st, ls⟩
      | none => .trap := by
  simp only [exec, step]; cases binOp op a b <;> rfl
@[wasm_exec] theorem exec_i32Rel (op b a) :
    exec (f + 1) (.i32Rel op :: is) ⟨.i32 b :: .i32 a :: st, ls⟩ =
      exec f is ⟨ofBool (relOp op a b) :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_i64Rel (op b a) :
    exec (f + 1) (.i64Rel op :: is) ⟨.i64 b :: .i64 a :: st, ls⟩ =
      exec f is ⟨ofBool (relOp op a b) :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_i32WrapI64 (a) :
    exec (f + 1) (.i32WrapI64 :: is) ⟨.i64 a :: st, ls⟩ = exec f is ⟨.i32 (a.setWidth 32) :: st, ls⟩ :=
  id rfl
@[wasm_exec] theorem exec_i64ExtendI32U (a) :
    exec (f + 1) (.i64ExtendI32U :: is) ⟨.i32 a :: st, ls⟩ =
      exec f is ⟨.i64 (a.setWidth 64) :: st, ls⟩ := id rfl
@[wasm_exec] theorem exec_i64ExtendI32S (a) :
    exec (f + 1) (.i64ExtendI32S :: is) ⟨.i32 a :: st, ls⟩ =
      exec f is ⟨.i64 (a.signExtend 64) :: st, ls⟩ := id rfl
end

/-- Unfold `Returns` for a function found by name: pick the function, then fuel. -/
theorem returns_of_invoke {m : Module} {name : String} {fn : Func} {args res : List Val}
    (hf : m.funcs.find? (·.name == name) = some fn) (h : ∃ fuel, invoke fn fuel args = some res) :
    Returns m name args res := ⟨fn, hf, h⟩

attribute [wasm_exec] invoke List.map_cons List.map_nil List.cons_append List.nil_append
  List.append_nil List.getElem?_cons_zero List.getElem?_cons_succ List.take_zero List.take_succ_cons
  List.take_nil List.length_cons List.length_nil List.set_cons_zero List.set_cons_succ
  List.reverse_cons List.reverse_nil ne_eq not_true_eq_false not_false_eq_true ite_true ite_false
  decide_true decide_false Option.map_some Option.map_none Nat.lt_irrefl Bool.false_eq_true

end FVA.Wasm

/-- Symbolically execute lifted code, unrolling loops while fuel lasts. -/
syntax "wasm_sim" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
/-- Symbolically execute lifted code, stopping at loop entries (for loop-invariant induction). -/
syntax "wasm_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wasm_sim) => `(tactic| simp only [wasm_exec, FVA.Wasm.exec_loop, Nat.reduceLT, Nat.reduceAdd])
  | `(tactic| wasm_sim [$ts,*]) =>
    `(tactic| simp only [$ts,*, wasm_exec, FVA.Wasm.exec_loop, Nat.reduceLT, Nat.reduceAdd])
  | `(tactic| wasm_step) => `(tactic| simp only [wasm_exec, Nat.reduceLT, Nat.reduceAdd])
  | `(tactic| wasm_step [$ts,*]) => `(tactic| simp only [$ts,*, wasm_exec, Nat.reduceLT, Nat.reduceAdd])
