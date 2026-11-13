import FVATest.Subjects.Lz4C.Seg
import FVATest.Subjects.Lz4C.ExtCommon
import Mathlib.Tactic.IntervalCases

/-! The main loop's 19 locals as one explicit list (`cLocals`) and the join points' packaging
(`c_atX4`, `c_err`, `cOuter`), shared by engine C's segment proofs `SegB`, `SegC`, `SegD`. -/

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

def cLocals (src dst n cap o' off : Nat) (v3 : Option Val) (v4 : Val) (acc : Nat)
    (v16 : Option Val) : List (Option Val) :=
  [some (vI src), some (vI dst), some (.i32 (BitVec.ofNat 32 o' - BitVec.ofNat 32 off)), v3,
    some v4, some (vI (dst + cap)), some (vI (dst + cap - 32)), some (vI (src + n)),
    some (vI (src + n - 16)), some (vI (dst + cap - 5)), some (vI (dst + cap - 7)),
    some (vI (src + n - 4)), some (vI (src + n - 8)), some (vI (dst + cap - 12)),
    some (vI (src + n - 15)), some (vI acc), v16, some (vI o'), some (vI off)]

theorem c_const (src dst n cap o' off : Nat) (v3 : Option Val) (v4 : Val) (acc : Nat)
    (v16 : Option Val) :
    ConstLocals (cLocals src dst n cap o' off v3 v4 acc v16) src dst n cap := by
  simp [ConstLocals, cLocals]

theorem c_decompose {ls : List (Option Val)} {src dst n cap o' off ml j : Nat}
    (h : ConstLocals ls src dst n cap) (h4 : ls[4]? = some (some (vI j)))
    (h15 : ls[15]? = some (some (vI ml))) (h17 : ls[17]? = some (some (vI o')))
    (h18 : ls[18]? = some (some (vI off)))
    (h2 : ls[2]? = some (some (.i32 (BitVec.ofNat 32 o' - BitVec.ofNat 32 off)))) :
    ∃ v3 v16, ls = cLocals src dst n cap o' off v3 (vI j) ml v16 := by
  rcases h with ⟨hlen, h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have get (i : Nat) (hi : i < 19) : ls[i]? = some (ls[i]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  refine ⟨ls[3]'(by omega), ls[16]'(by omega), List.ext_getElem? (fun i => ?_)⟩
  by_cases hi : i < 19
  · interval_cases i <;> simp_all only [cLocals, List.getElem?_cons_zero,
      List.getElem?_cons_succ, get 3 (by decide), get 16 (by decide)]
  · rw [List.getElem?_eq_none (by omega)]
    symm
    exact List.getElem?_eq_none (by simp [cLocals]; omega)

theorem c_atX4 (F : Context) (st : Store) (inst : ModuleInst) (src dst n cap o' off : Nat)
    (v3 : Option Val) (j acc : Nat) (v16 : Option Val) :
    AtX4 F st inst src dst n cap o' off acc j
      ((ctx5 (ctx2 F)).fill ⟨st, ⟨cLocals src dst n cap o' off v3 (vI j) acc v16, inst⟩,
        (body5.drop 5).map .plain⟩) := by
  refine ⟨_, c_const _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> rfl

theorem c_err (F : Context) (st : Store) (inst : ModuleInst) (src dst n cap o' off : Nat)
    (v3 : Option Val) (j acc : Nat) (v16 : Option Val) (hlo : src ≤ j) (hhi : j ≤ src + n + 1) :
    Err F st inst src dst n cap
      ((ctx1 F).fill ⟨st, ⟨cLocals src dst n cap o' off v3 (vI j) acc v16, inst⟩,
        (body1.drop 54).map .plain⟩) := by
  exact ⟨j, hlo, hhi, _, c_const _ _ _ _ _ _ _ _ _ _, rfl, rfl⟩

noncomputable def cOuter (es : List AInstr) : List AInstr :=
  [.label 0 [] (.label 0 [] (.label 0 [] (.label 0 [mainLoop]
    (.label 0 [] es :: (body5.drop 5).map .plain) :: (body4.drop 1).map .plain) ::
      (body3.drop 1).map .plain) :: (body2.drop 1).map .plain)] ++ (body1.drop 54).map .plain

end Subjects.Lz4C.Eval
