import FVA.Spec.Syntax

/-!
# Equality of the type family (verified implementation)

Lean derives no `DecidableEq` for the mutual nested family `HeapType`/`RefType`/`ValType`/
`FuncType`/`DefType` (A2, `docs/contracts/U28b-runtime.md` R1). Bool equality by structural
recursion (the kernel evaluates it, e.g. a `call_indirect` type check inside a proof) + its two
lemmas give the instances; their types are their correctness. The spec types embedding the family
derive theirs here, so `FVA/Spec` carries no equality instance for them.
-/

namespace FVA.Wasm

mutual
/-- Structural equality of heap types; defined types compare by group content + projection. -/
def HeapType.beq : HeapType → HeapType → Bool
  | .abs a, .abs b => a == b
  | .idx x, .idx y => x == y
  | .def_ d, .def_ e => DefType.beq d e
  | .rec_ i, .rec_ j => i == j
  | _, _ => false
  termination_by structural a _ => a
/-- Structural equality of reference types. -/
def RefType.beq : RefType → RefType → Bool
  | ⟨n, h⟩, ⟨m, k⟩ => n == m && HeapType.beq h k
  termination_by structural a _ => a
/-- Structural equality of value types. -/
def ValType.beq : ValType → ValType → Bool
  | .num a, .num b => a == b
  | .ref a, .ref b => RefType.beq a b
  | _, _ => false
  termination_by structural a _ => a
/-- Pointwise `ValType.beq`. -/
def ValType.beqs : List ValType → List ValType → Bool
  | [], [] => true
  | a :: as, b :: bs => ValType.beq a b && ValType.beqs as bs
  | _, _ => false
  termination_by structural a _ => a
/-- Structural equality of function types. -/
def FuncType.beq : FuncType → FuncType → Bool
  | ⟨p, r⟩, ⟨q, s⟩ => ValType.beqs p q && ValType.beqs r s
  termination_by structural a _ => a
/-- Pointwise `FuncType.beq`. -/
def FuncType.beqs : List FuncType → List FuncType → Bool
  | [], [] => true
  | a :: as, b :: bs => FuncType.beq a b && FuncType.beqs as bs
  | _, _ => false
  termination_by structural a _ => a
/-- Structural equality of defined types: same group, same projection. -/
def DefType.beq : DefType → DefType → Bool
  | ⟨g, i⟩, ⟨h, j⟩ => FuncType.beqs g h && i == j
  termination_by structural a _ => a
end

mutual
theorem HeapType.eq_of_beq : ∀ {a b : HeapType}, HeapType.beq a b = true → a = b
  | .abs a, .abs b, h => by simp_all [HeapType.beq]
  | .idx x, .idx y, h => by simp_all [HeapType.beq]
  | .def_ d, .def_ e, h => by rw [@DefType.eq_of_beq d e (by simpa [HeapType.beq] using h)]
  | .rec_ i, .rec_ j, h => by simp_all [HeapType.beq]
  | .abs _, .idx _, h | .abs _, .def_ _, h | .abs _, .rec_ _, h
  | .idx _, .abs _, h | .idx _, .def_ _, h | .idx _, .rec_ _, h
  | .def_ _, .abs _, h | .def_ _, .idx _, h | .def_ _, .rec_ _, h
  | .rec_ _, .abs _, h | .rec_ _, .idx _, h | .rec_ _, .def_ _, h => by simp [HeapType.beq] at h
theorem RefType.eq_of_beq : ∀ {a b : RefType}, RefType.beq a b = true → a = b
  | ⟨n, h₁⟩, ⟨m, k⟩, h => by
    simp only [RefType.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, HeapType.eq_of_beq h.2]
theorem ValType.eq_of_beq : ∀ {a b : ValType}, ValType.beq a b = true → a = b
  | .num a, .num b, h => by simp_all [ValType.beq]
  | .ref a, .ref b, h => by rw [@RefType.eq_of_beq a b (by simpa [ValType.beq] using h)]
  | .num _, .ref _, h | .ref _, .num _, h => by simp [ValType.beq] at h
theorem ValType.eq_of_beqs : ∀ {a b : List ValType}, ValType.beqs a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ValType.beqs, Bool.and_eq_true] at h
    rw [ValType.eq_of_beq h.1, ValType.eq_of_beqs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ValType.beqs] at h
theorem FuncType.eq_of_beq : ∀ {a b : FuncType}, FuncType.beq a b = true → a = b
  | ⟨p, r⟩, ⟨q, s⟩, h => by
    simp only [FuncType.beq, Bool.and_eq_true] at h
    rw [ValType.eq_of_beqs h.1, ValType.eq_of_beqs h.2]
theorem FuncType.eq_of_beqs : ∀ {a b : List FuncType}, FuncType.beqs a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [FuncType.beqs, Bool.and_eq_true] at h
    rw [FuncType.eq_of_beq h.1, FuncType.eq_of_beqs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [FuncType.beqs] at h
theorem DefType.eq_of_beq : ∀ {a b : DefType}, DefType.beq a b = true → a = b
  | ⟨g, i⟩, ⟨h, j⟩, e => by
    simp only [DefType.beq, Bool.and_eq_true, beq_iff_eq] at e
    rw [FuncType.eq_of_beqs e.1, e.2]
end

mutual
theorem HeapType.beq_refl : ∀ a : HeapType, HeapType.beq a a = true
  | .abs _ | .idx _ | .rec_ _ => by simp [HeapType.beq]
  | .def_ d => by simpa [HeapType.beq] using DefType.beq_refl d
theorem RefType.beq_refl : ∀ a : RefType, RefType.beq a a = true
  | ⟨_, h⟩ => by simpa [RefType.beq] using HeapType.beq_refl h
theorem ValType.beq_refl : ∀ a : ValType, ValType.beq a a = true
  | .num _ => by simp [ValType.beq]
  | .ref r => by simpa [ValType.beq] using RefType.beq_refl r
theorem ValType.beqs_refl : ∀ a : List ValType, ValType.beqs a a = true
  | [] => rfl
  | a :: as => by simp [ValType.beqs, ValType.beq_refl a, ValType.beqs_refl as]
theorem FuncType.beq_refl : ∀ a : FuncType, FuncType.beq a a = true
  | ⟨p, r⟩ => by simp [FuncType.beq, ValType.beqs_refl p, ValType.beqs_refl r]
theorem FuncType.beqs_refl : ∀ a : List FuncType, FuncType.beqs a a = true
  | [] => rfl
  | a :: as => by simp [FuncType.beqs, FuncType.beq_refl a, FuncType.beqs_refl as]
theorem DefType.beq_refl : ∀ a : DefType, DefType.beq a a = true
  | ⟨g, _⟩ => by simp [DefType.beq, FuncType.beqs_refl g]
end

/-- `DecidableEq` from a structural Bool equality and its two lemmas. -/
private abbrev decEqOf {α : Type} (beq : α → α → Bool) (eq_of : ∀ {a b}, beq a b = true → a = b)
    (refl : ∀ a, beq a a = true) : DecidableEq α := fun a b =>
  if h : beq a b then isTrue (eq_of h) else isFalse fun e => h (e ▸ refl a)

instance : DecidableEq HeapType := decEqOf HeapType.beq HeapType.eq_of_beq HeapType.beq_refl
instance : DecidableEq RefType := decEqOf RefType.beq RefType.eq_of_beq RefType.beq_refl
instance : DecidableEq ValType := decEqOf ValType.beq ValType.eq_of_beq ValType.beq_refl
instance : DecidableEq FuncType := decEqOf FuncType.beq FuncType.eq_of_beq FuncType.beq_refl
instance : DecidableEq DefType := decEqOf DefType.beq DefType.eq_of_beq DefType.beq_refl

deriving instance DecidableEq for TableType, GlobalType, BlockType, ImportDesc, Import

end FVA.Wasm
