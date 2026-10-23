import FVA.Proof.Valid.Store
import FVA.Proof.Exec.SoundLemmas

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- Nontrapping results have the declared output type; a trap admits any output stack. -/
def ResultTyped (s : Store) (r : Option Val) (ts : List OpType) : Prop :=
  ∀ v, r = some v → ∃ t, ts = [.val t] ∧ v.HasType s t

private theorem map_i32_typed (s : Store) (r : Option (BitVec 32)) :
    ResultTyped s (r.map .i32) [i32] := by
  intro v hv
  obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨_, rfl, trivial⟩

private theorem map_i64_typed (s : Store) (r : Option (BitVec 64)) :
    ResultTyped s (r.map .i64) [int .w64] := by
  intro v hv
  obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨_, rfl, trivial⟩

private theorem truncTo_typed (s : Store) (F : FloatFormat) (w : Width) (sx : Sx)
    (z : FVal) : ResultTyped s (truncTo F w.bits sx z) [int w] := by
  intro v hv
  cases w <;> cases sx <;> simp only [Width.bits, truncTo, Option.bind_eq_some_iff] at hv
  all_goals obtain ⟨b, _, hb⟩ := hv
  all_goals simp only [intVal, Option.some.injEq] at hb
  all_goals subst v; exact ⟨_, rfl, trivial⟩

private theorem truncSatTo_typed (s : Store) (F : FloatFormat) (w : Width) (sx : Sx)
    (z : FVal) : ResultTyped s (truncSatTo F w.bits sx z) [int w] := by
  intro v hv
  cases sx <;> cases w <;>
    simp only [truncSatTo, Width.bits, intVal, Option.some.injEq] at hv
  all_goals subst v; exact ⟨_, rfl, trivial⟩

set_option maxHeartbeats 1000000 in
theorem numResults_typed {s : Store} {C : Context} {i : Instr} {st : StackType}
    {args : List Val} {r : Option Val} (hi : InstrT C i st) (hr : r ∈ numResults i args) :
    ResultTyped s r st.outs := by
  fun_cases numResults i args <;>
    simp only [numResults, Set.mem_singleton_iff, Set.mem_image, Set.mem_empty_iff_false] at hr
  all_goals cases hi
  all_goals first | subst r | obtain ⟨z, _, rfl⟩ := hr
  all_goals first
    | exact map_i32_typed s _
    | exact map_i64_typed s _
    | exact truncTo_typed s _ .w32 _ _
    | exact truncTo_typed s _ .w64 _ _
    | exact truncSatTo_typed s _ .w32 _ _
    | exact truncSatTo_typed s _ .w64 _ _
    | intro v hv; cases hv; exact ⟨_, rfl, trivial⟩

set_option maxHeartbeats 1000000 in
theorem numResults_arity {C : Context} {i : Instr} {st : StackType}
    {args : List Val} {r : Option Val} (hi : InstrT C i st) (hr : r ∈ numResults i args) :
    args.length = st.ins.length := by
  fun_cases numResults i args <;> simp only [numResults, Set.mem_empty_iff_false] at hr
  all_goals (cases hi; rfl)

theorem ResultTyped.output {s : Store} {C : Context} {r : Option Val} {ts : List OpType}
    (h : ResultTyped s r ts) : ASeqT s C (numOut r) ⟨[], ts⟩ := by
  cases r with
  | none => exact .single .trap
  | some v =>
    obtain ⟨t, rfl, hv⟩ := h v rfl
    exact .single (.value hv)

/-- Runtime operands inhabit concrete types; bottom has no runtime inhabitant. -/
def HasOpType (s : Store) (v : Val) : OpType → Prop
  | .val t => v.HasType s t
  | .bot => False

@[simp] theorem hasOp_i32 {s : Store} {v : Val} :
    HasOpType s v (int .w32) ↔ ∃ b, v = .i32 b := by
  cases v <;> simp [HasOpType, Val.HasType, Width.int]

@[simp] theorem hasOp_i64 {s : Store} {v : Val} :
    HasOpType s v (int .w64) ↔ ∃ b, v = .i64 b := by
  cases v <;> simp [HasOpType, Val.HasType, Width.int]

@[simp] theorem hasOp_f32 {s : Store} {v : Val} :
    HasOpType s v (flt .w32) ↔ ∃ b, v = .f32 b := by
  cases v <;> simp [HasOpType, Val.HasType, Width.float]

@[simp] theorem hasOp_f64 {s : Store} {v : Val} :
    HasOpType s v (flt .w64) ↔ ∃ b, v = .f64 b := by
  cases v <;> simp [HasOpType, Val.HasType, Width.float]

private theorem unary_int {s : Store} {w : Width} {vs : List Val}
    (h : List.Forall₂ (HasOpType s) vs [int w]) :
    ∃ b : BitVec w.bits, vs = [w.int.val b.toNat] := by
  cases w <;> simp only [List.forall₂_cons_right_iff, List.forall₂_nil_right_iff,
    hasOp_i32, hasOp_i64] at h
  all_goals obtain ⟨v, rest, ⟨b, rfl⟩, rfl, rfl⟩ := h
  all_goals
    refine ⟨b, ?_⟩
    simp only [Width.int, NumType.val, List.singleton_inj, Val.i32.injEq, Val.i64.injEq]
    exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt b.isLt).symm

private theorem unary_float {s : Store} {w : Width} {vs : List Val}
    (h : List.Forall₂ (HasOpType s) vs [flt w]) :
    ∃ b : BitVec w.bits, vs = [w.float.val b.toNat] := by
  cases w <;> simp only [List.forall₂_cons_right_iff, List.forall₂_nil_right_iff,
    hasOp_f32, hasOp_f64] at h
  all_goals obtain ⟨v, rest, ⟨b, rfl⟩, rfl, rfl⟩ := h
  all_goals
    refine ⟨b, ?_⟩
    simp only [Width.float, NumType.val, List.singleton_inj, Val.f32.injEq, Val.f64.injEq]
    exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt b.isLt).symm

private theorem binary_int {s : Store} {w : Width} {vs : List Val}
    (h : List.Forall₂ (HasOpType s) vs [int w, int w]) :
    ∃ a b : BitVec w.bits, vs = [w.int.val a.toNat, w.int.val b.toNat] := by
  cases w <;> simp only [List.forall₂_cons_right_iff, List.forall₂_nil_right_iff,
    hasOp_i32, hasOp_i64] at h
  all_goals obtain ⟨v, rest, ⟨a, rfl⟩, ⟨v', rest', ⟨b, rfl⟩, rfl, rfl⟩, rfl⟩ := h
  all_goals
    refine ⟨a, b, ?_⟩
    simp only [Width.int, NumType.val, List.cons.injEq, Val.i32.injEq, Val.i64.injEq,
      and_true]
    exact ⟨BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt a.isLt).symm,
      BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt b.isLt).symm⟩

private theorem binary_float {s : Store} {w : Width} {vs : List Val}
    (h : List.Forall₂ (HasOpType s) vs [flt w, flt w]) :
    ∃ a b : BitVec w.bits, vs = [w.float.val a.toNat, w.float.val b.toNat] := by
  cases w <;> simp only [List.forall₂_cons_right_iff, List.forall₂_nil_right_iff,
    hasOp_f32, hasOp_f64] at h
  all_goals obtain ⟨v, rest, ⟨a, rfl⟩, ⟨v', rest', ⟨b, rfl⟩, rfl, rfl⟩, rfl⟩ := h
  all_goals
    refine ⟨a, b, ?_⟩
    simp only [Width.float, NumType.val, List.cons.injEq, Val.f32.injEq, Val.f64.injEq,
      and_true]
    exact ⟨BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt a.isLt).symm,
      BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt b.isLt).symm⟩

/-- Operators whose progress follows from `numResults_nonempty`. -/
def Numeric : Instr → Prop
  | .iunop .. | .ibinop .. | .itestEqz .. | .irelop .. | .funop .. | .fbinop ..
  | .frelop .. | .cvtop .. => True
  | _ => False

set_option maxHeartbeats 1000000 in
theorem numStep_exists {s : Store} {C : Context} {i : Instr} {st : StackType}
    {args : List Val} (hi : InstrT C i st) (hn : Numeric i)
    (ha : List.Forall₂ (HasOpType s) args st.ins) : ∃ r, Ref.numStep i args = some r := by
  cases hi <;> simp only [Numeric] at hn
  case iunop w op legal =>
    obtain ⟨b, rfl⟩ := unary_int ha
    cases w <;> exact ⟨_, rfl⟩
  case ibinop w op =>
    obtain ⟨a, b, rfl⟩ := binary_int ha
    cases w <;> exact ⟨_, rfl⟩
  case itestEqz w =>
    obtain ⟨b, rfl⟩ := unary_int ha
    cases w <;> exact ⟨_, rfl⟩
  case irelop w op =>
    obtain ⟨a, b, rfl⟩ := binary_int ha
    cases w <;> exact ⟨_, rfl⟩
  case funop w op =>
    obtain ⟨b, rfl⟩ := unary_float ha
    cases w <;> exact ⟨_, rfl⟩
  case fbinop w op =>
    obtain ⟨a, b, rfl⟩ := binary_float ha
    cases w <;> exact ⟨_, rfl⟩
  case frelop w op =>
    obtain ⟨a, b, rfl⟩ := binary_float ha
    cases w <;> exact ⟨_, rfl⟩
  case cvtop op =>
    cases op with
    | wrap => obtain ⟨b, rfl⟩ := unary_int (w := .w64) ha; exact ⟨_, rfl⟩
    | extend sx =>
      obtain ⟨b, rfl⟩ := unary_int (w := .w32) ha
      cases sx <;> exact ⟨_, rfl⟩
    | trunc dst src sx | truncSat dst src sx =>
      obtain ⟨b, rfl⟩ := unary_float ha
      cases dst <;> cases src <;> exact ⟨_, rfl⟩
    | convert dst src sx =>
      obtain ⟨b, rfl⟩ := unary_int ha
      cases dst <;> cases src <;> exact ⟨_, rfl⟩
    | demote => obtain ⟨b, rfl⟩ := unary_float (w := .w64) ha; exact ⟨_, rfl⟩
    | promote => obtain ⟨b, rfl⟩ := unary_float (w := .w32) ha; exact ⟨_, rfl⟩
    | reinterpret w toInt =>
      cases toInt with
      | false => obtain ⟨b, rfl⟩ := unary_int ha; cases w <;> exact ⟨_, rfl⟩
      | true => obtain ⟨b, rfl⟩ := unary_float ha; cases w <;> exact ⟨_, rfl⟩

theorem numResults_nonempty {s : Store} {C : Context} {i : Instr} {st : StackType}
    {args : List Val} (hi : InstrT C i st) (hn : Numeric i)
    (ha : List.Forall₂ (HasOpType s) args st.ins) : (numResults i args).Nonempty := by
  obtain ⟨r, hr⟩ := numStep_exists hi hn ha
  exact ⟨r, Ref.numStep_mem hr⟩

end FVA.Wasm.Valid
