import FVA.Impl.Cert.Compile
import FVA.Proof.Cert.Sort
import FVA.Proof.Decode.Module
import FVA.Proof.Decode.Pack
import FVA.Proof.Lib.Instance
import FVA.Proof.Lib.Arith

/-! The `Compiled` checker is sound (contract U9 C2). -/

namespace FVA.Cert

open FVA.Wasm FVA.Wasm.Binary FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

namespace Impl

theorem arithText_eq (e : Arith) : arithText e = e.text := by
  induction e with
  | x => rfl
  | const k =>
    cases k with
    | zero => rfl
    | succ k => simp only [arithText, Arith.text, digitsOf_eq _ _ [] (lt_ten_pow_succ _),
        List.append_nil]
  | add a b iha ihb => simp [arithText, Arith.text, iha, ihb]
  | sub a b iha ihb => simp [arithText, Arith.text, iha, ihb]
  | mul a b iha ihb => simp [arithText, Arith.text, iha, ihb]

theorem arithEq_eval {a b : Arith} (h : arithEq a b = true) (v : BitVec 32) :
    a.eval v = b.eval v := by
  induction a generalizing b with
  | x => cases b <;> simp_all [arithEq, Arith.eval]
  | const n =>
    cases b <;> simp_all [arithEq, Arith.eval]
    apply BitVec.eq_of_toNat_eq
    simpa using h
  | add a b iha ihb =>
    cases b <;> simp_all [arithEq, Arith.eval]
    rw [iha h.1, ihb h.2]
  | sub a b iha ihb =>
    cases b <;> simp_all [arithEq, Arith.eval]
    rw [iha h.1, ihb h.2]
  | mul a b iha ihb =>
    cases b <;> simp_all [arithEq, Arith.eval]
    rw [iha h.1, ihb h.2]

/-- A canonical numeral packs exactly its `leBytes`. -/
theorem pack_leBytes {n v : Nat} (h : v < 2 ^ (8 * n)) : pack (leBytes n v) = v := by
  induction n generalizing v with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    have hv : v / 256 < 2 ^ (8 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      calc v < 2 ^ (8 * (n + 1)) := h
        _ = 2 ^ (8 * n) * 256 := by rw [Nat.mul_succ, pow_add]; norm_num
    simp only [leBytes, pack, ih hv]
    have : ((v % 256).toUInt8).toNat = v % 256 := by simp
    rw [this]; omega

theorem leBytes_length (n v : Nat) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih]

/-- The decoded module of `toyBody` is `toyModule` of its body. -/
theorem toyBody_eq {m : Module} {body : List Instr} (h : toyBody m = some body) :
    m = toyModule body := by
  unfold toyBody at h
  split at h
  · rename_i f hf
    cases hb : (decide (m.types = [⟨[.num .i32], [.num .i32]⟩]) && Nat.beq f.type 0 &&
        f.locals.isEmpty && m.tables.isEmpty && m.mems.isEmpty && m.globals.isEmpty &&
        m.elems.isEmpty && m.datas.isEmpty && m.start.isNone && m.imports.isEmpty &&
        decide (m.exports = [⟨"f", .func 0⟩]))
    · rw [hb] at h; cases h
    · rw [hb, Bool.cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, Option.isNone_iff_eq_none,
        Nat.beq_eq] at hb
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, hty⟩, hl⟩, htab⟩, hmem⟩, hg⟩, he⟩, hd⟩, hs⟩, hi⟩, hx⟩ := hb
      obtain ⟨types, funcs, tables, mems, globals, elems, datas, start, imports, exports⟩ := m
      obtain ⟨fty, flocals, fbody⟩ := f
      simp only at hf ht hty hl htab hmem hg he hd hs hi hx
      subst hf ht hty hl htab hmem hg he hd hs hi hx
      rfl
  · cases h

/-- The function's frame while a toy body runs: the stack values (bottom first), then the rest of
the body. -/
def bodyConfig (s : Store) (inst : ModuleInst) (x : BitVec 32) (stack : List (BitVec 32))
    (rest : List Instr) : Config :=
  ⟨s, ⟨[], {}⟩, [.frame 1 ⟨[.i32 x], inst⟩
    [.label 1 [] (vals (stack.map Val.i32) ++ rest.map .plain)]]⟩

theorem straight_line (H : HostSem) (s : Store) (inst : ModuleInst) (x : BitVec 32) :
    ∀ (body : List Instr) (st : List Arith) (t : Arith),
      toyHeight body st.length = some 1 → symRun body st = some [t] →
      Must H (fun | .returned _ vs => vs = [.i32 (t.eval x)] | .trapped _ => False)
        (bodyConfig s inst x (st.reverse.map fun a => a.eval x) body) := by
  intro body
  induction body with
  | nil =>
    intro st t hh hs
    simp only [symRun, Option.some.injEq] at hs
    subst hs
    unfold bodyConfig
    wasm_run []
    exact Must.done (o := .returned s [.i32 (t.eval x)]) ⟨rfl, rfl⟩ rfl
  | cons i rest ih =>
    intro st t hh hs
    cases i
    case localGet k =>
      cases k with
      | succ k => simp [toyHeight] at hh
      | zero =>
        simp only [symRun] at hs
        simp only [toyHeight] at hh
        unfold bodyConfig
        wasm_step1 [seq_vals, seqUnique_vals]
        have h' := ih (.x :: st) t (by simpa using hh) hs
        simp only [bodyConfig, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          vals, List.append_assoc, List.singleton_append, List.reverse_reverse,
          Arith.eval] at h' ⊢
        exact h'
    case iconst w n =>
      cases w
      case w64 => simp [toyHeight] at hh
      case w32 =>
        simp only [symRun] at hs
        by_cases hn : n < 2 ^ 32
        · simp only [toyHeight, hn, ite_true] at hh
          have h' := ih (.const n :: st) t (by simpa using hh) hs
          have hv : (Val.i32 (BitVec.ofNat 32 n)).instr = .plain (.iconst .w32 n) := by
            have hn' : n < 4294967296 := hn
            simp [Val.instr, Nat.mod_eq_of_lt hn']
          simp only [bodyConfig, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
            vals, List.append_assoc, List.singleton_append, Arith.eval, hv] at h' ⊢
          exact h'
        · simp only [toyHeight] at hh
          split at hh
          · omega
          · cases hh
    case ibinop w op =>
      cases w
      case w64 => simp [toyHeight] at hh
      case w32 =>
        cases op
        case add =>
          match st, hs, hh with
          | b :: a :: st', hs, hh =>
            simp only [symRun] at hs
            simp only [toyHeight, List.length_cons] at hh
            have h' := ih (.add a b :: st') t (by simpa using hh) hs
            simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.singleton_append]
            unfold bodyConfig
            simp only [List.map_append, List.map_cons, List.map_nil]
            wasm_step1 [seq_vals, seqUnique_vals, List.reverse_append]
            simp only [bodyConfig, List.reverse_cons, List.map_append, List.map_cons,
              List.map_nil, vals, List.append_assoc, List.singleton_append, List.reverse_reverse,
              Arith.eval, iadd_eq] at h' ⊢
            exact h'
          | [], hs, _ => simp [symRun] at hs
          | [_], hs, _ => simp [symRun] at hs
        case sub =>
          match st, hs, hh with
          | b :: a :: st', hs, hh =>
            simp only [symRun] at hs
            simp only [toyHeight, List.length_cons] at hh
            have h' := ih (.sub a b :: st') t (by simpa using hh) hs
            simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.singleton_append]
            unfold bodyConfig
            simp only [List.map_append, List.map_cons, List.map_nil]
            wasm_step1 [seq_vals, seqUnique_vals, List.reverse_append]
            simp only [bodyConfig, List.reverse_cons, List.map_append, List.map_cons,
              List.map_nil, vals, List.append_assoc, List.singleton_append, List.reverse_reverse,
              Arith.eval, isub_eq] at h' ⊢
            exact h'
          | [], hs, _ => simp [symRun] at hs
          | [_], hs, _ => simp [symRun] at hs
        case mul =>
          match st, hs, hh with
          | b :: a :: st', hs, hh =>
            simp only [symRun] at hs
            simp only [toyHeight, List.length_cons] at hh
            have h' := ih (.mul a b :: st') t (by simpa using hh) hs
            simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.singleton_append]
            unfold bodyConfig
            simp only [List.map_append, List.map_cons, List.map_nil]
            wasm_step1 [seq_vals, seqUnique_vals, List.reverse_append]
            simp only [bodyConfig, List.reverse_cons, List.map_append, List.map_cons,
              List.map_nil, vals, List.append_assoc, List.singleton_append, List.reverse_reverse,
              Arith.eval, imul_eq] at h' ⊢
            exact h'
          | [], hs, _ => simp [symRun] at hs
          | [_], hs, _ => simp [symRun] at hs
        all_goals simp [toyHeight] at hh
    all_goals simp [toyHeight] at hh

/-- A valid toy body whose symbolic run ends with `t` makes `f` return `t`'s value. -/
theorem toy_returns (body : List Instr) (t : Arith) (hv : ToyValid body)
    (hr : symRun body [] = some [t]) (x : BitVec 32) :
    Returns (toyModule body) "f" [.i32 x] [.i32 (t.eval x)] := by
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[0]? = some (.wasm ⟨[.num .i32], [.num .i32]⟩ inst ⟨0, [], body⟩) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "f" = some 0 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨0, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  unfold invokeConfig
  wasm_step1 [hf]
  have := straight_line H s inst x body [] t (by simpa [ToyValid] using hv) hr
  simp only [bodyConfig, List.reverse_nil, List.map_nil, vals, List.nil_append] at this
  refine this.mono ?_
  rintro (_ | _) hq <;> exact hq

end Impl

open Impl in
theorem Compiled.check_sound (i o : Blob) (h : Compiled.check i o = true) :
    Accepted Compiled i o := by
  unfold Compiled.check at h
  split at h
  · rename_i e _ _ _
    split at h
    · rename_i v' ht
      obtain ⟨_, hi⟩ := takeBytes_sound ht
      cases hc : Nat.blt o.bytes (2 ^ (8 * o.len))
      · rw [hc, Bool.cond_false] at h; cases h
      · rw [hc, Bool.cond_true] at h
        split at h
        · rename_i m hd
          split at h
          · rename_i body hb
            cases hv : decide (toyHeight body 0 = some 1)
            · rw [hv, Bool.cond_false] at h; cases h
            · rw [hv, Bool.cond_true] at h
              split at h
              · rename_i t hr
                have hcan : o.bytes < 2 ^ (8 * o.len) := Nat.blt_eq.mp hc
                have hmb : ModuleB m o.data := by
                  apply FVA.Wasm.Decode.decode_sound
                  rw [Blob.data, pack_leBytes hcan, leBytes_length]
                  exact hd
                have hvalid : ToyValid body := (of_decide_eq_true hv : toyHeight body 0 = some 1)
                refine ⟨e, body, ?_, toyBody_eq hb ▸ hmb, hvalid, fun x => ?_⟩
                · rw [Blob.data, hi]
                  simp [arithText_eq, leBytes]
                · rw [← arithEq_eval h x]
                  exact toy_returns body t hvalid hr x
              · cases h
          · cases h
        · cases h
    · cases h
  · cases h

end FVA.Cert
