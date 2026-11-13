import FVATest.Subjects.Lz4C.Sim
import FVATest.Subjects.Lz4C.SpecEq
import FVATest.Subjects.Lz4C.Instance
import FVA.Proof.Lib.Mem

/-!
# R1–R3 from the cutpoint statements (contract U20)

The prepared fresh instance (`store0` + the source and destination bytes), the export lookup and
the entry code lead to the main loop, which returns `Model.decode`'s verdict (`Sim.lean`): every
call returns one `i32`, reading and writing only R1's sets (R1), a valid block's decoded length
with its content (R2, `Model.decode_complete`), and a non-negative result only for a parsed block
(R3, `Model.decode_sound`). Conditional on `Entry`, `ShortcutS5`, `SegA`…`SegD` and `ErrRet`
(proof support; outside the review surface).
-/

namespace Subjects.Lz4C.Top

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Subjects.Lz4C

/-- Memory 0 of the fresh instance. -/
noncomputable def mem0 : MemInst := store0.mems.getD 0 ⟨0, none, fun _ => 0⟩

section
attribute [local irreducible] alloc

theorem store0_mem : store0.mems[0]? = some mem0 := by kernel_rfl
theorem mem0_size : mem0.size = 2097152 := by decide +kernel
theorem mem0_tables : TablesOK mem0 := by unfold TablesOK; decide +kernel
theorem inst_mem : alloc.2.mems[0]? = some 0 := by decide +kernel
theorem inst_export : alloc.2.exportFunc "LZ4_decompress_safe" = some 2 := by decide +kernel
theorem inst_f3 : alloc.2.funcs[3]? = some 3 := by decide +kernel
theorem inst_f4 : alloc.2.funcs[4]? = some 4 := by decide +kernel
theorem store0_f2 : store0.funcs[2]? = some (.wasm decType alloc.2 Lifted.func2) := by kernel_rfl
theorem store0_f3 : store0.funcs[3]? = some (.wasm copyType alloc.2 Lifted.func3) := by
  kernel_rfl
theorem store0_f4 : store0.funcs[4]? = some (.wasm copyType alloc.2 Lifted.func4) := by
  kernel_rfl

end

-- The kernel facts above carry the instance; elaboration below never unfolds its construction.
attribute [local irreducible] alloc initConfig store0 mem0

/-- The store after the caller wrote the source, then the destination bytes. -/
noncomputable def prepped (src dst : Nat) (input initDst : List UInt8) : Store :=
  (store0.withBytes src input).withBytes dst initDst

theorem prep_eq {src dst : Nat} {input initDst : List UInt8} (h1 : src + input.length ≤ 2097152)
    (h2 : dst + initDst.length ≤ 2097152) :
    store0.prep [.write src input, .write dst initDst] = some (prepped src dst input initDst) := by
  simp only [Store.prep, store0_mem, Store.withBytes_mem0 store0_mem, MemInst.withBytes_size,
    mem0_size, h1, h2, ↓reduceIte]
  rfl

theorem prepped_mem (src dst : Nat) (input initDst : List UInt8) :
    (prepped src dst input initDst).mems[0]? =
      some ((mem0.withBytes src input).withBytes dst initDst) :=
  Store.withBytes_mem0 (Store.withBytes_mem0 store0_mem _ _) _ _

theorem withBytes_low (mem : MemInst) {p a : Nat} (bs : List UInt8) (h : a < p) :
    (mem.withBytes p bs).byte a = mem.byte a := by
  simp only [MemInst.withBytes]
  exact ite_eq_right (by omega)

theorem good {src dst : Nat} {input initDst : List UInt8} (hs : 131072 ≤ src)
    (hs' : src + input.length ≤ 2097152) (hd : 131072 ≤ dst) (hd' : dst + initDst.length ≤ 2097152)
    (hj : src + input.length ≤ dst ∨ dst + initDst.length ≤ src) :
    Good (prepped src dst input initDst) alloc.2 0 src dst input.length initDst.length where
  a3 := ⟨3, inst_f3, store0_f3⟩
  a4 := ⟨4, inst_f4, store0_f4⟩
  ma0 := inst_mem
  mem := by
    refine ⟨_, prepped_mem src dst input initDst, mem0_size, mem0_tables.of_low fun a ha => ?_⟩
    rw [withBytes_low _ _ (by omega), withBytes_low _ _ (by omega)]
  srcLo := hs
  dstLo := hd
  srcHi := hs'
  dstHi := hd'
  disj := hj

/-- The source bytes stay held after the destination write (disjoint, or one of them empty). -/
theorem held_input {src dst : Nat} {input initDst : List UInt8}
    (hj : input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) :
    HoldsAt ((mem0.withBytes src input).withBytes dst initDst) src input := by
  intro i hi
  have hout : ¬ (dst ≤ src + i ∧ src + i < dst + initDst.length) := by
    rcases hj with rfl | rfl | h | h
    · simp at hi
    · simp
    · omega
    · omega
  simp only [MemInst.withBytes]
  rw [ite_eq_right hout, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-- From the invocation, every execution reaches func 2's return of `Model.decode`'s verdict,
inside R1's sets. -/
theorem call_verdict (hE : Entry) (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC)
    (hD : SegD) (hR : ErrRet) {H : HostSem} {src dst : Nat} {input initDst : List UInt8}
    (hs : 131072 ≤ src) (hs' : src + input.length ≤ 2097152) (hd : 131072 ≤ dst)
    (hd' : dst + initDst.length ≤ 2097152)
    (hj : input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) :
    Until H (Within (R1R src input.length dst initDst.length) (R1W dst initDst.length))
      (Verdict 0 dst (Model.decode input initDst.length))
      (invokeConfig (prepped src dst input initDst) 2
        [vI src, vI dst, vI input.length, vI initDst.length]) := by
  have hin := held_input hj
  have he := hE H (prepped src dst input initDst) alloc.2 2 0 _ src dst input.length
    initDst.length store0_f2 inst_mem (prepped_mem src dst input initDst) (by omega) (by omega)
    (by omega) (by omega) (fun _ => by simp only [MemInst.withBytes_size, mem0_size]; omega)
  refine Until.trans (untilR1 he (fun m a h => Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)))
    fun _ _ h => h.elim) ?_
  rintro c (⟨hcase, rfl⟩ | ⟨-, hc0, hn1, rfl⟩ | ⟨-, -, hc, hn, ls, hl, rfl⟩)
  · -- −1 before the main loop: no block decodes
    have hdec : Model.decode input initDst.length = none := by
      unfold Model.decode
      rcases hcase with h | h | ⟨h0, h1⟩ | ⟨h0, h1⟩
      · omega
      · omega
      · rw [ite_eq_left h0, ite_eq_right fun he => h1 (by rw [he]; rfl)]
      · rw [ite_eq_right h0, ite_eq_left (List.eq_nil_of_length_eq_zero h1)]
    rw [hdec]
    exact .done ⟨_, _, rfl, neg1⟩
  · -- no room: the one-byte block `0` decodes to nothing
    obtain ⟨b, rfl⟩ : ∃ b, input = [b] := by
      match input, hn1 with
      | [b], _ => exact ⟨b, rfl⟩
    have hb := hin 0 (by simp)
    simp only [Nat.add_zero] at hb
    rw [hb]
    have hroom : initDst.length = 0 := hc0
    by_cases h0 : b = 0
    · subst h0
      have hdec : Model.decode [0] initDst.length = some [] := by
        unfold Model.decode; rw [ite_eq_left hroom, ite_eq_left rfl]
      rw [hdec]
      refine .done ⟨_, _, rfl, rfl, _, prepped_mem src dst [0] initDst, ?_, fun i hi => ?_⟩
      · simp only [MemInst.withBytes_size, mem0_size, List.length_nil]; omega
      · simp at hi
    · have hdec : Model.decode [b] initDst.length = none := by
        unfold Model.decode
        rw [ite_eq_left hroom, ite_eq_right fun he => h0 (List.singleton_inj.mp he)]
      rw [hdec]
      refine .done ⟨prepped src dst [b] initDst, BitVec.ofNat 32 4294967295, ?_, neg1⟩
      rw [show ([b] : List UInt8)[0]! = b from rfl, ite_eq_right h0]; rfl
  · -- the main loop simulates `Model.loop` from the empty prefix
    have hj' : src + input.length ≤ dst ∨ dst + initDst.length ≤ src := by
      rcases hj with h | h | h
      · exact absurd (congrArg List.length h) hn
      · exact absurd (congrArg List.length h) hc
      · exact h
    have hdec : Model.decode input initDst.length =
        Model.loop input initDst.length input.length 0 [] := by
      unfold Model.decode
      rw [ite_eq_right hc, ite_eq_right fun he => hn (by rw [he]; rfl)]
    rw [hdec]
    exact loopSim hS5 hA hB hC hD hR _ 0 [] _ _ rfl (by omega)
      ⟨_, ls, _, good hs hs' hd hd' hj', by simpa using hl, prepped_mem src dst input initDst, hin,
        fun i hi => absurd hi (by simp), by omega, by simp, rfl⟩

theorem prepared_eq {H : HostSem} {src dst : Nat} {input initDst : List UInt8} {s : Store}
    {inst : ModuleInst} (h1 : src + input.length ≤ 2097152) (h2 : dst + initDst.length ≤ 2097152)
    (hp : Prepared Lifted.module H [.write src input, .write dst initDst] s inst) :
    s = prepped src dst input initDst ∧ inst = alloc.2 := by
  obtain ⟨s₀, hi, hp⟩ := hp
  obtain ⟨rfl, rfl⟩ := instance_eq hi
  exact ⟨Option.some.inj (hp.symm.trans (prep_eq h1 h2)), rfl⟩

/-- From `Until` to func 2's returns, the call's footprint and its results. -/
theorem returns_of_until {H : HostSem} {s : Store} {args : List Val} {R W : Nat → Nat → Prop}
    {X : Config → Prop} {P : Store → List Val → Prop}
    (hu : Until H (Within R W) X (invokeConfig s 2 args)) (hok : InvokeOK s 2 args)
    (hx : ∀ c, X c → ∃ st' vs, c = ⟨st', ⟨[], {}⟩, vals vs⟩ ∧ P st' vs) :
    CallWithin H s alloc.2 "LZ4_decompress_safe" args R W ∧
      CallReturns H s alloc.2 "LZ4_decompress_safe" args P := by
  refine ⟨⟨2, inst_export, hok, (mustW_of_until (Q := fun _ => True) hu ?_).2⟩,
    ⟨2, inst_export, hok, (mustW_of_until hu ?_).1⟩⟩
  · intro c hc
    obtain ⟨st', vs, rfl, -⟩ := hx c hc
    exact mustW_final (o := .returned st' vs) ⟨rfl, rfl⟩ trivial
  · intro c hc
    obtain ⟨st', vs, rfl, hp⟩ := hx c hc
    exact mustW_final (o := .returned st' vs) ⟨rfl, rfl⟩ hp

theorem invoke_ok (src dst : Nat) (input initDst : List UInt8) :
    InvokeOK (prepped src dst input initDst) 2
      [vI src, vI dst, vI input.length, vI initDst.length] :=
  ⟨_, _, store0_f2, rfl, .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))⟩

/-- R1 from the cutpoint statements. -/
theorem r1_of (hE : Entry) (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD)
    (hR : ErrRet) : r1Unfactored := by
  intro src dst input initDst hs hs' hd hd' _ _ hj
  refine ⟨fun H => ⟨_, _, store0, instance_store0 H, prep_eq hs' hd'⟩, ?_⟩
  intro H s inst hp
  obtain ⟨rfl, rfl⟩ := prepared_eq hs' hd' hp
  exact returns_of_until (call_verdict hE hS5 hA hB hC hD hR (H := H) hs hs' hd hd' hj)
    (invoke_ok src dst input initDst) fun c ⟨st', v, hc, _⟩ => ⟨st', _, hc, v, rfl⟩

/-- R2 from the cutpoint statements. -/
theorem r2_of (hE : Entry) (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD)
    (hR : ErrRet) : r2Unfactored := by
  intro src dst input initDst hs hs' hd hd' _ _ hj
  refine ⟨fun H => ⟨_, _, store0, instance_store0 H, prep_eq hs' hd'⟩, ?_⟩
  intro H s inst hp c hv hcl hroom
  obtain ⟨rfl, rfl⟩ := prepared_eq hs' hd' hp
  have hu := call_verdict hE hS5 hA hB hC hD hR (H := H) hs hs' hd hd' hj
  rw [Model.decode_complete hv hcl hroom (by omega)] at hu
  exact (returns_of_until hu (invoke_ok src dst input initDst)
    fun c ⟨st', v, hc, hv, mem, hm, hsz, hh⟩ => ⟨st', _, hc, by rw [hv], mem, hm, hsz, hh⟩).2

/-- R3 from the cutpoint statements. -/
theorem r3_of (hE : Entry) (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD)
    (hR : ErrRet) : r3Unfactored := by
  intro src dst input initDst hs hs' hd hd' _ _ hj
  refine ⟨fun H => ⟨_, _, store0, instance_store0 H, prep_eq hs' hd'⟩, ?_⟩
  intro H s inst hp
  obtain ⟨rfl, rfl⟩ := prepared_eq hs' hd' hp
  refine (returns_of_until (call_verdict hE hS5 hA hB hC hD hR (H := H) hs hs' hd hd' hj)
    (invoke_ok src dst input initDst) fun c hx => ?_).2
  obtain ⟨st', v, rfl, hv⟩ := hx
  refine ⟨st', _, rfl, v, rfl, fun h0 => ?_⟩
  cases hdec : Model.decode input initDst.length with
  | none => rw [hdec] at hv; omega
  | some content =>
    rw [hdec] at hv
    obtain ⟨rfl, mem, hm, hsz, hh⟩ := hv
    obtain ⟨hlen, ss, last, hpa, hd⟩ := Model.decode_sound hdec
    have ht : (BitVec.ofNat 32 content.length).toInt = content.length := ofNat_toInt (by omega)
    exact ⟨by rw [ht]; omega, ss, last, content, hpa, hd, by rw [ht]; simp, mem, hm, hsz, hh⟩

end Subjects.Lz4C.Top
