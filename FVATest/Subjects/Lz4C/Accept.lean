import FVATest.Subjects.Lz4C.Spec
import FVATest.Subjects.Lz4C.Instance
import FVA.Proof.Lib.Footprint

/-! # Kernel-evaluated consistency instances for the blind R1–R3 statements

These runs observe only the lifted artifact. They are witnesses, not the universal proofs.
Proof-side fixtures and helper propositions stay here, outside `Spec`'s review surface.
-/

namespace Subjects.Lz4C.Accept

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

-- Keep the 8 KiB module and initialized memory out of elaborator conversion; the kernel still
-- evaluates them for every concrete run fact.
attribute [local irreducible] alloc initConfig store0

structure Fixture where
  src : Nat := 131072
  dst : Nat := 196608
  input : List UInt8
  initDst : List UInt8

def Fixture.prep (f : Fixture) : List Prep := [.write f.src f.input, .write f.dst f.initDst]

def Fixture.args (f : Fixture) : List Val :=
  [.i32 (BitVec.ofNat 32 f.src), .i32 (BitVec.ofNat 32 f.dst),
    .i32 (BitVec.ofNat 32 f.input.length), .i32 (BitVec.ofNat 32 f.initDst.length)]

noncomputable def Fixture.store (f : Fixture) : Store := (store0.prep f.prep).getD {}

noncomputable def Fixture.config (f : Fixture) : Config := invokeConfig f.store 2 f.args

theorem Fixture.prep_eq (f : Fixture) (hs : (store0.prep f.prep).isSome) :
    store0.prep f.prep = some f.store := by
  cases hp : store0.prep f.prep with
  | none => simp [hp] at hs
  | some s => simp only [Fixture.store, hp, Option.getD_some]

theorem Fixture.prepared (f : Fixture) (hs : (store0.prep f.prep).isSome) (H : HostSem) :
    Prepared Lifted.module H f.prep f.store alloc.2 :=
  ⟨store0, instance_store0 H, f.prep_eq hs⟩

theorem Fixture.prepared_eq (f : Fixture) (hs : (store0.prep f.prep).isSome)
    {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H f.prep s inst) : s = f.store ∧ inst = alloc.2 := by
  obtain ⟨s₀, hi, hprep⟩ := hp
  obtain ⟨rfl, rfl⟩ := instance_eq hi
  exact ⟨Option.some.inj (hprep.symm.trans (f.prep_eq hs)), rfl⟩

theorem Fixture.returns (f : Fixture) {n : Nat} {vs : List Val}
    (hs : (store0.prep f.prep).isSome)
    (hi : InvokeOK f.store 2 f.args)
    (hr : (runDet n f.config).isSome)
    (hv : ((runDet n f.config).get hr).instrs = vals vs)
    {P : Store → List Val → Prop} (hp : P ((runDet n f.config).get hr).store vs)
    {H : HostSem} {s : Store} {inst : ModuleInst}
    (hprep : Prepared Lifted.module H f.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" f.args (fun s' ws => ws = vs ∧ P s' ws) := by
  obtain ⟨rfl, rfl⟩ := f.prepared_eq hs hprep
  refine ⟨2, ?_, hi, must_returned_of_runDet_get hr hv hp⟩
  decide +kernel

/-- One literal, with spare destination capacity; destination bytes are initially nonzero. -/
def literal : Fixture := { input := [0x10, 0x61], initDst := [0xCC, 0xCC, 0xCC, 0xCC, 0xCC] }

/-- The format's empty block, with a zero-capacity destination inside the input's range. -/
def empty : Fixture := { dst := 131072, input := [0x00], initDst := [] }

/-- Eight repeated bytes, then five final literals: a valid independent match block. -/
def matched : Fixture :=
  { input := [0x13, 0x61, 0x01, 0x00, 0x50, 0x62, 0x63, 0x64, 0x65, 0x66],
    initDst := List.replicate 13 0xCC }

def matchSeq : Lz4.Seq := ⟨[0x61], 1, 7⟩
def matchLast : List UInt8 := [0x62, 0x63, 0x64, 0x65, 0x66]
def matchContent : List UInt8 := List.replicate 8 0x61 ++ matchLast

/-- A token asking for one missing literal; the decoder must return an error, not trap. -/
def malformed : Fixture := { input := [0x10], initDst := [0xCC] }

theorem literal_valid : Lz4.Valid literal.input [0x61] :=
  ⟨[], [0x61], ⟨0, by decide, by decide, by simp⟩, rfl, by simp [Lz4.EndOk]⟩

theorem empty_valid : Lz4.Valid empty.input [] :=
  ⟨[], [], ⟨0, by decide, by decide, by simp⟩, rfl, by simp [Lz4.EndOk]⟩

theorem matched_valid : Lz4.Valid matched.input matchContent := by
  refine ⟨[matchSeq], matchLast, ⟨0, by decide, by decide, ?_⟩, by decide, ?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    decide
  · simp [Lz4.EndOk, matchSeq, matchLast]

theorem literal_prep : (store0.prep literal.prep).isSome := by decide +kernel
theorem empty_prep : (store0.prep empty.prep).isSome := by decide +kernel
theorem matched_prep : (store0.prep matched.prep).isSome := by decide +kernel
theorem malformed_prep : (store0.prep malformed.prep).isSome := by decide +kernel

theorem literal_invoke : InvokeOK literal.store 2 literal.args := by
  refine ⟨.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩
    alloc.2 Lifted.func2, ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩,
    by kernel_rfl, rfl, ?_⟩
  exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))

theorem empty_invoke : InvokeOK empty.store 2 empty.args := by
  refine ⟨.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩
    alloc.2 Lifted.func2, ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩,
    by kernel_rfl, rfl, ?_⟩
  exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))

theorem matched_invoke : InvokeOK matched.store 2 matched.args := by
  refine ⟨.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩
    alloc.2 Lifted.func2, ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩,
    by kernel_rfl, rfl, ?_⟩
  exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))

theorem malformed_invoke : InvokeOK malformed.store 2 malformed.args := by
  refine ⟨.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩
    alloc.2 Lifted.func2, ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩,
    by kernel_rfl, rfl, ?_⟩
  exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))

theorem literal_run : (runDet 1000 literal.config).isSome := by decide +kernel
theorem empty_run : (runDet 1000 empty.config).isSome := by decide +kernel
theorem matched_run : (runDet 3000 matched.config).isSome := by decide +kernel
theorem malformed_run : (runDet 1000 malformed.config).isSome := by decide +kernel

noncomputable def literalFinal : Config := (runDet 1000 literal.config).get literal_run
noncomputable def emptyFinal : Config := (runDet 1000 empty.config).get empty_run
noncomputable def matchedFinal : Config := (runDet 3000 matched.config).get matched_run
noncomputable def malformedFinal : Config := (runDet 1000 malformed.config).get malformed_run

theorem literal_result : literalFinal.instrs = vals [.i32 1] := by kernel_rfl
theorem empty_result : emptyFinal.instrs = vals [.i32 0] := by kernel_rfl
theorem matched_result : matchedFinal.instrs = vals [.i32 13] := by kernel_rfl
theorem malformed_result : malformedFinal.instrs = vals [.i32 (-2)] := by kernel_rfl

noncomputable def literalMem : MemInst :=
  (literalFinal.store.mems[0]?).getD { pages := 0, max := none, byte := fun _ => 0 }
noncomputable def emptyMem : MemInst :=
  (emptyFinal.store.mems[0]?).getD { pages := 0, max := none, byte := fun _ => 0 }
noncomputable def matchedMem : MemInst :=
  (matchedFinal.store.mems[0]?).getD { pages := 0, max := none, byte := fun _ => 0 }

theorem literal_holds : Holds literalFinal.store literal.dst [0x61] :=
  ⟨literalMem, by kernel_rfl, by decide +kernel, by decide +kernel⟩

theorem empty_holds : Holds emptyFinal.store empty.dst [] :=
  ⟨emptyMem, by kernel_rfl, by decide +kernel, by decide +kernel⟩

theorem matched_holds : Holds matchedFinal.store matched.dst matchContent :=
  ⟨matchedMem, by kernel_rfl, by decide +kernel, by decide +kernel⟩

/-- R2's conclusion, kernel-evaluated on the shipped bytes: one literal, room 5. -/
theorem literal_r2 {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H literal.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" literal.args
      (fun s' vs => vs = [.i32 1] ∧ Holds s' literal.dst [0x61]) :=
  literal.returns literal_prep literal_invoke literal_run literal_result literal_holds hp

/-- R2's zero-capacity exception, including an empty destination at the input address. -/
theorem empty_r2 {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H empty.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" empty.args
      (fun s' vs => vs = [.i32 0] ∧ Holds s' empty.dst []) :=
  empty.returns empty_prep empty_invoke empty_run empty_result empty_holds hp

/-- R2's conclusion for a valid independent block containing a match. -/
theorem matched_r2 {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H matched.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" matched.args
      (fun s' vs => vs = [.i32 13] ∧ Holds s' matched.dst matchContent) :=
  matched.returns matched_prep matched_invoke matched_run matched_result matched_holds hp

/-- R3's nonnegative-result conclusion for an accepted input with a match. -/
theorem matched_r3 :
    0 ≤ (13 : BitVec 32).toInt →
      (13 : BitVec 32).toInt ≤ (matched.initDst.length : Int) ∧
        ∃ ss last content, Lz4.ParsesAny matched.input ss last ∧
          (Lz4.decode ss []).map (· ++ last) = some content ∧
          content.length = (13 : BitVec 32).toInt.toNat ∧
          Holds matchedFinal.store matched.dst content := by
  intro _
  refine ⟨by decide, [matchSeq], matchLast, matchContent, ?_, by decide, by decide, matched_holds⟩
  refine ⟨0, by decide, by decide, ?_⟩
  intro s hs
  simp only [List.mem_singleton] at hs
  subst hs
  decide

/-- R1's one-i32 total-return conclusion for a malformed input. -/
theorem malformed_r1 {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H malformed.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" malformed.args
      (fun _ vs => ∃ result : BitVec 32, vs = [.i32 result]) := by
  obtain ⟨rfl, rfl⟩ := malformed.prepared_eq malformed_prep hp
  refine ⟨2, by decide +kernel, malformed_invoke, ?_⟩
  exact (must_returned_of_runDet_get (P := fun _ _ => True)
    malformed_run malformed_result trivial).mono (by
      rintro (⟨s', vs⟩ | s' | ⟨s', a⟩) h
      · exact ⟨-2, h.1⟩
      all_goals exact h)

/-! ## The domain's empty-buffer cases (consultant-10): an empty buffer strictly inside the other,
where ordered separation fails and `Buffers` holds. -/

/-- An empty input strictly inside the destination's range. -/
def insideDst : Fixture := { src := 196609, input := [], initDst := [0xCC, 0xCC] }

/-- An empty destination strictly inside the input's range. -/
def insideSrc : Fixture := { dst := 131073, input := [0x10, 0x61], initDst := [] }

theorem insideDst_domain :
    Buffers insideDst.src insideDst.dst insideDst.input insideDst.initDst ∧
      ¬ (insideDst.src + insideDst.input.length ≤ insideDst.dst ∨
        insideDst.dst + insideDst.initDst.length ≤ insideDst.src) := by
  simp only [Buffers, insideDst]; decide

theorem insideSrc_domain :
    Buffers insideSrc.src insideSrc.dst insideSrc.input insideSrc.initDst ∧
      ¬ (insideSrc.src + insideSrc.input.length ≤ insideSrc.dst ∨
        insideSrc.dst + insideSrc.initDst.length ≤ insideSrc.src) := by
  simp only [Buffers, insideSrc]; decide

theorem insideDst_prep : (store0.prep insideDst.prep).isSome := by decide +kernel
theorem insideSrc_prep : (store0.prep insideSrc.prep).isSome := by decide +kernel

theorem insideDst_invoke : InvokeOK insideDst.store 2 insideDst.args := by
  refine ⟨.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩
    alloc.2 Lifted.func2, ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩,
    by kernel_rfl, rfl, ?_⟩
  exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))

theorem insideSrc_invoke : InvokeOK insideSrc.store 2 insideSrc.args := by
  refine ⟨.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩], 0⟩
    alloc.2 Lifted.func2, ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩,
    by kernel_rfl, rfl, ?_⟩
  exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))

theorem insideDst_run : (runDet 1000 insideDst.config).isSome := by decide +kernel
theorem insideSrc_run : (runDet 1000 insideSrc.config).isSome := by decide +kernel

theorem insideDst_result :
    ((runDet 1000 insideDst.config).get insideDst_run).instrs = vals [.i32 (-1)] := by kernel_rfl
theorem insideSrc_result :
    ((runDet 1000 insideSrc.config).get insideSrc_run).instrs = vals [.i32 (-1)] := by kernel_rfl

/-- R1's one-i32 total-return conclusion with an empty input inside the destination. -/
theorem insideDst_r1 {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H insideDst.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" insideDst.args
      (fun _ vs => ∃ result : BitVec 32, vs = [.i32 result]) := by
  obtain ⟨rfl, rfl⟩ := insideDst.prepared_eq insideDst_prep hp
  refine ⟨2, by decide +kernel, insideDst_invoke, ?_⟩
  exact (must_returned_of_runDet_get (P := fun _ _ => True)
    insideDst_run insideDst_result trivial).mono (by
      rintro (⟨s', vs⟩ | s' | ⟨s', a⟩) h
      · exact ⟨-1, h.1⟩
      all_goals exact h)

/-- R1's one-i32 total-return conclusion with an empty destination inside the input. -/
theorem insideSrc_r1 {H : HostSem} {s : Store} {inst : ModuleInst}
    (hp : Prepared Lifted.module H insideSrc.prep s inst) :
    CallReturns H s inst "LZ4_decompress_safe" insideSrc.args
      (fun _ vs => ∃ result : BitVec 32, vs = [.i32 result]) := by
  obtain ⟨rfl, rfl⟩ := insideSrc.prepared_eq insideSrc_prep hp
  refine ⟨2, by decide +kernel, insideSrc_invoke, ?_⟩
  exact (must_returned_of_runDet_get (P := fun _ _ => True)
    insideSrc_run insideSrc_result trivial).mono (by
      rintro (⟨s', vs⟩ | s' | ⟨s', a⟩) h
      · exact ⟨-1, h.1⟩
      all_goals exact h)

end Subjects.Lz4C.Accept
