import Proofs.Spec
import Proofs.Startup

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def caseStart (input : List UInt8) (capacity : Nat) : Store :=
  (initialized.store.withBytes 196608 (List.replicate capacity 165)).withBytes 131072 input

noncomputable def caseEnd (input : List UInt8) (capacity : Nat) : Config :=
  (runDet 5000 (invokeConfig (caseStart input capacity) 2
    [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
      .i32 (BitVec.ofNat 32 capacity)])).getD ⟨{}, ⟨[], {}⟩, []⟩

noncomputable def caseMem (input : List UInt8) (capacity : Nat) : MemInst :=
  (caseEnd input capacity).store.mems[0]?.getD { pages := 0, max := none, byte := fun _ => 0 }

private theorem call_of_run {H : HostSem} {s : Store} {inst codeInst : ModuleInst}
    {args results : List Val} {P : Store → List Val → Prop} {c : Config}
    (he : inst.exportFunc "LZ4_decompress_safe" = some 2)
    (hf : s.funcs[2]? = some (.wasm decoderType codeInst Lifted.func2))
    (ht : List.Forall₂ (Val.HasType s) args decoderType.params)
    (hr : runDet 5000 (invokeConfig s 2 args) = some c)
    (hv : c.instrs = vals results) (hp : P c.store results) :
    CallReturns H s inst "LZ4_decompress_safe" args P := by
  rcases c with ⟨s', f', es⟩
  dsimp only at hv hp
  subst es
  exact ⟨2, he, ⟨.wasm decoderType codeInst Lifted.func2, hf, ht⟩,
    must_returned_of_runDet hr hp⟩

private theorem caseStart_decoder (input : List UInt8) (capacity : Nat) :
    (caseStart input capacity).funcs[2]? =
      some (.wasm decoderType allocated.2 Lifted.func2) := by
  simpa only [caseStart, Store.withBytes_funcs] using initialized_decoder

private theorem decodeCase_of_run {input output : List UInt8} {capacity : Nat}
    (fitInput : Fits initialized.store 131072 input.length)
    (fitOutput : Fits initialized.store 196607 (capacity + 2))
    (hr : runDet 5000 (invokeConfig (caseStart input capacity) 2
      [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
        .i32 (BitVec.ofNat 32 capacity)]) = some (caseEnd input capacity))
    (hv : (caseEnd input capacity).instrs = vals [.i32 (BitVec.ofNat 32 output.length)])
    (hp : ∃ before after, initialized.store.mems[0]? = some before ∧
      (caseEnd input capacity).store.mems[0]? = some after ∧
      (∀ k : Fin output.length, after.byte (196608 + k.val) = output[k.val]) ∧
      after.byte 196607 = before.byte 196607 ∧
      after.byte (196608 + capacity) = before.byte (196608 + capacity)) :
    DecodeCase input output capacity := by
  refine ⟨fun H => ⟨initialized.store, allocated.2, initialized_instance H,
    fitInput, fitOutput⟩, ?_⟩
  intro H s inst hi _ _
  have hs := (instance_unique (H := H) (s := s) (inst := inst) hi).1
  have he := (instance_unique (H := H) (s := s) (inst := inst) hi).2
  rw [hs, he]
  exact call_of_run initialized_export (caseStart_decoder input capacity)
    (.cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))) hr hv ⟨rfl, hp⟩

private theorem fit_input_small {n : Nat} (hn : n ≤ 65536) :
    Fits initialized.store 131072 n := by
  refine ⟨initialMem, initialMem_lookup, ?_⟩
  rw [initialMem_size]
  omega

private theorem fit_output_small {n : Nat} (hn : n ≤ 65536) :
    Fits initialized.store 196607 (n + 2) := by
  refine ⟨initialMem, initialMem_lookup, ?_⟩
  rw [initialMem_size]
  omega

theorem emptyBlock_holds : emptyBlock := by
  apply decodeCase_of_run (input := [0]) (output := []) (capacity := 0) (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [0] 0, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · intro k; exact Fin.elim0 k
    · kernel_rfl
    · kernel_rfl


theorem emptyBlockPositive_holds : emptyBlockPositive := by
  apply decodeCase_of_run (input := [0]) (output := []) (capacity := 1)
    (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [0] 1, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · decide +kernel
    · kernel_rfl
    · kernel_rfl

theorem literalBlock_holds : literalBlock := by
  apply decodeCase_of_run (input := [80, 65, 66, 67, 68, 69]) (output := [65, 66, 67, 68, 69]) (capacity := 5)
    (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [80, 65, 66, 67, 68, 69] 5, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · decide +kernel
    · kernel_rfl
    · kernel_rfl

theorem overlappingMatch_holds : overlappingMatch := by
  apply decodeCase_of_run (input := [19, 65, 1, 0, 80, 66, 67, 68, 69, 70]) (output := [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]) (capacity := 13)
    (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 13, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · decide +kernel
    · kernel_rfl
    · kernel_rfl

theorem extendedLiterals_holds : extendedLiterals := by
  apply decodeCase_of_run (input := [240, 0, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]) (output := [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]) (capacity := 15)
    (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [240, 0, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79] 15, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · decide +kernel
    · kernel_rfl
    · kernel_rfl

theorem extendedMatch_holds : extendedMatch := by
  apply decodeCase_of_run (input := [31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70]) (output := (List.replicate 20 65 ++ [66, 67, 68, 69, 70])) (capacity := 25)
    (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70] 25, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · decide +kernel
    · kernel_rfl
    · kernel_rfl

theorem zeroOffset_holds : zeroOffset := by
  apply decodeCase_of_run (input := [3, 0, 0, 80, 65, 66, 67, 68, 69]) (output := [0, 0, 0, 0, 0, 0, 0, 65, 66, 67, 68, 69]) (capacity := 12)
    (fit_input_small (by decide)) (fit_output_small (by decide))
  · kernel_rfl
  · kernel_rfl
  · refine ⟨initialMem, caseMem [3, 0, 0, 80, 65, 66, 67, 68, 69] 12, initialMem_lookup, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · decide +kernel
    · kernel_rfl
    · kernel_rfl

end Proofs
