import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Valid.Validator

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

private theorem instantiated_eval :
    instantiate 1500 {} Lifted.module [] = some (initialStore, initialInst) := by
  kernel_rfl

theorem initialization_holds : initialization := by
  intro H
  exact instantiate_sound (by exact List.Forall₂.nil) instantiated_eval

private theorem empty_eval :
    runDet 100 (invokeConfig (initialStore.withBytes 131072 [0]) 2
      [.i32 131072, .i32 196608, .i32 1, .i32 0]) =
    some ⟨initialStore.withBytes 131072 [0], ⟨[], {}⟩, vals [.i32 0]⟩ := by
  kernel_rfl

theorem emptyBlock_holds : emptyBlock := by
  intro H
  have hf : (initialStore.withBytes 131072 [0]).funcs[2]? =
      some (.wasm ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩
        initialInst Lifted.func2) := by rfl
  refine ⟨2, rfl, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  exact must_returned_of_runDet empty_eval ⟨rfl, rfl⟩

theorem zeroCapacity_holds : zeroCapacity := by
  intro H mem src dst n hsrc hsize
  have hf : (callerStore mem).funcs[2]? =
      some (.wasm ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩
        initialInst Lifted.func2) := by rfl
  have hm : (callerStore mem).mems[0]? = some mem := rfl
  have hi : initialInst.mems[0]? = some 0 := rfl
  have hz : Num.ieqz src = 0 := (Num.ieqz_eq_zero src).mpr hsrc
  refine ⟨2, rfl, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  have hlt : Num.iltS (0 : BitVec 32) (BitVec.ofNat 32 0) = 0 := rfl
  have hn1 : Num.ine (BitVec.ofNat 32 1) (BitVec.ofNat 32 1) = 0 := rfl
  have hbound : src.toNat + 0 + 1 ≤ mem.size := by omega
  have hbound' : ¬ mem.size < src.toNat + 0 + 1 := by omega
  have hread : mem.read (src.toNat + 0) 1 = (mem.byte src.toNat).toNat := by
    simp [MemInst.read]
  unfold invokeConfig
  by_cases hn : n = BitVec.ofNat 32 1
  · subst n
    wasm_run [hf, Lifted.func2, hz, hlt, hn1, hm, hi, hbound', hread]
    by_cases hb : mem.byte src.toNat = 0
    · have hzero : BitVec.ofNat 32 (mem.byte src.toNat).toNat = 0 := by simp [hb]
      simp only [hzero, decide_true, Bool.cond_true]
      exact Must.done (o := .returned _ [.i32 0]) ⟨rfl, rfl⟩ ⟨rfl, by simp [hb]⟩
    · have hnonzero : BitVec.ofNat 32 (mem.byte src.toNat).toNat ≠ 0 := by
        intro he
        have hnz : (mem.byte src.toNat).toNat < 2^32 := by
          have := (mem.byte src.toNat).toBitVec.isLt
          change (mem.byte src.toNat).toNat < 2^8 at this
          omega
        have hz' := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnz] at hz'
        have hb' : (mem.byte src.toNat).toNat = (0 : UInt8).toNat := hz'
        exact hb ((UInt8.toNat_inj).mp hb')
      simp only [hnonzero, decide_false, Bool.cond_false]
      exact Must.done (o := .returned _ [.i32 (-1)]) ⟨rfl, rfl⟩ ⟨rfl, by simp [hb]⟩
  · have hn' : Num.ine n (BitVec.ofNat 32 1) ≠ 0 := by
      have hh : n.toNat ≠ 1 := by
        intro he
        exact hn (BitVec.eq_of_toNat_eq he)
      simp [Num.ine, Num.bool, hh]
    wasm_run [hf, Lifted.func2, hz, hn', hlt]
    refine Must.done (o := .returned (callerStore mem) [.i32 (-1)]) ⟨rfl, rfl⟩ ?_
    simp [hn]


private noncomputable def caseFinal (input : List UInt8) (capacity : Nat) : Config :=
  let c := invokeConfig (caseStore input capacity) 2
    [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
      .i32 (BitVec.ofNat 32 capacity)]
  (runDet 4000 c).getD c

private theorem checked_case (input : List UInt8) (capacity : Nat) (result : Int)
    (output : List UInt8) (final : Config)
    (hr : runDet 4000 (invokeConfig (caseStore input capacity) 2
      [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
        .i32 (BitVec.ofNat 32 capacity)]) =
      some ⟨final.store, final.frame, vals [.i32 (BitVec.ofInt 32 result)]⟩)
    (hb : (final.store.mems[0]?).map (fun mem =>
      (List.range output.length).map (fun i => mem.byte (196608 + i))) = some output) :
    ∀ H, CallReturns H (caseStore input capacity) initialInst "LZ4_decompress_safe"
      [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
        .i32 (BitVec.ofNat 32 capacity)]
      (fun s vs => vs = [.i32 (BitVec.ofInt 32 result)] ∧
        ∃ mem, s.mems[0]? = some mem ∧
          (List.range output.length).map (fun i => mem.byte (196608 + i)) = output) := by
  intro H
  have hf : (caseStore input capacity).funcs[2]? =
      some (.wasm ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩
        initialInst Lifted.func2) := by rfl
  refine ⟨2, rfl, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  exact must_returned_of_runDet hr ⟨rfl, Option.map_eq_some_iff.mp hb⟩

theorem literalCase_holds : literalCase := by
  exact checked_case [16, 65] 1 1 [65]
    (caseFinal [16, 65] 1) (by kernel_rfl) (by kernel_rfl)

theorem overlapCase_holds : overlapCase := by
  exact checked_case [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 13 13 [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]
    (caseFinal [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 13) (by kernel_rfl) (by kernel_rfl)

theorem longMatchCase_holds : longMatchCase := by
  exact checked_case [31, 65, 1, 0, 1, 80, 66, 67, 68, 69, 70] 26 26 [65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]
    (caseFinal [31, 65, 1, 0, 1, 80, 66, 67, 68, 69, 70] 26) (by kernel_rfl) (by kernel_rfl)

theorem zeroOffsetCase_holds : zeroOffsetCase := by
  exact checked_case [3, 0, 0, 80, 66, 67, 68, 69, 70] 12 12 [0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70]
    (caseFinal [3, 0, 0, 80, 66, 67, 68, 69, 70] 12) (by kernel_rfl) (by kernel_rfl)

theorem shortcutCase_holds : shortcutCase := by
  exact checked_case [131, 65, 66, 67, 68, 69, 70, 71, 72, 8, 0, 240, 0, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111] 64 30 [65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 67, 68, 69, 70, 71, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
    (caseFinal [131, 65, 66, 67, 68, 69, 70, 71, 72, 8, 0, 240, 0, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111] 64) (by kernel_rfl) (by kernel_rfl)

private theorem validation_eval : FVA.Wasm.Valid.validate Lifted.module = true := by
  kernel_rfl

theorem validModule_holds : validModule := FVA.Wasm.Valid.validate_sound validation_eval

end Proofs
