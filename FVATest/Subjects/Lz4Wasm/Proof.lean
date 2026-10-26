import FVATest.Subjects.Lz4Wasm.Spec
import FVA.Proof.Lib.Instance
import FVATest.Subjects.Lz4.Parse

/-! Proofs of the lz4-wasm counterexamples (contract U14 S2). The run facts close by kernel
evaluation of the reference interpreter on the lifted bytes; each store/memory fact is a top-level
constant so the kernel, never the elaborator, reduces the prepared and final stores. -/

namespace Subjects.Lz4Wasm

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Lz4

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## Format side (R1): the returned block is not a valid LZ4 block -/

/-- The one sequence the block parses into: three literals, offset 1, match length 5. -/
def encSeq : Seq := ⟨[0x61, 0x62, 0x61], 1, 5⟩
/-- The block's trailing literals. -/
def encLast : List UInt8 := [0x61, 0x61, 0x61, 0x62, 0x61]

/-- The empty block `00` decodes to nothing and meets the end conditions. -/
theorem empty_block_valid : Lz4.Valid [0x00] [] :=
  ⟨[], [], ⟨0, by decide, by decide, by simp⟩, rfl, by simp [EndOk]⟩

/-- `encBlock` is not a valid LZ4 block of any content. -/
theorem encode_not_valid : ∀ c, ¬ Lz4.Valid encBlock c := by
  have hp : Parses encBlock [encSeq] encLast :=
    ⟨0, by decide, by decide, by intro s hs; simp at hs; subst hs; decide⟩
  have hend : ¬ EndOk [encSeq] encLast := by simp [EndOk, encSeq, encLast]
  rintro c ⟨ss, last, hp', -, hend'⟩
  obtain ⟨rfl, rfl⟩ := hp'.unique hp
  exact hend hend'

/-! ## Binary side: kernel runs of the reference interpreter on the lifted bytes -/

noncomputable def alloc : Store × ModuleInst := allocModule {} Lifted.module [] [] []

-- The prepared store for the encoder run.
theorem encPrepSome : (alloc.1.prep encPrep).isSome := by decide +kernel
noncomputable def encStore : Store := (alloc.1.prep encPrep).get encPrepSome
theorem encStore_eq : alloc.1.prep encPrep = some encStore := (Option.some_get encPrepSome).symm
theorem encMemSome : (encStore.mems[0]?).isSome := by decide +kernel
noncomputable def encMem : MemInst := (encStore.mems[0]?).get encMemSome
theorem encMem_eq : encStore.mems[0]? = some encMem := (Option.some_get encMemSome).symm

-- The encoder's final configuration and its output memory.
noncomputable def encCfg : Config :=
  invokeConfig encStore 2
    [.i32 (BitVec.ofNat 32 inputAddr), .i32 13, .i32 (BitVec.ofNat 32 (inputAddr + 13))]
theorem encRunSome : (runDet 600 encCfg).isSome := by decide +kernel
noncomputable def encFinal : Config := (runDet 600 encCfg).get encRunSome
theorem encFinalMemSome : (encFinal.store.mems[0]?).isSome := by decide +kernel
noncomputable def encFinalMem : MemInst := (encFinal.store.mems[0]?).get encFinalMemSome
theorem encFinalMem_eq : encFinal.store.mems[0]? = some encFinalMem :=
  (Option.some_get encFinalMemSome).symm

theorem encFinal_holds : Holds encFinal.store (inputAddr + 13) encBlock :=
  ⟨encFinalMem, encFinalMem_eq, by decide +kernel, by decide +kernel⟩

theorem encode_breaks_r1_holds : Subjects.Lz4Wasm.encode_breaks_r1 := by
  refine ⟨⟨fun H => ⟨encStore, alloc.2, ⟨alloc.1, instance_alloc_self H rfl rfl rfl rfl rfl,
    encStore_eq⟩, encMem, encMem_eq, by decide +kernel⟩, ?_⟩, encode_not_valid⟩
  rintro H s inst ⟨s₀, hinst, hprep⟩ -
  obtain ⟨h1, h2⟩ := Prod.mk.inj (instance_alloc rfl rfl rfl rfl hinst)
  subst h1; subst h2
  obtain rfl : s = encStore := Option.some.inj (hprep.symm.trans encStore_eq)
  refine ⟨2, by decide +kernel, ⟨_, rfl, ?_⟩, ?_⟩
  · refine .cons ?_ (.cons ?_ (.cons ?_ .nil)) <;> exact ⟨⟩
  · exact must_returned_of_runDet_get (P := fun s' _ => Holds s' (inputAddr + 13) encBlock)
      (n := 600) encRunSome (by kernel_rfl) encFinal_holds

/-! ## R3: the decoder reads past its input and traps -/

theorem decPrepSome : (alloc.1.prep [.write lastByte [0x00]]).isSome := by decide +kernel
noncomputable def decStore : Store := (alloc.1.prep [.write lastByte [0x00]]).get decPrepSome
theorem decStore_eq : alloc.1.prep [.write lastByte [0x00]] = some decStore :=
  (Option.some_get decPrepSome).symm
noncomputable def decCfg : Config :=
  invokeConfig decStore 3 [.i32 (BitVec.ofNat 32 lastByte), .i32 1, .i32 0]
theorem decRunSome : (runDet 200 decCfg).isSome := by decide +kernel

theorem decode_traps_valid_holds : Subjects.Lz4Wasm.decode_traps_valid := by
  refine ⟨empty_block_valid, fun H => ⟨decStore, alloc.2, alloc.1,
    instance_alloc_self H rfl rfl rfl rfl rfl, decStore_eq⟩, ?_⟩
  rintro H s inst ⟨s₀, hinst, hprep⟩
  obtain ⟨h1, h2⟩ := Prod.mk.inj (instance_alloc rfl rfl rfl rfl hinst)
  subst h1; subst h2
  obtain rfl : s = decStore := Option.some.inj (hprep.symm.trans decStore_eq)
  refine ⟨3, by decide +kernel, ⟨_, rfl, ?_⟩, ?_⟩
  · refine .cons ?_ (.cons ?_ (.cons ?_ .nil)) <;> exact ⟨⟩
  · exact must_trapped_of_runDet_get (n := 200) decRunSome (by kernel_rfl) trivial

end Subjects.Lz4Wasm
