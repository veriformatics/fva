import Proofs.Spec
import Proofs.Startup

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem decoder_at_instance {H : HostSem} {s : Store} {inst : ModuleInst}
    (hi : Instance Lifted.module H s inst) :
    s.funcs[2]? = some (.wasm decoderType allocated.2 Lifted.func2) ∧
    inst.exportFunc "LZ4_decompress_safe" = some 2 := by
  constructor
  · rw [(instance_unique (H := H) (s := s) (inst := inst) hi).1]
    exact initialized_decoder
  · rw [(instance_unique (H := H) (s := s) (inst := inst) hi).2]
    exact initialized_export

private theorem eqz_ptr : ieqz (131072 : BitVec 32) = 0 := by decide +kernel
private theorem eqz_zero : ieqz (0 : BitVec 32) = 1 := by decide +kernel
private theorem lt_zero : iltS (0 : BitVec 32) (0#32) = 0 := by decide +kernel
private theorem lt_zero_plain : iltS (0 : BitVec 32) 0 = 0 := by decide +kernel
private theorem lt_one : iltS (1 : BitVec 32) (0#32) = 0 := by decide +kernel
private theorem ne_one : ine (1 : BitVec 32) (1#32) = 0 := by decide +kernel
private theorem one_ne_zero : (1 : BitVec 32) ≠ 0 := by decide

private theorem pointer_nat : (131072 : BitVec 32).toNat = 131072 := by kernel_rfl
private theorem zero_byte : (0 : UInt8).toNat = 0 := by kernel_rfl
private theorem zero_bv : BitVec.ofNat 32 0 = 0 := by kernel_rfl

theorem emptySource_holds : emptySource := by
  refine ⟨fun H => ⟨initialized.store, allocated.2, initialized_instance H⟩, ?_⟩
  intro H s inst hi
  obtain ⟨hf, he⟩ := decoder_at_instance hi
  refine ⟨2, he, ⟨.wasm decoderType allocated.2 Lifted.func2, hf, ?_⟩, ?_⟩
  · exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))
  · unfold invokeConfig
    wasm_run [hf, Lifted.func2, decoderType, eqz_ptr, eqz_zero, lt_zero, lt_zero_plain, lt_one, ne_one, one_ne_zero]
    exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ rfl

private theorem read_one (m : MemInst) (p : Nat) (b : UInt8) :
    (m.withBytes p [b]).read p 1 = b.toNat := by
  simp [MemInst.read, MemInst.withBytes]

private theorem allocated_mems : allocated.2.mems = [0] := by kernel_rfl

private theorem zero_capacity_run (H : HostSem) (s : Store) (b : UInt8) (mem : MemInst)
    (hf : s.funcs[2]? = some (.wasm decoderType allocated.2 Lifted.func2))
    (hm : s.mems[0]? = some mem) (hbound : 131073 ≤ mem.size) :
    Must H (fun o => match o with
      | .returned _ vs => vs = [.i32 (if b = 0 then 0 else 4294967295)]
      | .trapped _ => False)
      (invokeConfig (s.withBytes 131072 [b]) 2
        [.i32 131072, .i32 196608, .i32 1, .i32 0]) := by
  have hf' : (s.withBytes 131072 [b]).funcs[2]? =
      some (.wasm decoderType allocated.2 Lifted.func2) := hf
  have hm' := Store.withBytes_mem0 hm 131072 [b]
  have hno : ¬ mem.size < 131073 := by omega
  have hptr : (131072 : BitVec 32) ≠ 0 := by decide
  have hneg : ¬ (0 : BitVec 32).slt 0 := by decide
  by_cases hb : b = 0
  · subst b
    unfold invokeConfig
    wasm_run [hptr, hneg, hf', Lifted.func2, decoderType, eqz_ptr, eqz_zero, lt_zero, lt_zero_plain, lt_one, ne_one, one_ne_zero, hm', allocated_mems,
      MemInst.withBytes_size, pointer_nat, zero_byte, zero_bv, hno, read_one]
    exact Must.done (o := .returned (s.withBytes 131072 [0]) [.i32 0]) ⟨rfl, rfl⟩ rfl
  · have hsmall : b.toNat < 2 ^ 32 := by have := b.toNat_lt; omega
    have hn : b.toNat ≠ 0 := fun h => hb (UInt8.toNat_inj.mp h)
    have hv : (BitVec.ofNat 32 b.toNat) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at h'
      exact hn h'
    unfold invokeConfig
    wasm_run [hptr, hneg, hf', Lifted.func2, decoderType, eqz_ptr, eqz_zero, lt_zero, lt_zero_plain, lt_one, ne_one, one_ne_zero, hm', allocated_mems,
      MemInst.withBytes_size, pointer_nat, zero_byte, zero_bv, hno, read_one, hv]
    exact Must.done (o := .returned (s.withBytes 131072 [b]) [.i32 4294967295])
      ⟨rfl, rfl⟩ (by simp only [hb, ↓reduceIte])

theorem zeroCapacityByte_holds : zeroCapacityByte := by
  intro b
  refine ⟨?_, ?_⟩
  · intro H
    refine ⟨initialized.store, allocated.2, initialized_instance H, initialMem,
      initialMem_lookup, ?_⟩
    rw [initialMem_size]
    change 131073 ≤ 2097152
    decide
  · intro H s inst hi hfit
    obtain ⟨hf, he⟩ := decoder_at_instance hi
    obtain ⟨mem, hm, hbound⟩ := hfit
    refine ⟨2, he, ⟨.wasm decoderType allocated.2 Lifted.func2, hf, ?_⟩, ?_⟩
    · exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))
    · apply zero_capacity_run H s b mem hf hm
      exact hbound

end Proofs
