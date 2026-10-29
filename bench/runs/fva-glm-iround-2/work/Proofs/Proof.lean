import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

attribute [-wasm_step] numStep numUnique instrUnique

private theorem artifact_return :
    Returns Lifted.module "iround" [.f64 0x3fdfffffffffffff] [.i32 1] := by
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl h
  have hf : s.funcs[0]? = some (.wasm
      ⟨[.num .f64], [.num .i32]⟩ inst Lifted.func0) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
    rfl
  have he : inst.exportFunc "iround" = some 0 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
    rfl
  clear ha h
  refine ⟨0, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
  have hh : AInstr.plain (.fconst .w64 4602678819172646912) =
      (Val.f64 0x3fe0000000000000).instr := rfl
  have hadd : numStep (.fbinop .w64 .add)
      [.f64 0x3fdfffffffffffff, .f64 0x3fe0000000000000] =
      some (some (.f64 0x3ff0000000000000)) := by decide +kernel
  have htrunc : numStep (.cvtop (.truncSat .w32 .w64 .s))
      [.f64 0x3ff0000000000000] = some (some (.i32 1)) := by decide +kernel
  have hnan : Num.Impl.isNaN (ofBits f64fmt 0x3ff0000000000000) = false := by
    decide +kernel
  have hu : instrUnique (.fbinop .w64 .add)
      [.f64 0x3fe0000000000000, .f64 0x3fdfffffffffffff] = true := by decide +kernel
  have hut : instrUnique (.cvtop (.truncSat .w32 .w64 .s))
      [.f64 0x3ff0000000000000] = true := by decide +kernel
  have hui : instrUnique (.localGet 0) [] = true := rfl
  unfold invokeConfig
  wasm_run [hf, Lifted.func0, hh, hadd, htrunc, hnan, hu, hut, hui]
  exact Must.done (o := .returned s [.i32 1]) ⟨rfl, rfl⟩ rfl

theorem R1_counterexample_holds : R1_counterexample := by
  have hx : ofBits f64fmt (0x3fdfffffffffffff : BitVec 64) =
      .normal false 4503599627370495 (-2) := by decide +kernel
  have hr : (ofBits f64fmt (0x3fdfffffffffffff : BitVec 64)).toReal f64fmt =
      (9007199254740991 : ℝ) / 18014398509481984 := by
    rw [hx]
    norm_num [FVal.toReal, f64fmt]
  unfold R1_counterexample
  dsimp only
  refine ⟨?_, hr, ?_, ?_, artifact_return, ?_⟩
  · rw [hx]; trivial
  all_goals rw [hr]; norm_num

end Proofs
