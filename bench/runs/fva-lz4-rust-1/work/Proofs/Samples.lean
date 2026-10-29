import Proofs.ConcreteRuns

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Samples

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem example_of_check (e : Example) (hd : domainCheck e = true)
    (hc : runCheck e = true) : ExampleCorrect e := by
  have hd' := of_decide_eq_true hd
  refine ⟨hd'.1, hd'.2.1, hd'.2.2, ?_, ?_⟩
  · intro H
    obtain ⟨mem, hm, hsize⟩ := Execution.fresh_mem_size
    refine ⟨Execution.freshStore, Execution.allocation.2,
      Execution.fresh_instance H, ⟨mem, hm, ?_⟩, ⟨mem, hm, ?_⟩⟩ <;> omega
  · intro H s inst hi
    obtain ⟨rfl, rfl⟩ := Execution.instance_unique hi
    have he : Execution.allocation.2.exportFunc "lz4_decompress" = some 7 := rfl
    have hf : (Execution.freshStore.withBytes 131072 e.input).funcs[7]? = some (.wasm
        ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩
        Execution.allocation.2 Lifted.func7) := by
      rw [Store.withBytes_funcs, Execution.fresh_funcs]
      rfl
    refine ⟨7, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
    unfold runCheck at hc
    cases hr : runDet 10000 (call e) with
    | none => simp [hr] at hc
    | some c =>
      rw [hr] at hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hinstr, hmem⟩ := hc
      have hinstr' := resultCheck_sound hinstr
      cases hm : c.store.mems[0]? with
      | none => simp [hm] at hmem
      | some mem =>
        rw [hm] at hmem
        have hout := of_decide_eq_true hmem
        have heq : c = ⟨c.store, c.frame, vals [.i32 e.result]⟩ := by
          calc
            c = ⟨c.store, c.frame, c.instrs⟩ := rfl
            _ = _ := by rw [hinstr']
        rw [heq] at hr
        exact must_returned_of_runDet hr ⟨rfl, mem, hm, hout⟩

end Proofs.Samples
