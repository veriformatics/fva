import FVATest.Subjects.EdgerCpm.Caller
import FVATest.Subjects.EdgerCpm.LoaderFinish

namespace Subjects.EdgerCpm

open FVA.Wasm FVA.Wasm.Exec Existence

/-- One sufficiently large linked loader-prepared store witnesses every covered input. -/
theorem exists_admissible_of_loader {env : Store} {imports : List ExternVal}
    {loaded : Store} {inst : ModuleInst} {mem : MemInst}
    (hl : LoaderReady FiniteAllocator.host Lifted.module env imports loaded inst)
    (hlink : Linked loaded inst 12 13) (hm : loaded.mems[0]? = some mem)
    (hfit : FiniteAllocator.limit ≤ mem.size) :
    ∀ x, Domain x → ∃ H l s inst, Admissible H x l s inst := by
  intro x hx
  refine ⟨FiniteAllocator.host, layout x, callerStore loaded mem x, inst, ?_,
    caller_data hx hm hfit, ?_, (fun _ => layout_separate x), layout_bounds hx⟩
  · exact ⟨env, imports, loaded, prep x, hl, caller_prep hx hm hfit⟩
  · exact ⟨12, 13, FiniteAllocator.heap, FiniteAllocator.blocks,
      FiniteAllocator.ready (8 * x.m), caller_linked hlink,
      FiniteAllocator.allocator _ (domain_cap hx), caller_ready hx hm hfit,
      fun _ ha => Or.inl (layout_outside_heap hx ha)⟩

theorem exists_admissible : ∀ x, Domain x → ∃ H l s inst, Admissible H x l s inst :=
  exists_admissible_of_loader (loader_ready FiniteAllocator.host) loaded_linked
    loaded_mem loaded_fits

end Subjects.EdgerCpm
