import FVATest.Subjects.Bustools.Spec

/-! Proof of the import claim: the lifted module's import list, compared by the kernel. -/

namespace Subjects.Bustools

theorem wasiImports_holds : wasiImports := by
  unfold wasiImports
  decide +kernel

end Subjects.Bustools
