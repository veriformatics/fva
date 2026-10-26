import FVATest.Subjects.EdgerCpm.LoaderSetup
import FVA.Proof.Exec.Instantiate

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def placeholder : Store × ModuleInst :=
  allocModule env Lifted.module imports (Lifted.module.globals.map (·.type.val.default))
    (Lifted.module.elems.map fun _ => [])

noncomputable def globalValues? : Option (List Val) :=
  Lifted.module.globals.mapM fun g => evalConst 100 placeholder.1 placeholder.2 g.init

theorem globalValues_some : globalValues?.isSome := by decide +kernel
noncomputable def globalValues : List Val := globalValues?.get globalValues_some

noncomputable def elementValues? : Option (List (List Ref)) :=
  Lifted.module.elems.mapM fun e => e.init.mapM fun ex =>
    evalConst 100 placeholder.1 placeholder.2 ex >>= asRef

theorem elementValues_some : elementValues?.isSome := by decide +kernel
noncomputable def elementValues : List (List Ref) := elementValues?.get elementValues_some

noncomputable def allocation : Store × ModuleInst :=
  allocModule env Lifted.module imports globalValues elementValues

theorem globals_eq :
    (Lifted.module.globals.mapM fun g => evalConst 100 allocation.1 allocation.2 g.init) =
      some globalValues := by decide +kernel

theorem elements_eq :
    (Lifted.module.elems.mapM fun e => e.init.mapM fun ex =>
      evalConst 100 allocation.1 allocation.2 ex >>= asRef) = some elementValues := by
  decide +kernel

end Subjects.EdgerCpm.Existence
