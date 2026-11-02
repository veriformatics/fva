import FVATest.Cheats.SubjectArg.Spec

namespace Cheats.SubjectArg

theorem picked_holds : picked := rfl

theorem code_holds : code := fun b => by split <;> decide

end Cheats.SubjectArg
