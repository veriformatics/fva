import FVA.Impl.Exec.Ref
import FVA.Impl.Valid

/-!
# Validation and instantiation helpers, pinned

Concrete cases of behavior the U28c contract specifies that no proof or mutation-stage test fixes
(U28c survivors; `scripts/test-p2valid` + `scripts/test-p2exec` pin them outside the stages).
-/

namespace FVA.Wasm.Pin

/-- U28c V4 (Wasm 3.0 `Catch_ok`): `catch_all_ref` hands its label a non-null `exnref`. -/
theorem catchOk_allRef_nonNull :
    Valid.Check.catchOk { labels := [[.ref ⟨false, .abs .exn⟩]] } (.allRef 0) = true := rfl

private def glob (e : Expr) : Global := { type := ⟨.const, .num .i32⟩, init := e }

/-- U28c V5 (R1 = B): a global's initializer reads an earlier defined global's value, the module's
second global included. -/
theorem initCandidates_earlier :
    (Exec.Ref.initCandidates 8 {}
      { globals := [glob [.iconst .w32 1], glob [.iconst .w32 2], glob [.globalGet 1]] }
      []).map (·.1) = some [.i32 1, .i32 2, .i32 2] := rfl

end FVA.Wasm.Pin
