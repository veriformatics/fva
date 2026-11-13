import FVA.Impl.Exec.Ref

/-!
# Instantiation's tag index space + the null-table predicate (U28b mutation survivors, classifier-2)

`allocModule` (3.0 `allocmodule`) gives an instance its tag addresses as the imported ones, in
import order and aliases kept, then the fresh ones after the store's; a tag export resolves in that
index space (U28b R4). `Module.nullTables` admits the 2.0 tables, whose initializer is one
`ref.null` (R4; `fva call` and the instantiation proofs rest on it). No test executes tags before
U28e's runner, and the proofs' `nullTables = true` premises never establish the predicate, so
these checks pin what the survivors of U28b's mutation update changed. Like
`FVATest/DecodeDiag.lean`, the module sits in `FVATest.Certs`' import closure: a proof root built
for every scope mutant, outside the test executables' closures, so adding it re-keys survivors
alone (`docs/contracts/U12-mutation.md` R2).
-/

namespace FVA.Test.RuntimeDiag

open FVA.Wasm FVA.Wasm.Exec

/-- `[] → []`: the tags' function type. -/
def ft : FuncType := ⟨[], []⟩

/-- The tags' closed defined type. -/
def dt : DefType := ⟨[ft], 0⟩

-- imported tags keep their addresses, an alias included (`ExternVal.tags`)
example : (allocModule { tags := [⟨dt⟩, ⟨dt⟩] }
    { types := [[ft]], imports := [⟨"env", "a", .tag 0⟩, ⟨"env", "alias", .tag 0⟩] }
    [.tag 1, .tag 1] [] [] []).2.tags = [1, 1] := rfl

-- a module's own tag gets the address after the store's
example : (allocModule {} { types := [[ft]], tags := [⟨0⟩] } [] [] [] []).2.tags = [0] := rfl

-- an imported tag alone fills the index space
example : (allocModule { tags := [⟨dt⟩] }
    { types := [[ft]], imports := [⟨"env", "t", .tag 0⟩] } [.tag 0] [] [] []).2.tags = [0] := rfl

-- imports come first, fresh addresses after them
example : (allocModule { tags := [⟨dt⟩, ⟨dt⟩] }
    { types := [[ft]], imports := [⟨"env", "t", .tag 0⟩], tags := [⟨0⟩] }
    [.tag 1] [] [] []).2.tags = [1, 2] := rfl

-- a tag export exposes the tag's address, as a tag
example : ((allocModule {} { types := [[ft]], tags := [⟨0⟩], exports := [⟨"t", .tag 0⟩] }
    [] [] [] []).2.exports.map (·.value) |>.map fun
      | .tag a => some a
      | _ => none) = [some 0] := rfl

-- a 2.0 table (initializer `ref.null`) is a null table; any other initializer is not
example : ({ tables := [⟨⟨⟨1, none⟩, .funcref⟩, [.refNull (.abs .func)]⟩] } : Module).nullTables
    = true := rfl
example : ({ tables := [⟨⟨⟨1, none⟩, .funcref⟩, [.refFunc 0]⟩] } : Module).nullTables
    = false := rfl

end FVA.Test.RuntimeDiag
