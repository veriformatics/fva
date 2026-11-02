import Lean

/-!
# The claim marker (reviewed once, D13)

`@[fva_claim]` marks a definition of a spec module as a claim: `fva trust` requires a proof of
each marked definition. Unmarked `Prop` definitions of the spec module are vocabulary: the report
lists them apart, since nothing proves them. Every lifted or blob module imports this one (through
`FVA.Lifted`), so a spec about an artifact needs no import of its own.
-/

namespace FVA

/-- `@[fva_claim]` (`fva trust` reads it from each module's `.olean` entries). -/
initialize claimAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `fva_claim "a claim of an FVA spec module: fva trust requires its proof"

end FVA
