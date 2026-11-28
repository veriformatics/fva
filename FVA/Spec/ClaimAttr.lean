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

/-- `@[fva_witness C]`: this theorem proves claim `C`'s domain obligation (U37: `fva trust` checks
its statement against the obligation it derives from `C`). -/
initialize witnessAttr : Lean.ParametricAttribute Lean.Name ←
  Lean.registerParametricAttribute {
    name := `fva_witness
    descr := "a witness of an FVA claim's input domain: fva trust checks its statement"
    getParam := fun decl stx => do
      let target ←
        Lean.Elab.realizeGlobalConstNoOverloadWithInfo (← Lean.Attribute.Builtin.getIdent stx)
      unless claimAttr.hasTag (← Lean.getEnv) target do
        throwError "@[fva_witness {target}]: {target} is no @[fva_claim] definition"
      unless (← Lean.getConstInfo decl) matches .thmInfo _ do
        throwError "@[fva_witness {target}]: {decl} is not a theorem"
      return target }

end FVA
