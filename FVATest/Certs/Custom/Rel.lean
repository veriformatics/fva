import FVA.Spec.Cert

/-! A project's own relation (contract U9 P6): read in the project's review surface. -/

namespace FVATest.Certs.Custom

/-- The output file holds the input file's bytes in reverse order. -/
def Reversed (i o : List UInt8) : Prop := o = i.reverse

end FVATest.Certs.Custom
