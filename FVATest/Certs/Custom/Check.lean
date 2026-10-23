import FVATest.Certs.Custom.Rel

/-! The project relation's checker, proven sound (the certificate convention: `R.check`,
`R.check_sound`). -/

namespace FVATest.Certs.Custom

/-- The output's bytes are the input's, reversed. -/
def Reversed.check (i o : FVA.Cert.Blob) : Bool := decide (o.data = i.data.reverse)

theorem Reversed.check_sound (i o : FVA.Cert.Blob) (h : Reversed.check i o = true) :
    FVA.Cert.Accepted Reversed i o :=
  show o.data = i.data.reverse from of_decide_eq_true h

end FVATest.Certs.Custom
