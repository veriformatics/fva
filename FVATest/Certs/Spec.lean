import FVATest.Certs.Sort.Py.Spec
import FVATest.Certs.Sort.R.Spec
import FVATest.Certs.Sort.Java.Spec
import FVATest.Certs.Sort.Ts.Spec
import FVATest.Certs.Pos.Sorted.Spec
import FVATest.Certs.Pos.Empty.Spec
import FVATest.Certs.Compile.E1.Spec
import FVATest.Certs.Compile.E2.Spec
import FVATest.Certs.Compile.E3.Spec
import FVATest.Certs.Custom.Rev.Spec

/-! Every accepted certificate fixture (contract U9), for one `fva trust` run in the gate. -/

namespace FVATest.Certs

/-- Certificate: the Python producer's sorted output. -/
def sortPy : Prop := FVATest.Certs.Sort.Py.claim

/-- Certificate: the R producer's sorted output. -/
def sortR : Prop := FVATest.Certs.Sort.R.claim

/-- Certificate: the Java producer's sorted output. -/
def sortJava : Prop := FVATest.Certs.Sort.Java.claim

/-- Certificate: the TypeScript producer's sorted output. -/
def sortTs : Prop := FVATest.Certs.Sort.Ts.claim

/-- Certificate: a sorted output with duplicates. -/
def sortDuplicates : Prop := FVATest.Certs.Pos.Sorted.claim

/-- Certificate: the empty file as its own sorted output. -/
def sortEmpty : Prop := FVATest.Certs.Pos.Empty.claim

/-- Certificate: the toy compiler's output for `(x+1)`. -/
def compiled1 : Prop := FVATest.Certs.Compile.E1.claim

/-- Certificate: the toy compiler's output for `((x*x)-(3*x))`. -/
def compiled2 : Prop := FVATest.Certs.Compile.E2.claim

/-- Certificate: the toy compiler's output for `(((x+7)*(x-2))*100000)`. -/
def compiled3 : Prop := FVATest.Certs.Compile.E3.claim

/-- Certificate: the project relation `Reversed` on a small file. -/
def reversed : Prop := FVATest.Certs.Custom.Rev.claim

end FVATest.Certs
