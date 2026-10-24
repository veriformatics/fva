# Produces rnanorm-factors.txt from counts.tsv (genes x samples) with RNAnorm 2.2.0.
import numpy as np
from rnanorm import TMM

m = np.loadtxt("counts.tsv", delimiter="\t", ndmin=2)
f = TMM().fit(m.T).get_norm_factors(m.T)
with open("rnanorm-factors.txt", "w") as out:
    out.write("".join(f"{float(x)!r}\n" for x in f))
