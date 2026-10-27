exec(open('verification/generate.py').read().split("out='import")[0])
import math
out='import Proofs.Data\nimport Proofs.MeanBounds\n\nset_option Elab.async false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Verification\n\nattribute [local irreducible] refIndex kept library terms\n\n'
for i in range(7):
 ps=[(r[i],r[3]) for r in x if r[i]>0 and r[3]>0]; n=len(ps)
 def rank(p,key):
  val=key(p); return 2*sum(key(q)<val for q in ps)+sum(key(q)==val for q in ps)+1
 ks=[p for p in ps if 2*(n*3//10+1)<=rank(p,lambda p:Q(p[0],p[1]))<=2*(n-n*3//10) and 2*(n//20+1)<=rank(p,lambda p:p[0]*p[1])<=2*(n-n//20)]
 ts=[(1/(Q(1,o)-Q(1,libs[i])+Q(1,r)-Q(1,libs[3])),Q(o*libs[3],r*libs[i])) for o,r in ks]
 loInt, hiInt = [(19,20),(292,293),(182,183),(0,0),(-160,-158),(-26,-25),(1,2)][i]
 lo=Q(loInt,1000); hi=Q(hiInt,1000)
 out+=f'theorem terms_{i} : terms {i} = {lean(ts)} := by\n  delta terms\n  rewrite [kept_{i}]\n  simp only [List.map_cons, List.map_nil, weight, ratio, reference]\n  simp only [library_{i}, library_3]\n  norm_num\n\n'
 out+=f'theorem raw_{i} : (({lean(lo)} : ℚ) : ℝ) ≤ raw {i} ∧ raw {i} ≤ (({lean(hi)} : ℚ) : ℝ) := by\n'
 out+=f'  change (({lean(lo)} : ℚ) : ℝ) ≤ weightedLog (terms {i}) / (((terms {i}).map Prod.fst).sum : ℚ) ∧ weightedLog (terms {i}) / (((terms {i}).map Prod.fst).sum : ℚ) ≤ (({lean(hi)} : ℚ) : ℝ)\n'
 out+=f'  apply mean_bounds (terms {i}) {lean(lo)} {lean(hi)} <;> (rewrite [terms_{i}]; decide +kernel)\n\n'
 print(i,lo,hi)
out+='end Verification\n'
Path('Proofs/Numeric.lean').write_text(out)
