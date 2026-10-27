from pathlib import Path
from fractions import Fraction as Q
import json

x = [list(map(int, r.split())) for r in Path('counts.tsv').read_text().splitlines()]
libs = [sum(r[i] for r in x) for i in range(7)]
assert len(x)==454 and all(len(r)==7 and any(r) for r in x)
assert all(v>=0 for r in x for v in r)

def lean(v):
    if isinstance(v, tuple): return '('+', '.join(map(lean,v))+')'
    if isinstance(v, list): return '['+', '.join(map(lean,v))+']'
    if isinstance(v,Q): return f'({v.numerator} / {v.denominator})'
    return str(v)

def proof(name, statement, pre=''):
    return f'theorem {name} : {statement} := by\n  {pre}' + 'decide +kernel' + '\n\n'

out='import Proofs.Spec\n\nset_option Elab.async false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Verification\n\n'

out+=proof('shape',f'matrix.length = 454 ∧ matrix.all (fun r => r.length == 7 && r.any (0 < ·)) = true','rw [matrix]\n  ')
for i in range(7):
 out+=proof(f'library_{i}',f'library {i} = {libs[i]}','simp only [library, column, matrix]\n  ')
quartiles=[]
for i in range(7):
 col=sorted(r[i] for r in x); k=3*(len(col)-1)
 quartiles.append((Q(col[k//4])*(4-k%4)+Q(col[k//4+1])*(k%4))/(4*libs[i]))
 out+=proof(f'len_{i}',f'(column {i}).length = 454')
 out+=proof(f'qlow_{i}',f'kth (column {i}) 339 = {col[339]}')
 out+=proof(f'qhigh_{i}',f'kth (column {i}) 340 = {col[340]}')
 out+=f'theorem uq_{i} : uq {i} = {lean(quartiles[-1])} := by\n  norm_num [uq, len_{i}, qlow_{i}, qhigh_{i}, library_{i}]\n\n'
out += 'theorem reference : refIndex = 3 := by\n  norm_num [refIndex, uqMean, show List.range 7 = [0,1,2,3,4,5,6] from by decide, ' + ', '.join('uq_'+str(i) for i in range(7)) + ']\n\n'

for i in range(7):
 ps=[(r[i],r[3]) for r in x if r[i]>0 and r[3]>0]
 n=len(ps)
 def rank(p,key):
  val=key(p)
  return 2*sum(key(q)<val for q in ps)+sum(key(q)==val for q in ps)+1
 ks=[p for p in ps if 2*(n*3//10+1)<=rank(p,lambda p:Q(p[0],p[1]))<=2*(n-n*3//10) and 2*(n//20+1)<=rank(p,lambda p:p[0]*p[1])<=2*(n-n//20)]
 out+=proof(f'pairs_{i}',f'pairs {i} = {lean(ps)}', 'simp only [pairs, matrix, reference]\n  ')
 out+=proof(f'kept_{i}',f'kept {i} = {lean(ks)}', f'simp only [kept, pairs_{i}]\n  ')
 print(i, 'pairs',len(ps),'kept',len(ks))
out+='end Verification\n'
Path('Proofs/Data.lean').write_text(out)
