"""Auxiliary numeric evidence, separate from the Lean proofs. Requires NumPy."""
from fractions import Fraction as F
import numpy as np
x = np.loadtxt('counts.tsv', dtype=int)
x = x[np.any(x, axis=1)]
libs=x.sum(0)
q=np.quantile(x,.75,axis=0)/libs
ref=int(np.argmin(abs(q-q.mean())))
def ranks(v):
    return np.array([1+sum(w<t for w in v)+(sum(w==t for w in v)-1)/2 for t in v])
raw=[[],[]]
print('Library sizes:', libs.tolist(), 'reference sample:', ref+1)
for j in range(7):
    sel=(x[:,j]>0)&(x[:,ref]>0)
    a=x[sel,j]; b=x[sel,ref]; n=len(a)
    rr=a/libs[j]; rt=b/libs[ref]
    m=np.log2(rr/rt); aa=np.log2(rr*rt)/2
    w=(1-rr)/a+(1-rt)/b
    for mode in range(2):
        rm=ranks(m if mode else [F(int(v),int(z)) for v,z in zip(a,b)])
        ra=ranks(aa if mode else [int(v)*int(z) for v,z in zip(a,b)])
        keep=(rm>=3*n//10+1)&(rm<=n-3*n//10)&(ra>=n//20+1)&(ra<=n-n//20)
        raw[mode].append(2**(sum(m[keep]/w[keep])/sum(1/w[keep])))
        print('sample',j+1,['exact ranks','NumPy ranks'][mode],'retained',int(sum(keep)))
f=np.array(raw).T
f/=np.exp(np.log(f).mean(0))
e=np.loadtxt('edger-factors.txt');r=np.loadtxt('rnanorm-factors.txt')
assert max(abs(f[:,1]-r))<1e-12
print('sample   exact-rank approximation   shipped edgeR   shipped RNAnorm')
for i in range(7): print(i+1,*(f'{v:.17g}' for v in [f[i,0],e[i],r[i]]))
print('NumPy formula replay: max absolute error',max(abs(f[:,1]-r)))
print('Shipped absolute differences:',abs(e-r).tolist())
