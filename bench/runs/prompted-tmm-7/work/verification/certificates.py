"""Untrusted certificate search: every emitted claim is checked by Lean's kernel."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
x=[list(map(int,l.split())) for l in Path('counts.tsv').read_text().splitlines()]
ns=list(map(sum,zip(*x)))
def lit(q):
    q=F(q)
    return f'({q.numerator} / {q.denominator} : ℚ)'
def listlit(xs):return '['+', '.join(xs)+']'
def pairlit(p):return '('+', '.join(map(lit,p))+')'
def bounds(q):
    z=(q-1)/(q+1)
    p=z+z**3/3+z**5/5+z**7/7
    e=abs(z)**9/(1-z*z)
    return 2*(p-e),2*(p+e)
def down(q):return F(q.numerator*1000000//q.denominator,1000000)
def up(q):return -down(-q)
out='''import Proofs.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.style.longLine false
namespace Verify
'''
out+='def data : List (List ℕ) := '+repr(x)+'\n'
out+='theorem matrix_eq : matrix = data := by decide +kernel\n'
out+='theorem matrix_shape : matrix.length = 454 ∧ (∀ r ∈ matrix, r.length = 7 ∧ r.any (· > 0)) := by\n  rw [matrix_eq]; decide +kernel\n'
out+='theorem libraries : (List.range 7).map lib = [1261,621,755,1097,1916,1136,1219] := by\n  decide +kernel\n'
# Include intended a_trim=.05 and literal docstring a_trim=m_trim=.3.
for anum,aden,tag,ab in [
 (1,20,'default',[(19,20),(292,293),(182,183),(-1,1),(-160,-159),(-26,-25),(1,2)]),
 (3,10,'literal',[(-38,-37),(416,417),(225,226),(-1,1),(-134,-133),(-17,-16),(68,69)])]:
 for i in range(7):
    ps=[(r[i],r[3]) for r in x if r[i] and r[3]]
    def rank(p,key):return 2*sum(key(q)<key(p) for q in ps)+sum(key(q)==key(p) for q in ps)+1
    n=len(ps);ml=n*3//10+1;al=n*anum//aden+1
    selected=[p for p in ps if 2*ml<=rank(p,lambda q:F(*q))<=2*(n+1-ml) and 2*al<=rank(p,lambda q:q[0]*q[1])<=2*(n+1-al)]
    ts=[]
    for (o,r),count in Counter(selected).items():
        ts.append((F(o*ns[3],r*ns[i]), count/(F(1,o)+F(1,r)-F(1,ns[i])-F(1,ns[3]))))
    a,b=[F(t,1000) for t in ab[i]]
    cs=[(down(w*(bounds(q)[0]-a)),up(w*(bounds(q)[1]-b))) for q,w in ts]
    assert sum(l for l,u in cs)>0 and sum(u for l,u in cs)<0
    name=f'{tag}_{i}'
    out+=f'def ts_{name} : List Term := '+listlit(map(pairlit,ts))+'\n'
    out+=f'theorem terms_{name} : terms {i} {anum} {aden} = ts_{name} := by\n  simp only [terms, kept, pairs, lib, matrix_eq]; decide +kernel\n'
    out+=f'def cs_{name} : List Cert := '+listlit(map(pairlit,cs))+'\n'
    out+=f'theorem cert_{name} : leaves ts_{name} {lit(a)} {lit(b)} cs_{name} := by decide +kernel\n'
    out+=f'theorem weight_{name} : 0 < weight ts_{name} := by decide +kernel\n'
    out+=f'theorem sign_{name} : 0 ≤ (cs_{name}.map Prod.fst).sum ∧ (cs_{name}.map Prod.snd).sum ≤ 0 := by decide +kernel\n'
    out+=f'theorem bound_{name} : ({lit(a)} : ℝ) ≤ rawLog {anum} {aden} {i} ∧ rawLog {anum} {aden} {i} ≤ ({lit(b)} : ℝ) := by\n'
    out+=f'  unfold rawLog\n  rw [terms_{name}]\n  exact mean_bounds _ _ _ _ cert_{name} weight_{name} sign_{name}.1 sign_{name}.2\n'
out+='end Verify\n'
Path('Proofs/Certificates.lean').write_text(out)
