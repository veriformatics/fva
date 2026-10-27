from fractions import Fraction as Q
from pathlib import Path
from math import log, exp, floor, ceil
rows=[[int(s) for s in l.split('\t')] for l in Path('counts.tsv').read_text().splitlines()]
cs=list(map(list, zip(*[r for r in rows if any(r)]))); libs=list(map(sum,cs))
def uq(c):
 c=sorted(c); k=3*(len(c)-1); return Q(4-k%4,4)*c[k//4]+Q(k%4,4)*c[k//4+1]
qs=[uq(c)/sum(c) for c in cs]; av=sum(qs)/7
ref=min(range(7),key=lambda j:abs(qs[j]-av))
def rank2(vs,x):return 2*sum(v<x for v in vs)+sum(v==x for v in vs)+1
ess=[]
for j,c in enumerate(cs):
 pairs=[(a,b) for a,b in zip(c,cs[ref]) if a and b];n=len(pairs)
 ms=[Q(a*libs[ref],b*libs[j]) for a,b in pairs]; aa=[Q(a*b) for a,b in pairs]
 es=[]
 for a,b in pairs:
  m=Q(a*libs[ref],b*libs[j]); v=Q(1,a)+Q(1,b)-Q(1,libs[j])-Q(1,libs[ref])
  if 2*(n*3//10+1)<=rank2(ms,m)<=2*(n-n*3//10) and 2*(n//20+1)<=rank2(aa,Q(a*b))<=2*(n-n//20):es.append((m,1/v))
 ess.append(es)
def approx(q):
 z=(q-1)/(q+1);return 2*sum(z**(2*i+1)/(2*i+1) for i in range(4))
def error(q):
 z=(q-1)/(q+1);return 2*abs(z)**9/(1-z*z)
def bounds(es):
 w=sum(w for _,w in es)
 return (sum(v*(approx(q)-error(q)) for q,v in es)/w,sum(v*(approx(q)+error(q)) for q,v in es)/w)
bs=[bounds(es) for es in ess]
intervals=[(Q(floor(l*100000),100000),Q(ceil(h*100000),100000)) for l,h in bs]
def rat(q):return f'({q.numerator} / {q.denominator} : ℚ)' if q>=0 else f'(-{abs(q.numerator)} / {q.denominator} : ℚ)'
def array(a,f):return '['+', '.join(map(f,a))+']'
def pair(p):return '('+rat(p[0])+', '+rat(p[1])+')'
text='import Proofs.Bounds\nimport Proofs.Counts\nimport FVA.Proof.Decode.Pack\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Data\n'
text+='def inputBytes : List UInt8 := '+array(Path('counts.tsv').read_bytes(),str)+'\n'
text+='theorem pack_eq : FVA.Wasm.Binary.pack inputBytes = Counts.bytes := by kernel_rfl\n'
text+='theorem len_eq : inputBytes.length = Counts.len := by kernel_rfl\n'
text+='theorem data_eq : Counts.blob.data = inputBytes := by\n  change FVA.Wasm.Binary.leBytes Counts.len Counts.bytes = inputBytes\n  rw [← pack_eq, ← len_eq, FVA.Wasm.Binary.leBytes_pack]\n'
text+='def rows : List (List Nat) := '+array(rows,lambda r:array(r,str))+'\n'
text+='theorem rows_parsed : Model.matrix inputBytes = rows := by kernel_rfl\n'
text+='theorem rows_eq : Model.matrix Counts.blob.data = rows := by rw [data_eq, rows_parsed]\n'
text+='def cs : List (List Nat) := '+array(cs,lambda r:array(r,str))+'\n'
for j,c in enumerate(cs):
 text+=f'def c{j} : List Nat := '+array(c,str)+'\n'
 text+=f'theorem sum{j} : c{j}.sum = {sum(c)} := by kernel_rfl\n'
 text+=f'theorem uq{j} : Model.uq c{j} = '+rat(uq(c))+' := by kernel_rfl\n'
text+='theorem nonzero : rows.filter (fun r => r.any (· > 0)) = rows := by kernel_rfl\n'
text+='theorem columns_eq : Model.columns rows = cs := by kernel_rfl\n'
text+='theorem cs_eq : cs = ['+', '.join(f'c{j}' for j in range(7))+'] := by kernel_rfl\n'
text+='theorem ref_eq : Model.reference cs = 3 := by\n  unfold Model.reference\n  rw [cs_eq]\n  simp only [List.map_cons, List.map_nil, '+', '.join(f'uq{j}' for j in range(7))+']\n  decide +kernel\n'
for j,es in enumerate(ess):
 text+=f'def e{j} : List (ℚ × ℚ) := '+array(es,pair)+'\n'
 text+=f'theorem e{j}_eq : Model.entries c{j} c3 = e{j} := by\n  unfold Model.entries\n  simp only [sum{j}, sum3]\n  kernel_rfl\n'
text+='def es : List (List (ℚ × ℚ)) := ['+', '.join(f'e{j}' for j in range(7))+']\n'
es_proof='theorem es_eq : Model.samples Counts.blob.data = es := by\n  unfold Model.samples\n  rw [rows_eq, nonzero]\n  dsimp only\n  rw [columns_eq, ref_eq, cs_eq]\n  change [Model.entries c0 c3, Model.entries c1 c3, Model.entries c2 c3, Model.entries c3 c3, Model.entries c4 c3, Model.entries c5 c3, Model.entries c6 c3] = es\n  rw ['+', '.join(f'e{j}_eq' for j in range(7))+']\n  rfl\n'
text+='def intervals : List (ℚ × ℚ) := '+array(intervals,pair)+'\n'
for j in range(7):
 text+=f'theorem bounds{j} : Bounds.good e{j} ∧ (intervals[{j}]!).1 ≤ Bounds.lower e{j} ∧ Bounds.upper e{j} ≤ (intervals[{j}]!).2 := by decide +kernel\n'
text+='end Proofs.Data\n'
Path('Proofs/Raw.lean').write_text(text)
Path('Proofs/Data.lean').write_text('import Proofs.Raw\nnamespace Proofs.Data\n'+es_proof+'end Proofs.Data\n')
print('reference (one based)',ref+1,'libraries',libs)
print('kept',list(map(len,ess)))
print('log intervals',intervals)
ss=[sum(float(w)*log(float(q)) for q,w in es)/sum(float(w) for _,w in es) for es in ess]; avg=sum(ss)/7
print('exact-real approximation',[exp(s-avg) for s in ss])
