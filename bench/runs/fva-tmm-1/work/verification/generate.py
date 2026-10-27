"""Untrusted certificate generator. All its output is checked by Lean/FVA."""
from pathlib import Path
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as F
import math
from functools import cache

ROOT = Path(__file__).resolve().parent.parent
xs = [[int(s) for s in line.split()] for line in (ROOT/'counts.tsv').read_text().splitlines()]
libs = [sum(row[j] for row in xs) for j in range(7)]
def lean(x):
    if isinstance(x,F): return f'({x.numerator} / {x.denominator})'
    if isinstance(x,(list,tuple)): return '['+', '.join(map(lean,x))+']'
    return str(x)
def ds(path):
    return [(int(s.replace('.','')),len(s.split('.')[1])) for s in (ROOT/path).read_text().splitlines()]
def decs(v): return '['+', '.join(f'({m}, {p})' for m,p in v)+']'
@cache
def selected(j):
    ps=[(row[j],row[3]) for row in xs if row[j] and row[3]]
    ms=[F(a,b) for a,b in ps]; aa=[a*b for a,b in ps]; n=len(ps)
    def keep(v,x,p,q):
        rank=2*sum(z<x for z in v)+sum(z==x for z in v)+1
        lo=n*p//q+1; hi=n+1-lo
        return 2*lo <= rank <= 2*hi
    return [(a,b) for a,b in ps if keep(ms,F(a,b),3,10) and keep(aa,a*b,1,20)]

data='''import Proofs.Spec
import FVA.Proof.Cert.Sort
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Witness
'''
data+='def matrix : List (List Nat) := '+lean(xs)+'\n'
data+='def edger : List Decimal := '+decs(ds('edger-factors.txt'))+'\n'
data+='def rnanorm : List Decimal := '+decs(ds('rnanorm-factors.txt'))+'\n'
data+='''
theorem blob_eq (b : FVA.Cert.Blob) (bs : List UInt8)
    (h : FVA.Cert.Impl.takeBytes bs b.len b.bytes = some (0, 0)) : b.data = bs := by
  have he := (FVA.Cert.Impl.takeBytes_sound h).2
  simpa [FVA.Cert.Blob.data, FVA.Wasm.Binary.leBytes] using he

def fastDecimal (n : Nat) : List UInt8 := FVA.Cert.Impl.digitsOf (n+1) n []
theorem fastDecimal_eq (n : Nat) : fastDecimal n = FVA.Cert.decimal n := by
  simpa [fastDecimal] using FVA.Cert.Impl.digitsOf_eq n n [] (FVA.Cert.Impl.lt_ten_pow_succ n)
def fastFactorText (ds : List Decimal) : List UInt8 := ds.flatMap fun d =>
  fastDecimal (d.1 / 10 ^ d.2) ++ [46] ++
  List.replicate (d.2 - (fastDecimal (d.1 % 10 ^ d.2)).length) 48 ++
  fastDecimal (d.1 % 10 ^ d.2) ++ [10]
def fastMatrixText (xs : List (List Nat)) : List UInt8 :=
  xs.flatMap fun row => List.intercalate [9] (row.map fastDecimal) ++ [10]
theorem fastFactorText_eq (ds : List Decimal) : fastFactorText ds = factorText ds := by
  unfold fastFactorText factorText
  apply congrArg (fun f => ds.flatMap f)
  funext d
  simp only [decimalText, fastDecimal_eq]
theorem fastMatrixText_eq (xs : List (List Nat)) : fastMatrixText xs = matrixText xs := by
  have hf : fastDecimal = FVA.Cert.decimal := funext fastDecimal_eq
  simp only [fastMatrixText, matrixText, hf]
theorem counts_eq : Counts.blob.data = matrixText matrix :=
  (blob_eq Counts.blob (fastMatrixText matrix) (by decide +kernel)).trans (fastMatrixText_eq matrix)
theorem edger_eq : Edger.blob.data = factorText edger :=
  (blob_eq Edger.blob (fastFactorText edger) (by decide +kernel)).trans (fastFactorText_eq edger)
theorem rnanorm_eq : Rnanorm.blob.data = factorText rnanorm :=
  (blob_eq Rnanorm.blob (fastFactorText rnanorm) (by decide +kernel)).trans (fastFactorText_eq rnanorm)
'''
for j in range(7):
    ps=selected(j)
    data+=f'def ps{j} : List (Nat × Nat) := '+ '['+', '.join(f'({a}, {b})' for a,b in ps)+']\n'
    allps=[(row[j],row[3]) for row in xs if row[j] and row[3]]
    data+=f'def allps{j} : List (Nat × Nat) := ['+', '.join(f'({a}, {b})' for a,b in allps)+']\n'
    data+=f'def ms{j} : List ℚ := '+lean([F(a,b) for a,b in allps])+'\n'
    data+=f'def aa{j} : List ℚ := '+lean([a*b for a,b in allps])+'\n'
    data+=f'theorem pairs{j} : pairs matrix {j} 3 = allps{j} := by decide +kernel\n'
    data+=f'theorem ms_eq{j} : allps{j}.map (fun p => (p.1 : ℚ) / p.2) = ms{j} := by decide +kernel\n'
    data+=f'theorem aa_eq{j} : allps{j}.map (fun p => ((p.1 * p.2 : Nat) : ℚ)) = aa{j} := by decide +kernel\n'
    names=[]
    for vsname, vals, num, den in [(f'ms{j}',[F(a,b) for a,b in allps],3,10),(f'aa{j}',[F(a*b) for a,b in allps],1,20)]:
        data+=f'theorem {vsname}_length : {vsname}.length = {len(vals)} := by decide +kernel\n'
        for k,x in enumerate(sorted(set(vals))):
            rank=2*sum(v<x for v in vals)+sum(v==x for v in vals)+1
            lower=len(vals)*num//den+1; upper=len(vals)+1-lower
            keep='true' if 2*lower <= rank <= 2*upper else 'false'
            rn=f'{vsname}_rank{k}'; kn=f'{vsname}_keep{k}'; names.append(kn)
            data+=f'theorem {rn} : rank2 {vsname} {lean(x)} = {rank} := by decide +kernel\n'
            data+=f'theorem {kn} : rankKeep {vsname} {lean(x)} {num} {den} = {keep} := by\n  unfold rankKeep\n  rw [{vsname}_length, {rn}]\n  decide +kernel\n'
    data+=f'theorem selected{j} : selected matrix {j} 3 = ps{j} := by\n  unfold selected\n  rw [pairs{j}]\n  dsimp only\n  rw [ms_eq{j}, aa_eq{j}]\n  norm_num [allps{j}, ps{j}, List.filter_cons, List.filter_nil, '+', '.join(names)+']\n'
for j,l in enumerate(libs):
    data+=f'theorem lib{j} : library matrix {j} = {l} := by decide +kernel\n'
for j,l in enumerate(libs):
    vs=sorted(row[j] for row in xs)
    q=F(vs[339]+3*vs[340],4*l)
    data+=f'theorem q{j} : quartile matrix {j} = {lean(q)} := by\n  unfold quartile\n  rw [List.mergeSort_eq_insertionSort]\n  decide +kernel\n'
data+='theorem ref_ok : referenceOK matrix 3 := by\n  norm_num [referenceOK, List.range_succ, '+', '.join('q'+str(j) for j in range(7))+']\n'
data+='theorem matrix_ok : matrixOK matrix := by\n'
data+='  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ref_ok, ?_⟩\n'
data+='  intro j hj\n  simp only [List.mem_range] at hj\n  interval_cases j\n'
for j in range(7):
    data+=f'  · rw [selected{j}, lib{j}'+ (', lib3' if j!=3 else '') + ']; decide +kernel\n'
data+='end Proofs.Witness\n'
head=data[:data.index('def ps0')]
starttail=data.index('theorem lib0')
startok=data.index('theorem matrix_ok')
(ROOT/'Proofs/WitnessData.lean').write_text(head+data[starttail:startok]+'end Proofs.Witness\n')
for j in range(7):
    begin=data.index(f'def ps{j}')
    end=data.index(f'def ps{j+1}') if j<6 else starttail
    selected_start=data.index(f'theorem selected{j}',begin)
    settings='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Witness\n'
    ranks=data[begin:selected_start].replace(':= by decide +kernel', ':= by kernel_rfl')
    (ROOT/f'Proofs/Ranks{j}.lean').write_text('import Proofs.WitnessData\n'+settings+ranks+'end Proofs.Witness\n')
    selection=f'import Proofs.Ranks{j}\n'+settings.replace('namespace Proofs.Witness\n','set_option linter.unusedSimpArgs false\nnamespace Proofs.Witness\n')+data[selected_start:end]+'end Proofs.Witness\n'
    line=next(l for l in selection.splitlines() if l.startswith('  norm_num ['))
    names=line[len('  norm_num ['):-1].split(', ')[4:]
    pre=''.join(f'  have h_{n} := {n}\n' for n in names)
    pre+='  simp only [div_one] at '+' '.join('h_'+n for n in names)+'\n'
    newline='  norm_num ['+', '.join(line[len('  norm_num ['):-1].split(', ')[:4]+['h_'+n for n in names])+']'
    selection=selection.replace(line,pre+newline)
    (ROOT/f'Proofs/Selection{j}.lean').write_text(selection)
(ROOT/'Proofs/Witness.lean').write_text(''.join(f'import Proofs.Selection{j}\n' for j in range(7))+'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Witness\n'+data[startok:])

with localcontext() as ctx:
    ctx.prec=80
    def dec(q): return Decimal(q.numerator)/Decimal(q.denominator)
    def bound(v,scale=10**9):
        return (int((v*scale).to_integral_value(rounding=ROUND_FLOOR)),int((v*scale).to_integral_value(rounding=ROUND_CEILING)))
    keys=sorted(set(range(43))|set(libs))
    logs={n:bound(Decimal(n).ln()) if n else (0,0) for n in keys}
    out='''import Proofs.Bounds
import Proofs.Witness
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Numeric
'''
    for name,idx in [('lb',0),('ub',1)]:
        out+=f'def {name} (n : Nat) : ℚ :=\n  match n with\n'
        for n in keys: out+=f'  | {n} => {logs[n][idx]} / 1000000000\n'
        out+= '  | _ => '+('0' if idx==0 else 'n')+'\n'
    for n in keys:
        out+=f'theorem log{n} : (lb {n} : ℝ) ≤ Real.log {n} ∧ Real.log {n} ≤ (ub {n} : ℝ) := by\n'
        if n<=1: out+='  norm_num [lb, ub]\n'
        else:
            k=n.bit_length()-1
            out+=f'  exact log_certificate {n} {k} _ _ (by norm_num) (by decide +kernel) (by decide +kernel)\n'
    out+='theorem log_bounds (n : Nat) : (lb n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (ub n : ℝ) := by\n'
    out+='  by_cases h : n ≤ 42\n  · interval_cases n\n'
    for n in range(43): out+=f'    · simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using log{n}\n'
    for n in keys[43:]:
        out+=f'  by_cases h{n} : n = {n}\n  · subst n; exact log{n}\n'
    out+='  simp only [lb, ub]\n'
    # simp only unfolds match to nested ifs; use split_ifs? fallback matches Nat literals
    out=out.removesuffix('  simp only [lb, ub]\n')
    out+='  have hlo : lb n = 0 := by unfold lb; split <;> first | rfl | omega\n'
    out+='  have hhi : ub n = n := by unfold ub; split <;> first | rfl | omega\n'
    out+='  rw [hlo, hhi]\n  exact ⟨by simpa using Real.log_natCast_nonneg n, by exact_mod_cast Real.log_le_self (Nat.cast_nonneg n)⟩\n'
    coeff='import Proofs.Witness\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Numeric\n'
    raw=[]
    for j in range(7):
        ps=selected(j)
        weights=[1/(1/F(a)-1/F(libs[j])+1/F(b)-1/F(libs[3])) for a,b in ps]
        total=sum(weights)
        cs=[(c/total,n) for (a,b),w in zip(ps,weights) for c,n in [(w,a),(-w,b)]]+[(F(1),libs[3]),(F(-1),libs[j])]
        low=sum(c*F(logs[n][0 if c>=0 else 1],10**9) for c,n in cs)
        high=sum(c*F(logs[n][1 if c>=0 else 0],10**9) for c,n in cs)
        # rounded outward at 1e-7
        l=low.numerator*10**7//low.denominator
        u=-((-high.numerator*10**7)//high.denominator)
        raw.append((F(l,10**7),F(u,10**7)))
        out+=f'\ntheorem raw{j} : ({lean(raw[-1][0])} : ℝ) ≤ rawLog Witness.matrix {j} 3 ∧\n    rawLog Witness.matrix {j} 3 ≤ ({lean(raw[-1][1])} : ℝ) := by\n'
        coeff+=f'def cs{j} : List (ℚ × Nat) := ['+', '.join(f'({lean(c)}, {n})' for c,n in cs)+']\n'
        coeff+=f'theorem coeffs{j} : rawCoeffs Witness.matrix {j} 3 = cs{j} := by\n'
        coeff+=f'  unfold rawCoeffs\n  rw [Witness.selected{j}, Witness.lib{j}'+(', Witness.lib3' if j!=3 else '')+']\n'
        coeff+='  dsimp only\n'
        coeff+=f'  have hw : (Witness.ps{j}.map (weight {libs[j]} {libs[3]})).sum = {lean(total)} := by kernel_rfl\n'
        coeff+='  rw [hw]\n  kernel_rfl\n'
        if j == 3:
            out+='  rw [raw3_zero]\n  constructor <;> norm_num\n'
            continue
        out+=f'  have h := evalLogs_bounds lb ub log_bounds cs{j}\n'
        out+=f'  change _ ≤ evalLogs (rawCoeffs Witness.matrix {j} 3) ∧ evalLogs (rawCoeffs Witness.matrix {j} 3) ≤ _\n  rw [coeffs{j}]\n'
        out+=f'  have hl : ({lean(raw[-1][0])} : ℚ) ≤ (cs{j}.map (lowerTerm lb ub)).sum := by decide +kernel\n'
        out+=f'  have hu : (cs{j}.map (upperTerm lb ub)).sum ≤ ({lean(raw[-1][1])} : ℚ) := by decide +kernel\n'
        out+="  have hl' := (Rat.cast_le (K := ℝ)).mpr hl\n"
        out+="  have hu' := (Rat.cast_le (K := ℝ)).mpr hu\n"
        out+="  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, Rat.cast_neg] at hl' hu'\n"
        out+='  exact ⟨le_trans hl\' h.1, le_trans h.2 hu\'⟩\n'
    for j in range(7):
        if j == 3: continue
        begin=coeff.index(f'def cs{j} :')
        end=coeff.index(f'def cs{j+1} :') if j<6 else len(coeff)
        body=coeff[begin:end]
        line=next(l for l in body.splitlines() if l.startswith('  have hw :'))
        theorem=line.replace('  have hw :',f'theorem weightSum{j} :')
        (ROOT/f'Proofs/Weights{j}.lean').write_text(f'import Proofs.Selection{j}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Numeric\n'+theorem+'\nend Proofs.Numeric\n')
        body=body.replace(line,f'  have hw := weightSum{j}').replace('  rw [hw]\n  kernel_rfl',f'  rw [hw]\n  change _ = cs{j}\n  kernel_rfl')
        (ROOT/f'Proofs/Coefficients{j}.lean').write_text(f'import Proofs.Weights{j}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Numeric\n'+body+'end Proofs.Numeric\n')
    (ROOT/'Proofs/Coefficients.lean').write_text(''.join(f'import Proofs.Coefficients{j}\n' if j != 3 else 'import Proofs.SelfComparison\n' for j in range(7))+'import Proofs.Witness\n')
    # Generate real factor enclosures at 1e-6, independently verified with log certificates.
    centers=[]
    for j in range(7):
        ps=selected(j); weights=[1/(1/F(a)-1/F(libs[j])+1/F(b)-1/F(libs[3])) for a,b in ps]
        rv=sum(dec(w)*(Decimal(a).ln()-Decimal(b).ln()) for (a,b),w in zip(ps,weights))/dec(sum(weights))+Decimal(libs[3]).ln()-Decimal(libs[j]).ln()
        centers.append(rv)
    avg=sum(centers)/7
    fact=[]
    for j,rv in enumerate(centers):
        f=(rv-avg).exp()
        # broad 1e-6 interval enough for accumulated 1e-7 log errors
        mid=int(f*10**6)
        a=F(mid-1,10**6); b=F(mid+2,10**6); fact.append((a,b))
        al,au=bound(dec(a).ln()); bl,bu=bound(dec(b).ln())
        out+=f'\ntheorem factor{j} : ({lean(a)} : ℝ) ≤ tmm Witness.matrix {j} 3 ∧\n    tmm Witness.matrix {j} 3 ≤ ({lean(b)} : ℝ) := by\n'
        out+=f'  have ha := log_certificate ({lean(a)}) 0 ({al}/1000000000) ({au}/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)\n'
        out+=f'  have hb := log_certificate ({lean(b)}) 0 ({bl}/1000000000) ({bu}/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)\n'
        out+='  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb\n'
        for k in range(7): out+=f'  have h{k} := raw{k}\n'
        out+=f'  have hbound : (({lean(a)[1:-1]} : ℚ) : ℝ) ≤ tmm Witness.matrix {j} 3 ∧\n      tmm Witness.matrix {j} 3 ≤ (({lean(b)[1:-1]} : ℚ) : ℝ) := by\n'
        out+=f'    apply exp_bounds (factorLog Witness.matrix {j} 3) ({lean(a)[1:-1]} : ℚ) ({lean(b)[1:-1]} : ℚ) (by norm_num) (by norm_num)\n'
        out+='    all_goals\n      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]\n      unfold factorLog\n      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]\n      linarith [ha.1, ha.2, hb.1, hb.2]\n'
        out+='  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound\n'
        print(j+1,'kept',len(selected(j)), 'raw',raw[j], 'factor',f, 'enclosure',a,b)
    out+='end Proofs.Numeric\n'
    idx=out.index('\ntheorem raw0')
    (ROOT/'Proofs/LogBounds.lean').write_text(out[:idx].replace('import Proofs.Witness\n','')+'\nend Proofs.Numeric\n')
    factor=out.index('\ntheorem factor0')
    for j in range(7):
        begin=out.index(f'\ntheorem raw{j}')
        end=out.index(f'\ntheorem raw{j+1}') if j<6 else factor
        dep=f'Proofs.Coefficients{j}' if j!=3 else 'Proofs.SelfComparison'
        (ROOT/f'Proofs/Raw{j}.lean').write_text(f'import Proofs.LogBounds\nimport {dep}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Numeric\n'+out[begin:end]+'end Proofs.Numeric\n')
    (ROOT/'Proofs/Numeric.lean').write_text('import Proofs.LogBounds\nimport Proofs.Coefficients\n'+''.join(f'import Proofs.Raw{j}\n' for j in range(7))+'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Proofs.Numeric\n'+out[factor:])
    (ROOT/'verification/enclosures.txt').write_text('\n'.join(f'{i+1}: {a} <= TMM <= {b}' for i,(a,b) in enumerate(fact))+'\n')
