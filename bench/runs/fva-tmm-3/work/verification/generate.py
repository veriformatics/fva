"""Untrusted witness printer. Lean checks all its output; no numeric result is assumed."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import math
root = Path(__file__).resolve().parent.parent
x = [[int(v) for v in l.split()] for l in (root/'counts.tsv').read_text().splitlines()]
libs = [sum(row[j] for row in x) for j in range(7)]
def ds(name):
    out=[]
    for line in (root/name).read_text().splitlines():
        a,b=line.split('.')
        out.append((int(a+b),len(b)))
    return out

def lean_list(x):
    if isinstance(x,list): return '['+', '.join(map(lean_list,x))+']'
    if isinstance(x,tuple): return '('+', '.join(map(lean_list,x))+')'
    return str(x)

def make_pairs(j):
    ps=[(row[j],row[3]) for row in x if row[j] and row[3]]
    n=len(ps)
    def rm(p):
        return 2*sum(a*p[1]<p[0]*b for a,b in ps)+sum(a*p[1]==p[0]*b for a,b in ps)+1
    def ra(p):
        return 2*sum(a*b<p[0]*p[1] for a,b in ps)+sum(a*b==p[0]*p[1] for a,b in ps)+1
    return [p for p in ps if 2*(3*n//10+1)<=rm(p)<=2*(n-3*n//10) and 2*(n//20+1)<=ra(p)<=2*(n-n//20)]

w=['import Proofs.Spec','import Mathlib.Tactic','', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '', 'namespace Proofs', '', 'def matrix : Matrix := '+lean_list(x), '', 'def edgeValues : List Decimal := '+lean_list(ds('edger-factors.txt')), '', 'def rnaValues : List Decimal := '+lean_list(ds('rnanorm-factors.txt')), '', 'theorem counts_bytes : Counts.blob.data = countBytes matrix := by kernel_rfl', 'theorem edge_bytes : Edge.blob.data = factorBytes edgeValues := by kernel_rfl', 'theorem rna_bytes : RNA.blob.data = factorBytes rnaValues := by kernel_rfl', 'theorem matrix_shape : matrix.length = 454 ∧ (∀ row ∈ matrix, row.length = 7) := by decide +kernel','theorem quartiles_eq : (List.range 7).map (quartile matrix) = [4/1261, 2/621, 2/755, 3/1097, 5/1916, 3/1136, 3/1219] := by kernel_rfl', 'theorem reference_eq : reference matrix = 3 := by', '  unfold reference', '  have hn : (matrix.headD []).length = 7 := by kernel_rfl', '  rw [hn]', '  dsimp only', '  rw [quartiles_eq]', '  decide +kernel', '']
for j in range(7):
    ps=make_pairs(j)
    positive=[(row[j],row[3]) for row in x if row[j] and row[3]]
    w += [f'def positive{j} : List (Nat × Nat) := '+lean_list(positive), f'theorem positive_eq{j} : positivePairs matrix {j} 3 = positive{j} := by kernel_rfl']
    w += [f'def pairs{j} : List (Nat × Nat) := '+lean_list(ps), f'theorem kept{j} : keptPairs matrix {j} 3 = pairs{j} := by', '  unfold keptPairs', f'  rw [positive_eq{j}]', '  kernel_rfl', f'theorem lib{j} : library matrix {j} = {libs[j]} := by decide +kernel','']
w += ['end Proofs','']
(root/'Proofs/Witness.lean').write_text('\n'.join(w))

nums=list(range(1,43))+sorted(set(libs))
with localcontext() as c:
    c.prec=70
    bounds={n:(int((Decimal(n).ln()*10**6).to_integral_value(rounding='ROUND_FLOOR'))-1,int((Decimal(n).ln()*10**6).to_integral_value(rounding='ROUND_CEILING'))+1) for n in nums}
logfile=['import Proofs.Bounds','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace Proofs', '']
for n,(lo,hi) in bounds.items():
    k=n.bit_length()-1
    q=F(n,2**k)
    logfile += [f'theorem ln{n} : (({lo} : ℚ)/1000000 : ℝ) ≤ Real.log {n} ∧ Real.log {n} ≤ (({hi} : ℚ)/1000000 : ℝ) := by', '  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Nat.cast_ofNat, Nat.cast_one, Rat.cast_one] using',f'    (log_certificate {n} {k} ({q.numerator}/{q.denominator}) ({lo}/1000000) ({hi}/1000000)', '      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel))', '']
logfile += ['def logLo (n : Nat) : ℚ :=', '  match n with']
logfile += [f'  | {n} => {lo}/1000000' for n,(lo,hi) in bounds.items()]
logfile += ['  | _ => 0', '', 'def logHi (n : Nat) : ℚ :=', '  match n with']
logfile += [f'  | {n} => {hi}/1000000' for n,(lo,hi) in bounds.items()]
logfile += ['  | _ => 0', '', 'def logDomain : List Nat := '+lean_list(nums), '', 'theorem log_bounds (n : Nat) (hn : n ∈ logDomain) :','    (logLo n : ℝ) ≤ Real.log n ∧ Real.log n ≤ (logHi n : ℝ) := by', '  simp only [logDomain, List.mem_cons, List.not_mem_nil, or_false] at hn', '  rcases hn with '+ ' | '.join(['rfl']*len(nums))]
logfile += [f'  · simpa [logLo, logHi] using ln{n}' for n in nums]
logfile += ['', 'end Proofs', '']
(root/'Proofs/Logs.lean').write_text('\n'.join(logfile))
print('matrix',len(x),'library sizes',libs,'kept',*[len(make_pairs(j)) for j in range(7)])

lo=[18,291,181,-1,-161,-27,0]
hi=[21,294,184,2,-158,-24,3]
sfile=['import Proofs.Witness','import Proofs.ScoreBounds','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace Proofs','']
for j in range(7):
    l,u=lo[j],hi[j]
    sfile += [f'theorem score{j}_bounds : (({l}/1000 : ℚ) : ℝ) ≤ score matrix {j} 3 ∧',f'    score matrix {j} 3 ≤ (({u}/1000 : ℚ) : ℝ) := by', '  unfold score', f'  simp only [kept{j}, lib{j}, lib3]',f'  exact weighted_bounds pairs{j} {libs[j]} 1097 ({l}/1000) ({u}/1000)', '    (by decide +kernel) (by decide +kernel) (by decide +kernel)', '    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)', '']
sfile += ['theorem factor_lower : (114/100 : ℝ) < factor matrix 2 := by', '  have h0 := score0_bounds', '  have h1 := score1_bounds', '  have h2 := score2_bounds', '  have h3 := score3_bounds', '  have h4 := score4_bounds', '  have h5 := score5_bounds', '  have h6 := score6_bounds', '  have he : (132/1000 : ℝ) < score matrix 2 3 -', '      ((List.range 7).map (fun k => score matrix k 3)).sum / 7 := by', '    norm_num [List.range_succ, List.map_cons, List.sum_cons] at *', '    linarith', '  have hs := series_bounds (57/50) (by norm_num) 10', '  have hu : series (57/50) 10 + remainder (57/50) 10 < (132/1000 : ℚ) := by decide +kernel', '  have hlog : Real.log (114/100 : ℝ) < 132/1000 := by', '    have huR : (((series (57/50) 10 + remainder (57/50) 10 : ℚ)) : ℝ) < ((132/1000 : ℚ) : ℝ) := Rat.cast_lt.mpr hu', '    have hh := lt_of_le_of_lt hs.2 huR', '    norm_num at hh ⊢', '    exact hh', '  unfold factor', '  rw [reference_eq]', '  exact (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 114/100)).mp (hlog.trans he)', '', 'end Proofs','']
(root/'Proofs/ScoreData.lean').write_text('\n'.join(sfile))
