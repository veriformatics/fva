"""Untrusted proof-data generator. Lean checks all its claimed facts against blobs."""
from pathlib import Path
from fractions import Fraction as F

matrix = [list(map(int, line.split('\t'))) for line in Path('counts.tsv').read_text().splitlines()]

def decimals(path):
    result = []
    for line in Path(path).read_text().splitlines():
        whole, fraction = line.split('.')
        result.append(f'⟨{int(whole)}, {int(fraction)}, {len(fraction)}⟩')
    return '[' + ', '.join(result) + ']'

def qstr(q):
    return f'({q.numerator}/{q.denominator})'

pairs = [(row[2], row[3]) for row in matrix if row[2] > 0 and row[3] > 0]
n = len(pairs)

def rank2(xs, v):
    return 2 * sum(x < v for x in xs) + sum(x == v for x in xs) + 1

ms = [F(a, b) for a, b in pairs]
as_ = [a*b for a, b in pairs]
retained = [p for p in pairs
    if 2*(n*3//10+1) <= rank2(ms, F(*p)) <= 2*(n-n*3//10)
    and 2*(n//20+1) <= rank2(as_, p[0]*p[1]) <= 2*(n-n//20)]

def lean_pairs(ps):
    return '[' + ', '.join(f'({a}, {b})' for a,b in ps) + ']'

cols = list(zip(*matrix))
libs = list(map(sum, cols))
qs = []
for col, lib in zip(cols, libs):
    cs = sorted(col)
    h = 3*(len(cs)-1)
    qs.append((F(cs[h//4]) + F(h%4,4)*(cs[h//4+1]-cs[h//4]))/lib)

text = '''import Proofs.Spec
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs
open TMM

'''
text += 'def matrix : List (List Nat) := [\n' + ',\n'.join('  ['+', '.join(map(str,row))+']' for row in matrix) + '\n]\n\n'
text += 'def edger : List Dec := ' + decimals('edger-factors.txt') + '\n'
text += 'def rnanorm : List Dec := ' + decimals('rnanorm-factors.txt') + '\n'
text += 'def kept : List (Nat × Nat) := ' + lean_pairs(retained) + '\n\n'
text += '''theorem counts_bytes : Counts.blob.data = matrixBytes matrix := by decide +kernel
theorem edger_bytes : Edger.blob.data = factorBytes edger := by decide +kernel
theorem rnanorm_bytes : RNAnorm.blob.data = factorBytes rnanorm := by decide +kernel

theorem matrix_length : matrix.length = 454 := by decide +kernel
theorem matrix_shape : ∀ row ∈ matrix, row.length = 7 := by decide +kernel
'''
text += 'theorem libraries : (List.range 7).map (library matrix) = [' + ', '.join(map(str,libs)) + '] := by decide +kernel\n'
text += 'theorem quartiles_eq : quartiles matrix = [' + ', '.join(map(qstr,qs)) + '] := by decide +kernel\n'
text += '''theorem retained_eq : retained matrix 2 3 = kept := by decide +kernel

theorem nO_eq : library matrix 2 = 755 := by decide +kernel
theorem nR_eq : library matrix 3 = 1097 := by decide +kernel

end Proofs
'''
Path('Proofs/Data.lean').write_text(text)
print(f'Wrote Proofs/Data.lean: {len(matrix)} rows, {len(pairs)} positive pairs, {len(retained)} retained.')
