"""Independent high precision diagnostic. Lean, not this script, proves the bounds."""
from decimal import Decimal as D, getcontext
from fractions import Fraction as Q
from pathlib import Path
getcontext().prec = 60
x = [list(map(int, line.split())) for line in Path('counts.tsv').read_text().splitlines()]
libs = [sum(row[j] for row in x) for j in range(7)]
q = []
for j in range(7):
    col = sorted(row[j] for row in x)
    q.append(Q(col[339] + 3*col[340], 4*libs[j]))
ref = min(range(7), key=lambda j: abs(q[j] - sum(q)/7))
assert ref == 3
z = []
for j in range(7):
    pairs = [(r[j], r[ref]) for r in x if r[j] and r[ref]]
    m = [Q(o, r) for o, r in pairs]
    a = [o*r for o, r in pairs]
    def ranks(v):
        return [2*sum(b < t for b in v) + sum(b == t for b in v) + 1 for t in v]
    n = len(pairs)
    kept = [p for p, rm, ra in zip(pairs, ranks(m), ranks(a))
            if 2*(n*3//10+1) <= rm <= 2*(n-n*3//10)
            and 2*(n//20+1) <= ra <= 2*(n-n//20)]
    weights = [1 / ((Q(1, o)-Q(1, libs[j]))+(Q(1, r)-Q(1, libs[ref])))
               for o, r in kept]
    def dec(v):
        return D(v.numerator)/D(v.denominator)
    v = (D(libs[ref])/D(libs[j])).ln() + sum(
        dec(w)*(D(o)/D(r)).ln() for (o,r),w in zip(kept,weights)) / dec(sum(weights))
    z.append(v)
mean = sum(z)/7
print('Reference sample:', ref+1)
print('Exact-tie TMM factors (60-digit Decimal diagnostic, not proof):')
for j, v in enumerate(z):
    print(j+1, (v-mean).exp())
