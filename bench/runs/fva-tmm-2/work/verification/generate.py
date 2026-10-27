#!/usr/bin/env python3
"""Untrusted proof-data generator. All generated assertions are checked by Lean."""
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal, localcontext
import json

ROOT = Path(__file__).resolve().parent.parent


def ls(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def rat(q):
    q = Q(q)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def dec(s):
    a, b = s.split('.')
    return f'⟨{a}, {ls(map(int, b))}⟩'


matrix = [[int(v) for v in line.split('\t')]
          for line in (ROOT / 'counts.tsv').read_text().splitlines()]
edge = (ROOT / 'edger-factors.txt').read_text().splitlines()
rna = (ROOT / 'rnanorm-factors.txt').read_text().splitlines()
data = ['import Proofs.Model', '', 'namespace Proofs.Data', '',
        'def counts : Model.Matrix := [',
        ',\n'.join('  ' + ls(row) for row in matrix), ']', '',
        'def edge : List Model.Decimal := [' + ', '.join(map(dec, edge)) + ']',
        'def rna : List Model.Decimal := [' + ', '.join(map(dec, rna)) + ']', '']

libs = [sum(row[j] for row in matrix) for j in range(7)]
for j in range(7):
    data += [f'def sorted{j} : List Nat := ' + ls(sorted(row[j] for row in matrix))]
ref = 3
all_kept = []
raw = []
with localcontext() as ctx:
    ctx.prec = 70
    ln = lambda n: Decimal(n).ln()
    for j in range(7):
        ps = [(row[j], row[ref]) for row in matrix if row[j] and row[ref]]

        def rank2(p, key):
            return 2 * sum(key(q) < key(p) for q in ps) + sum(key(q) == key(p) for q in ps) + 1

        n = len(ps)
        lo_m, hi_m = 2 * (n * 3 // 10 + 1), 2 * (n - n * 3 // 10)
        lo_a, hi_a = 2 * (n // 20 + 1), 2 * (n - n // 20)
        kept = [p for p in ps if lo_m <= rank2(p, lambda q: Q(*q)) <= hi_m
                and lo_a <= rank2(p, lambda q: q[0] * q[1]) <= hi_a]
        all_kept.append(kept)
        data += [f'def kept{j} : List (Nat × Nat) := ' +
                 ls(f'({a}, {b})' for a, b in kept)]
        weights = [1 / (Q(libs[j] - a, libs[j] * a) +
                        Q(libs[ref] - b, libs[ref] * b)) for a, b in kept]
        mean = sum((Decimal(w.numerator) / Decimal(w.denominator)) *
                   (ln(a) - ln(b) + ln(libs[ref]) - ln(libs[j]))
                   for (a, b), w in zip(kept, weights))
        total = sum(weights)
        mean /= Decimal(total.numerator) / Decimal(total.denominator)
        raw.append(mean)
    center = [v - sum(raw) / 7 for v in raw]
    factors = [v.exp() for v in center]
    brackets = [(int(v * 1000000) - 1, int(v * 1000000) + 2) for v in factors]
    data += ['\ndef rawBounds : List (Bounds.I) := [\n' + ',\n'.join(
        f'  ⟨{rat(Q(int(v * 10**9) - 2, 10**9))}, {rat(Q(int(v * 10**9) + 2, 10**9))}⟩'
        for v in raw) + '\n]']
    data += ['def factorBounds : List (Nat × Nat) := ' + ls(f'({a}, {b})' for a, b in brackets)]
    numbers = sorted(set(range(1, max(max(row) for row in matrix) + 1)) |
                     set(libs) | {1000000} | {v for pair in brackets for v in pair})
    logbounds = {}
    for n in numbers:
        value = ln(n)
        lower = int(value * 10**12) - 1
        upper = int(value * 10**12) + 2
        logbounds[n] = (lower, upper)
    data += ['def logI (n : Nat) : Bounds.I :=\n  match n with\n' + '\n'.join(
        f'  | {n} => ⟨{rat(Q(a, 10**12))}, {rat(Q(b, 10**12))}⟩'
        for n, (a, b) in logbounds.items()) + '\n  | _ => ⟨0, 0⟩',
        'def logged : List Nat := ' + ls(numbers), '', 'end Proofs.Data', '']
    data.insert(1, 'import Proofs.Bounds')
    (ROOT / 'Proofs/Data.lean').write_text('\n'.join(data))
    checks = ['import Proofs.Data', '', 'namespace Proofs', 'open Bounds Model',
              'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    for n in numbers:
        a, b = logbounds[n]
        k = n.bit_length() - 1
        checks += [f'theorem log_{n} : (Data.logI {n}).Holds (Real.log ({n} : Nat)) := by',
                   f'  apply log_nat {n} {k} {rat(Q(a, 10**12))} {rat(Q(b, 10**12))}',
                   '  all_goals decide +kernel', '']
    checks += ['theorem log_valid (n : Nat) (hn : n ∈ Data.logged) :',
               '    (Data.logI n).Holds (Real.log n) := by',
               '  simp only [Data.logged, List.mem_cons, List.not_mem_nil, or_false] at hn',
               '  rcases hn with ' + ' | '.join('h' for _ in numbers)]
    for n in numbers:
        checks += [f'  · subst n; exact log_{n}']
    checks += ['', 'end Proofs', '']
    (ROOT / 'Proofs/LogChecks.lean').write_text('\n'.join(checks))
    report = dict(libraries=libs, reference_1based=ref + 1,
                  exact_kept=[len(p) for p in all_kept],
                  ideal_factors=list(map(str, factors)), brackets=brackets,
                  edge_absolute_errors=[str(abs(Decimal(s) - f)) for s, f in zip(edge, factors)],
                  rna_absolute_errors=[str(abs(Decimal(s) - f)) for s, f in zip(rna, factors)])
    (ROOT / 'verification/numerical.json').write_text(json.dumps(report, indent=2) + '\n')
print('Generated proof data; acceptance requires lake build and fva trust.')
