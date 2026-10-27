"""Untrusted certificate generator: Lean checks every interval by rational arithmetic."""
from fractions import Fraction
from math import log, floor
from pathlib import Path

args = list(range(1, 43)) + [621, 755, 1097, 1136, 1219, 1261, 1916]

def rat(x):
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator}/{x.denominator})'

out = ['import Proofs.LogBounds', '', 'namespace TMMVerification', '', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
       'def logArgs : List Nat := [' + ', '.join(map(str, args)) + ']', '',
       'def logCert (n : Nat) : LogCert := match n with']
for n in args:
    k = n.bit_length() - 1
    y = Fraction(n, 2**k)
    t = (y-1)/(y+1)
    lo = Fraction(floor(log(n)*10**6)-1, 10**6)
    hi = lo + Fraction(3, 10**6)
    out.append(f'  | {n} => ⟨{n}, {k}, {rat(t)}, {rat(lo)}, {rat(hi)}⟩')
out += ['  | _ => ⟨1, 0, 0, 0, 0⟩', '',
        'theorem log_certificates_checked :',
        '    ∀ n ∈ logArgs, (logCert n).arg = n ∧ (logCert n).valid := by',
        '  decide +kernel', '',
        'theorem log_bounds_at (n : Nat) (h : n ∈ logArgs) :',
        '    ((logCert n).lo : ℝ) ≤ Real.log n ∧',
        '    Real.log n ≤ ((logCert n).hi : ℝ) := by',
        '  obtain ⟨ha, hv⟩ := log_certificates_checked n h',
        '  simpa only [ha] using (logCert n).sound hv', '',
        'end TMMVerification', '']
Path('Proofs/Certificates.lean').write_text('\n'.join(out))
