from pathlib import Path

counts = Path('counts.tsv').read_bytes()
assert counts.endswith(b'\n') and all(c in b'0123456789\t\n' for c in counts)
matrix = [list(map(int, row.split(b'\t'))) for row in counts[:-1].split(b'\n')]
assert len(matrix) == 454 and all(len(r) == 7 and max(r) < 100 for r in matrix)
assert counts == b''.join(b'\t'.join(str(n).encode() for n in row) + b'\n' for row in matrix)
def decimal_data(path):
    data = Path(path).read_bytes()
    assert data.endswith(b'\n')
    rows = data[:-1].split(b'\n')
    assert len(rows) == 7
    result = []
    for row in rows:
        whole, frac = row.split(b'.')
        assert len(whole) == 1 and whole.isdigit() and frac.isdigit()
        result.append((int(whole + frac), len(frac)))
    encoded = b''.join((str(n // 10**p) + '.' + str(n % 10**p).zfill(p) + '\n').encode() for n, p in result)
    assert encoded == data
    return result

def literal(v):
    if isinstance(v, list): return '[' + ', '.join(map(literal, v)) + ']'
    if isinstance(v, tuple): return '(' + ', '.join(map(literal, v)) + ')'
    return str(v)

s = 'import Mathlib.Data.Rat.Defs\nnamespace Verification\n'
s += 'def matrix : List (List Nat) := ' + literal(matrix) + '\n'
s += 'def edgeData : List (Nat × Nat) := ' + literal(decimal_data('edger-factors.txt')) + '\n'
s += 'def rnaData : List (Nat × Nat) := ' + literal(decimal_data('rnanorm-factors.txt')) + '\n'
s += 'end Verification\n'
Path('Proofs/Input.lean').write_text(s)
