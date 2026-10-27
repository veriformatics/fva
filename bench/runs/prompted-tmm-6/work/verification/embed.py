"""Embed the three artifacts without interpreting or rounding their contents."""
import json
from fractions import Fraction
from pathlib import Path

FILES = ("counts.tsv", "edger-factors.txt", "rnanorm-factors.txt")
NAMES = ("countsText", "edgeText", "rnaText")

def source():
    raw = "".join(
        f"def {name} : String := {json.dumps(Path(file).read_bytes().decode('ascii'))}\n"
        for file, name in zip(FILES, NAMES)
    )
    matrix = [list(map(int, row.split('\t'))) for row in Path(FILES[0]).read_text().splitlines()]
    data = f"def matrix : List (List Nat) := {json.dumps(matrix)}\n"
    for file, name in zip(FILES[1:], ('edge', 'rna')):
        values = [Fraction(s) for s in Path(file).read_text().splitlines()]
        data += f"def {name} : List ℚ := [" + ', '.join(
            f"({v.numerator} / {v.denominator})" for v in values) + "]\n"
    return "import Mathlib.Data.Rat.Defs\nnamespace Artifact\n" + raw + data + "end Artifact\n"

if __name__ == "__main__":
    import sys
    target = Path("Proofs/Artifact.lean")
    if "--check" in sys.argv:
        assert target.read_bytes() == source().encode(), "artifact embedding differs"
        print("Artifact bytes match all three embedded strings")
    else:
        target.write_text(source())
