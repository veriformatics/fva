import Proofs.Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace TMM

/-- A total, character-by-character parser for the positive decimal lines here.
`n` collects all digits and `d` is multiplied by ten after the decimal point.
The exact input strings are separately pinned by `edge_bytes` and `rna_bytes`.
-/
def decimalLinesAux : List Char → ℕ → ℕ → Bool → List ℚ
  | [], n, d, seen => if seen then [(n:ℚ)/d] else []
  | c::cs, n, d, seen =>
    if c == '\n' then (n/d : ℚ) :: decimalLinesAux cs 0 1 false
    else if c == '.' then decimalLinesAux cs n d true
    else decimalLinesAux cs (10*n+(c.toNat-48)) (if seen then 10*d else d) seen

def decimalLines (s : String) : List ℚ := decimalLinesAux s.toList 0 1 false

theorem edge_decimals_checked : edgeFactors = decimalLines edgeText := by
  decide +kernel

theorem rna_decimals_checked : rnaFactors = decimalLines rnaText := by
  decide +kernel
end TMM
