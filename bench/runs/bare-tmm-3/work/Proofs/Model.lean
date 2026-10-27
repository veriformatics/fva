import Mathlib

/-! Exact, real-arithmetic TMM model. Indices are zero based.
Raw files are embedded by Lean, rather than transcribed numeric constants. -/
namespace TMMVerification

def countsText : String := include_str "../counts.tsv"
def edgeText : String := include_str "../edger-factors.txt"
def rnaText : String := include_str "../rnanorm-factors.txt"

/-- A character-list parser, so even parsing is reducible in Lean's kernel.
The separate byte/grammar checker rejects malformed input; this parser only
needs decimal digits, tabs, dots and newlines for the supplied files. -/
def splitChars (sep : Char) (cs : List Char) : List (List Char) :=
  cs.foldr (fun c acc => if c == sep then [] :: acc else
    match acc with
    | [] => [[c]]
    | a :: rest => (c :: a) :: rest) [[]]

def parseNat (cs : List Char) : Nat :=
  cs.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0

def lines (s : String) : List (List Char) :=
  (splitChars '\n' s.toList).filter (· != [])

def matrix : List (List Nat) :=
  (lines countsText).map fun l => (splitChars '\t' l).map parseNat

def decimal (s : List Char) : ℚ :=
  let p := splitChars '.' s
  let a := parseNat p[0]!
  let b := p[1]!
  (a : ℚ) + (parseNat b : ℚ) / (10 ^ b.length : Nat)

def edgeFactors : List ℚ := (lines edgeText).map decimal
def rnaFactors : List ℚ := (lines rnaText).map decimal

def rows : List (List Nat) := matrix.filter (fun r => r.any (· > 0))
def libSize (j : Nat) : Nat := (matrix.map (fun r => r[j]!)).sum

/-- R's default type-7 quantile, p=3/4, divided by the library size. -/
def upperQuartile (j : Nat) : ℚ :=
  let col := (rows.map (fun r => r[j]!)).mergeSort (· ≤ ·)
  let h := 3 * (col.length - 1)
  let i := h / 4
  let t := h % 4
  (((4 - t) * col[i]! + t * col[i+1]! : Nat) : ℚ) / 4 / libSize j

def indices : List Nat := List.range 7
def quartileMean : ℚ := (indices.map upperQuartile).sum / 7

def reference : Nat := indices.foldl (fun best j =>
  if |upperQuartile j - quartileMean| < |upperQuartile best - quartileMean|
  then j else best) 0

abbrev Pair := Nat × Nat

def positivePairs (j : Nat) : List Pair :=
  (rows.map (fun r => (r[j]!, r[reference]!))).filter (fun p => p.1 > 0 && p.2 > 0)

/-- Twice the usual one-based average rank (so ties are represented exactly). -/
def rank2 (ps : List Pair) (key : Pair → ℚ) (p : Pair) : Nat :=
  2 * (ps.filter (fun q => key q < key p)).length +
    (ps.filter (fun q => key q == key p)).length + 1

def mKey (p : Pair) : ℚ := (p.1 : ℚ) / p.2
def aKey (p : Pair) : ℚ := (p.1 * p.2 : Nat)

/-- Logs are strictly increasing: M ranks by obs/ref, A by obs*ref.
Library-size constants do not change either ranking. -/
def keptPairs (j : Nat) : List Pair :=
  let ps := positivePairs j
  let n := ps.length
  let lm := n * 3 / 10 + 1
  let la := n / 20 + 1
  ps.filter fun p =>
    let rm := rank2 ps mKey p
    let ra := rank2 ps aKey p
    2 * lm ≤ rm && rm ≤ 2 * (n + 1 - lm) &&
    2 * la ≤ ra && ra ≤ 2 * (n + 1 - la)

/-- Inverse asymptotic binomial variance, with the defaults' weighting enabled. -/
def weight (j : Nat) (p : Pair) : ℚ :=
  1 / ((1 / (p.1 : ℚ) - 1 / libSize j) +
       (1 / (p.2 : ℚ) - 1 / libSize reference))

/-- A term (c,n) denotes c * log n, using natural logs. -/
abbrev Term := ℚ × Nat

def rawTerms (j : Nat) : List Term :=
  if j == reference then [] else
  let ps := keptPairs j
  let total := (ps.map (weight j)).sum
  [(1, libSize reference), (-1, libSize j)] ++
    ps.flatMap (fun p => [(weight j p / total, p.1), (-weight j p / total, p.2)])

/-- Subtract the mean log factor: division by the geometric mean in factor space. -/
def centeredTerms (j : Nat) : List Term := rawTerms j ++
  indices.flatMap (fun i => (rawTerms i).map (fun p => (-p.1 / 7, p.2)))

noncomputable def evalTerms (ts : List Term) : ℝ :=
  (ts.map (fun p => (p.1 : ℝ) * Real.log p.2)).sum

/-- log(2) cancels between weighted M-values and exponentiation by 2. -/
noncomputable def exactFactor (j : Nat) : ℝ := Real.exp (evalTerms (centeredTerms j))

end TMMVerification
