import Init

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

namespace Artifacts

def scale : Nat := 10^17

def edgeBytes : String := include_str ".." / "edger-factors.txt"
def rnaBytes : String := include_str ".." / "rnanorm-factors.txt"

-- Pure byte-list parsing: no native evaluation or partial string parser.
def split (sep : Nat) : List Nat → List (List Nat)
  | [] => [[]]
  | c :: cs => match split sep cs with
    | [] => []
    | h :: t => if c = sep then [] :: h :: t else (c :: h) :: t

def digits (cs : List Nat) : Option Nat :=
  if cs.isEmpty then none else
    cs.foldlM (fun n c => if 48 ≤ c ∧ c ≤ 57
      then some (10*n + (c - 48)) else none) 0

-- An accepted decimal denotes exactly the returned natural divided by 10^17.
def decimal (cs : List Nat) : Option Nat := do
  let [whole, frac] := split 46 cs | none
  if frac.length > 17 then none else
    return (← digits whole) * scale + (← digits frac) * 10^(17-frac.length)

def factors (s : String) : Option (List Nat) := do
  let [] :: rev := (split 10 (s.toByteArray.data.toList.map UInt8.toNat)).reverse | none
  rev.reverse.mapM decimal

def edge : List Nat := [99099942459293067, 127729840687922480,
  112530763972047750, 95358597286325431, 81337534218434382,
  92968280356711641, 97359269251916547]
def rna : List Nat := [98168800156560440, 127930969286268350,
  112707959486475650, 95508752809178440, 81465611605536380,
  93114671989379980, 97512575114157940]

-- At 17 decimal places, 10^-10 is 10^7 integer units.
abbrev within10 (a b : Nat) : Prop := a ≤ b + 10^7 ∧ b ≤ a + 10^7

def rounded10 (a : Nat) : Nat := (a + 5000000) / 10000000

abbrev normalized (xs : List Nat) : Prop :=
  xs.length = 7 ∧ (∀ i : Fin xs.length, 0 < xs[i]) ∧
  xs.prod * 10^14 ≤ scale^7 * (10^14 + 1) ∧
  scale^7 * (10^14 - 1) ≤ xs.prod * 10^14

theorem artifact_values : factors edgeBytes = some edge ∧ factors rnaBytes = some rna := by
  decide

theorem r1_necessary_conditions : normalized edge := by decide

theorem r2_necessary_conditions : normalized rna := by decide

theorem r3_all_samples_fail :
    edge.length = 7 ∧ rna.length = 7 ∧
    ∀ i : Fin 7, ¬ within10 edge[i.val]! rna[i.val]! ∧
      rounded10 edge[i.val]! ≠ rounded10 rna[i.val]! := by
  decide

theorem r3_sample1_gap :
    edge[0]! = rna[0]! + 931142302732627 ∧
    edge[0]! > rna[0]! + 10^14 := by decide

theorem r3_failure_of_artifact :
    ∃ e r, factors edgeBytes = some e ∧ factors rnaBytes = some r ∧
      e.length = 7 ∧ r.length = 7 ∧
      ∀ i : Fin 7, ¬ within10 e[i.val]! r[i.val]! ∧
        rounded10 e[i.val]! ≠ rounded10 r[i.val]! := by
  exact ⟨edge, rna, artifact_values.1, artifact_values.2, r3_all_samples_fail⟩

end Artifacts

#print axioms Artifacts.artifact_values
#print axioms Artifacts.r1_necessary_conditions
#print axioms Artifacts.r2_necessary_conditions
#print axioms Artifacts.r3_all_samples_fail
#print axioms Artifacts.r3_sample1_gap
#print axioms Artifacts.r3_failure_of_artifact
