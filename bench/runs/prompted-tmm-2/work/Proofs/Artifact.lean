namespace Artifact
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def distance (a b : Nat) : Nat := (a-b)+(b-a)
-- Each inner list is one line of ASCII bytes, with its LF supplied by the binding check.
def digits (bs : List Nat) : Nat := bs.foldl (fun a b => 10*a+(b-48)) 0
def decimal17 (bs : List Nat) : Option Nat := do
  let a := bs.takeWhile (· != 46)
  let b := bs.drop (a.length+1)
  if bs[a.length]? != some 46 || a.isEmpty || b.isEmpty || b.length > 17 ||
     !(a++b).all (fun d => 48 ≤ d && d ≤ 57) then none else
    return digits a * 10^17 + digits b * 10^(17-b.length)
def parse (bs : List (List Nat)) : Option (List Nat) := bs.mapM decimal17
def edgeBytes : List (List Nat) := [[48,46,57,57,48,57,57,57,52,50,52,53,57,50,57,51,48,54,55],[49,46,50,55,55,50,57,56,52,48,54,56,55,57,50,50,52,56],[49,46,49,50,53,51,48,55,54,51,57,55,50,48,52,55,55,53],[48,46,57,53,51,53,56,53,57,55,50,56,54,51,50,53,52,51,49],[48,46,56,49,51,51,55,53,51,52,50,49,56,52,51,52,51,56,50],[48,46,57,50,57,54,56,50,56,48,51,53,54,55,49,49,54,52,49],[48,46,57,55,51,53,57,50,54,57,50,53,49,57,49,54,53,52,55]]
def rnaBytes : List (List Nat) := [[48,46,57,56,49,54,56,56,48,48,49,53,54,53,54,48,52,52],[49,46,50,55,57,51,48,57,54,57,50,56,54,50,54,56,51,53],[49,46,49,50,55,48,55,57,53,57,52,56,54,52,55,53,54,53],[48,46,57,53,53,48,56,55,53,50,56,48,57,49,55,56,52,52],[48,46,56,49,52,54,53,54,49,49,54,48,53,53,51,54,51,56],[48,46,57,51,49,49,52,54,55,49,57,56,57,51,55,57,57,56],[48,46,57,55,53,49,50,53,55,53,49,49,52,49,53,55,57,52]]
def edge : List Nat := [99099942459293067,127729840687922480,112530763972047750,95358597286325431,81337534218434382,92968280356711641,97359269251916547]
def rna : List Nat := [98168800156560440,127930969286268350,112707959486475650,95508752809178440,81465611605536380,93114671989379980,97512575114157940]
theorem edge_bytes : parse edgeBytes = some edge := by decide_cbv
theorem rna_bytes : parse rnaBytes = some rna := by decide_cbv
-- A tolerance of 10^-10 is 10^7 of these units.
theorem first_gap : edge[0]! - rna[0]! = 931142302732627 := by decide_cbv
theorem R3_false : ¬ (∀ i : Fin 7, distance edge[i.val]! rna[i.val]! ≤ 10^7) := by
  intro h
  have h0 := h ⟨0, by decide_cbv⟩
  have hn : ¬ distance edge[0]! rna[0]! ≤ 10^7 := by decide_cbv
  exact hn h0
-- Also reject the common interpretations based on decimal formatting.
theorem different_truncated_10 : edge[0]! / 10^7 ≠ rna[0]! / 10^7 := by decide_cbv
theorem different_rounded_10 : (edge[0]! + 5*10^6) / 10^7 ≠ (rna[0]! + 5*10^6) / 10^7 := by decide_cbv
end Artifact
