import FVA.Tool.Explain

/-!
# `fva explain` pure parts (U10; built by `scripts/test-trust`, beside its explain run)

Outside `FVATest.Main` like `FVATest.Trust`: the files of `fvatest`'s dispatch enter every U12
test-kill digest.
-/

namespace FVA.Tool.Explain.Check

open FVA.Tool.Explain

-- saved text: current only for the same inputs and the same claims (in any order)
#guard !isStale (some "a") "a" ["x", "y"] ["y", "x"]
#guard isStale (some "a") "b" ["x"] ["x"]
#guard isStale (some "a") "a" ["x"] ["x", "y"]
#guard isStale none "a" [] []

-- proof status: issues naming the claim or its proofs, plus project-wide ones naming no claim;
-- a name is matched whole (`gcd` is not inside `gcd_holds` or `Toy.gcd2`)
#guard proofStatus [("unproven", "T.gcd has no proof"), ("link", "L.lean: MISMATCH")]
    ["T.gcd", "T.gcd_holds", "T.clamp"] ["T.gcd", "T.gcd_holds"] ==
  (false, ["T.gcd has no proof"], ["link"])
#guard proofStatus [("axiom", "T.gcd_holds (proof of T.gcd) depends on sorryAx")]
    ["T.gcd", "T.gcd_holds", "T.clamp"] ["T.clamp"] == (true, [], [])
#guard proofStatus [("unproven", "T.gcd2 has no proof")] ["T.gcd", "T.gcd2"] ["T.gcd"] ==
  (true, [], [])
#guard proofStatus [] ["T.gcd"] ["T.gcd"] == (true, [], [])

-- report text
#guard wrap "a b c" "  " "    " == ["  a b c"]
#guard (wrap (String.intercalate " " (List.replicate 40 "word")) "  " "    ").length == 3
#guard num 4294967295 32 == "4294967295 (= -1 signed)"
#guard num 5 32 == "5"
#guard signed 255 8 == -1
#guard modFile "/p" "A.B.Spec" == ("/p/A/B/Spec.lean" : System.FilePath)
#guard FVA.Trust.stripComments "def x := 1 -- c\n/- d -/def y := \"--s\"" ==
  "def x := 1 \ndef y := \"--s\""

end FVA.Tool.Explain.Check
