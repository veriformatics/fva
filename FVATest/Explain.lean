import FVA.Tool.Explain
import FVA.Explain

/-! # `fva explain` pure parts (U10; built with `fvatest`, so `lake test` runs them) -/

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
#guard modPath "A.B.Spec" == ("A/B/Spec.lean" : System.FilePath)
#eval show IO Unit from do
  let s := FVA.Trust.stripComments (← Lean.mkEmptyEnvironment)
    "def x := 1 -- c\n/- d -/def y := \"--s\"\n/-- doc /- nested -/ -/ z\nw-- right after"
  unless s == "def x := 1 \ndef y := \"--s\"\n z\nw" do throw <| .userError s!"stripComments: {s}"

-- requirements file (D5): each `## <id>` line starts a requirement; the text before = context
#guard parseReqs "Ctx line\n\n## R1\nclamp x.\n\n## R2\nsecond\nmore\n" ==
  ("Ctx line", [{ id := "R1", text := "clamp x." }, { id := "R2", text := "second\nmore" }])
#guard (parseReqs "no requirement\n# R1 is a title").2 == []

-- neutral names (D5): a project name's last component renamed wherever an identifier names
-- it, claims numbered first; string literals, projections and other packages' names stay
private def rn : Renamer :=
  Renamer.of [`Ex.Toy.clamp, `Ex.Toy.gcd] [`Ex.Toy.clamp, `Ex.Toy.gcd, `Ex.Toy.helper]
#guard rn.apply "def clamp : Prop := Returns m \"clamp\" (helper x) ∧ Nat.gcd a b = x.gcd" ==
  "def claim_1 : Prop := Returns m \"clamp\" (name_3 x) ∧ Nat.gcd a b = x.gcd"
#guard rn.apply "Ex.Toy.gcd ∧ Toy.helper ∧ Other.helper ∧ «clamp» ∧ clamp'" ==
  "Ex.Toy.claim_2 ∧ Toy.name_3 ∧ Other.helper ∧ «clamp» ∧ clamp'"
#guard rn.restore "claim_1 holds when name_3 is claim_10; `claim_2`." ==
  "clamp holds when helper is claim_10; `gcd`."

-- example values (D16): `whnf` reads the definition, never the compiled override, and the
-- kernel confirms the value by `rfl` (or refuses a wrong one)
def sumBelowWrong (_ : Nat) : Nat := 0
@[implemented_by sumBelowWrong]
def sumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow n + n

open Lean Meta FVA.Explain in
#eval show MetaM Unit from do
  let ten := mkApp (mkConst ``sumBelow) (mkNatLit 10)
  let res := mkApp3 (mkConst ``List.cons [0]) (mkConst ``FVA.Wasm.Exec.Val)
    (mkApp (mkConst ``FVA.Wasm.Exec.Val.i32) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32) ten))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``FVA.Wasm.Exec.Val))
  unless (← values res) == some [("i32", 45)] do throwError "values: {← values res}"
  unless (← kernelAccepts res (valsExpr [("i32", 45)])) == some true do throwError "45 refused"
  unless (← kernelAccepts res (valsExpr [("i32", 0)])) == some false do throwError "0 accepted"
  -- D17: a case past its heartbeat budget is `cost`, decided inside Lean (no process kill)
  let big := mkApp3 (mkConst ``List.cons [0]) (mkConst ``FVA.Wasm.Exec.Val)
    (mkApp (mkConst ``FVA.Wasm.Exec.Val.i32) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32)
      (mkApp (mkConst ``sumBelow) (mkNatLit 4294967295))))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``FVA.Wasm.Exec.Val))
  unless (← evalCase big).2 == "cost" do throwError "sumBelow 4294967295 not too costly"
  unless (← evalCase res) == ([("i32", 45)], "confirmed") do throwError "evalCase {← evalCase res}"

-- the explain thread has no shell, image viewer or MCP tool (closing review SEC-4)
#guard ["shell_tool", "unified_exec", "view_image"].all fun f =>
  (FVA.Tool.Codex.serverArgs.toList.zip FVA.Tool.Codex.serverArgs.toList.tail).contains
    ("--disable", f)
#guard (FVA.Tool.Codex.serverArgs.toList.zip FVA.Tool.Codex.serverArgs.toList.tail).contains
  ("-c", "mcp_servers={}")

end FVA.Tool.Explain.Check
