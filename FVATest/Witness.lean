import FVA.Trust.Obligation
import FVA.Spec.ClaimAttr
import FVA.Spec.Valid.Soundness

/-! U37 C5: hand-written domain obligations, compared by the kernel. -/

namespace FVATest.Witness

open Lean Elab Command Term FVA.Trust

private def showObligation : Obligation → MessageData
  | .notRequired => "notRequired"
  | .required e => m!"required {e}"
  | .unavailable why => m!"unavailable {repr why}"

private def expect (claim : Name) (want : Obligation) : MetaM Unit := do
  let env ← getEnv
  let got ← obligation (fun n => env.contains n && !env.isImportedConst n) claim
  let agrees ← match got, want with
    | .notRequired, .notRequired | .unavailable _, .unavailable _ => pure true
    | .required a, .required b =>
      match Kernel.isDefEq env {} a b with
      | .ok same => pure same
      | .error _ => throwError "{claim}: kernel comparison failed:\n  {a}\n  {b}"
    | _, _ => pure false
  unless agrees do
    throwError "{claim}: got {showObligation got}, expected {showObligation want}"

elab "#domain " c:ident " => " p:term : command => liftTermElabM do
  let claim ← resolveGlobalConstNoOverload c
  let want ← elabTermEnsuringType p (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  expect claim (.required (← instantiateMVars want))

elab "#no_domain " c:ident : command => liftTermElabM do
  expect (← resolveGlobalConstNoOverload c) .notRequired

elab "#unavailable_domain " c:ident : command => liftTermElabM do
  expect (← resolveGlobalConstNoOverload c) (.unavailable "")

-- G1: an equality is a conclusion atom.
@[fva_claim] def noBinder : Prop := (0 : Nat) = 0
#no_domain noBinder

-- G2–G4: even an unused binder counts, regardless of origin or inhabitation.
@[fva_claim] def coreData : Prop := ∀ _ : Nat, True
#domain coreData => ∃ _ : Nat, True

private structure Box where
  value : Nat

@[fva_claim] def projectData : Prop := ∀ b : Box, b.value = b.value
#domain projectData => ∃ _ : Box, True

@[fva_claim] def emptyData : Prop := ∀ _ : Fin 0, True
#domain emptyData => ∃ _ : Fin 0, True

-- G5–G7: independent premises are conjuncts; later binder types can depend on earlier proofs.
@[fva_claim] def onePremise : Prop := (1 : Nat) = 1 → (2 : Nat) = 2
#domain onePremise => (1 : Nat) = 1

@[fva_claim] def dependentData : Prop :=
  ∀ n : Nat, n < 5 → ∀ i : Fin (n + 1), i.val = n → i.val < n + 1
#domain dependentData => ∃ n : Nat, n < 5 ∧ ∃ i : Fin (n + 1), i.val = n

@[fva_claim] def dependentPremise : Prop :=
  ∀ h : (0 : Nat) = 0, h = rfl → True
#domain dependentPremise => ∃ h : (0 : Nat) = 0, h = rfl

-- G8: δ exposes the wrapper, ζ exposes the head function, β reveals the postcondition's binder.
private def onCall (post : Nat → Prop) : Prop := ∀ n : Nat, n < 5 → post n

@[fva_claim] def wrapped : Prop :=
  (let call := onCall; call) (fun n => ∀ i : Fin n, i.val < 2 → i.val ≤ n)
#domain wrapped => ∃ n : Nat, n < 5 ∧ ∃ i : Fin n, i.val < 2

-- G9–G10: sibling conclusions can require different inputs. Premises never fork.
@[fva_claim] def fork : Prop := ∀ x : Nat, (x = 0 → True) ∧ (x = 1 → True)
#domain fork => (∃ x : Nat, x = 0) ∧ (∃ x : Nat, x = 1)

@[fva_claim] def binderlessBranch : Prop := True ∧ (∀ x : Nat, x = 2 → True)
#domain binderlessBranch => ∃ x : Nat, x = 2

@[fva_claim] def conjunctPremise : Prop := ∀ x : Nat, x = 0 ∧ x = 1 → True
#domain conjunctPremise => ∃ x : Nat, x = 0 ∧ x = 1

-- G11–G14: only a Prop binder immediately refuted by False is omitted.
@[fva_claim] def refuted : Prop := (2 : Nat) = 2 → (2 : Nat) = 3 → False
#domain refuted => (2 : Nat) = 2

private def emptyProp : Prop := False

@[fva_claim] def refutedAlias : Prop := ∀ x : Nat, x = 0 → emptyProp
#domain refutedAlias => ∃ _ : Nat, True

@[fva_claim] def dataToFalse : Prop := ∀ _ : Fin 0, False
#domain dataToFalse => ∃ _ : Fin 0, True

@[fva_claim] def conditionalNegation : Prop := ∀ x : Nat, x = 0 → ¬ x = 1
#domain conditionalNegation => ∃ x : Nat, x = 0

@[fva_claim] def negation : Prop := ¬ (∀ _ : Fin 0, True)
#no_domain negation

-- G15: no search below conclusion atoms.
@[fva_claim] def iffAtom : Prop := (∀ _ : Fin 0, True) ↔ True
#no_domain iffAtom

@[fva_claim] def orAtom : Prop := (∀ _ : Fin 0, True) ∨ True
#no_domain orAtom

@[fva_claim] def existsAtom : Prop := ∃ x : Nat, x = 1 → True
#no_domain existsAtom

-- G16: unfolding this imported base predicate would expose many leading binders.
@[fva_claim] def baseHead : Prop := FVA.Wasm.Valid.NeverStuck (fun _ => true)
#no_domain baseHead

-- G17–G18: declaration bodies are generated only to place δ steps at the fuel boundary.
elab "#domain_aliases " stem:ident count:num : command => do
  let mut body ← `(term| ∀ _ : Nat, True)
  for i in [1:count.getNat + 1] do
    let name := mkIdent (.str .anonymous s!"{stem.getId}{i}")
    elabCommand (← `(command| private def $name : Prop := $body))
    body ← `(term| $name)

#domain_aliases chain 256
#domain_aliases peer 130

@[fva_claim] def atLimit : Prop := chain255
#domain atLimit => ∃ _ : Nat, True

@[fva_claim] def overLimit : Prop := chain256
#unavailable_domain overLimit

-- The δ budget belongs to the claim, not to each branch.
@[fva_claim] def withinSharedBudget : Prop := chain127 ∧ peer128
#domain withinSharedBudget => (∃ _ : Nat, True) ∧ (∃ _ : Nat, True)

@[fva_claim] def overSharedBudget : Prop := chain130 ∧ peer130
#unavailable_domain overSharedBudget

-- G19: a universe parameter on the claim makes its obligation unavailable.
@[fva_claim] def polymorphic.{u} : Prop := ∀ _ : ULift.{u} Nat, True
#unavailable_domain polymorphic

-- G20–G21: preserve the premise with its binder in scope, including a stuck match.
@[fva_claim] def letPremise : Prop := ∀ n : Nat, (let m := n + 1; m < 4) → n < 4
#domain letPremise => ∃ n : Nat, (let m := n + 1; m < 4)

@[fva_claim] def matchPremise : Prop :=
  ∀ n : Nat, (match n with | 0 => False | k + 1 => k < 5) → n ≤ 5
#domain matchPremise => ∃ n : Nat, (match n with | 0 => False | k + 1 => k < 5)

@[fva_claim] def stuckConclusion : Prop :=
  ∀ n : Nat, match n with | 0 => ∀ _ : Fin 0, True | _ + 1 => False
#domain stuckConclusion => ∃ _ : Nat, True

-- K4–K5: the same registered attribute works for a theorem naming a marked claim.
@[fva_witness coreData] theorem goodAttribute : ∃ _ : Nat, True := ⟨0, .intro⟩

/-- error: -/
#guard_msgs (error, substring := true) in
@[fva_witness coreData] def notATheorem : ∃ _ : Nat, True := ⟨0, .intro⟩

private def notAClaim : Prop := coreData

/-- error: -/
#guard_msgs (error, substring := true) in
@[fva_witness notAClaim] theorem badTarget : ∃ _ : Nat, True := ⟨0, .intro⟩

-- G9 property: every generated a ≠ b pair is inhabited branchwise, never by one tuple.
elab "#check_sibling_domains" : command => do
  let mut seed : UInt32 := 37
  for i in [:8] do
    seed := seed * 1664525 + 1013904223
    let a := seed.toNat % 101
    let b := a + 1 + seed.toNat / 101 % 101
    let x := Syntax.mkNumLit (toString a)
    let y := Syntax.mkNumLit (toString b)
    let c := mkIdent (.str .anonymous s!"siblingCase{i}")
    elabCommand (← `(command| @[fva_claim] def $c : Prop :=
      ∀ n : Nat, (n = $x → True) ∧ (n = $y → True)))
    elabCommand (← `(command| #domain $c => (∃ n : Nat, n = $x) ∧ (∃ n : Nat, n = $y)))

#check_sibling_domains

end FVATest.Witness
