import Lean

/-!
# Claim domain obligations (U37, contract `docs/contracts/U37-witness.md` C1; trusted glue)

`obligation inU c` = what a witness of claim `c` proves: for each conclusion path of `c`'s
statement, the path's leading binders closed existentially (a data binder `∃ x : A`, a premise `A ∧
…`, or `∃ h : A, …` when later binders mention `h`), the paths conjoined. A path forks at each `∧`
of a conclusion (never inside a premise) and ends at the first other head. Heads are normalized at
every visit: metadata, `let` and β, plus δ of the definitions `inU` admits (the project's and
subjects'), at most `bound` δ steps per claim. A binder `h : A` whose body normalizes to `False` is
the statement the claim refutes: its path ends before `h`. Prop-ness and universe levels come from
the kernel (`Kernel.check` + `Kernel.whnf`), so the result does not depend on which environment
extensions are loaded: `fva trust`'s collector (`loadExts := false`) and the proof-side
`fva_obligation%` elaborator compute the same `Expr`. -/

namespace FVA.Trust
open Lean Meta

/-- C1's outcome for one claim (the reviewed report keeps its printed form, `Domain`). -/
inductive Obligation where
  /-- No binder on any conclusion path: nothing to witness. -/
  | notRequired
  /-- The closed proposition a witness must prove. -/
  | required (e : Expr)
  /-- C1 could not compute it (unfolding bound, universe parameters, a kernel error). -/
  | unavailable (why : String)
deriving Inhabited

/-- δ steps one claim may take (contract C1). -/
def domainBound : Nat := 256

/-- The kernel's type of `e` in the current local context, in weak head normal form. -/
def kernelSort (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let lctx ← getLCtx
  match Kernel.check env lctx e with
  | .error _ => throwError "kernel cannot type a binder of the claim"
  | .ok t => match Kernel.whnf env lctx t with
    | .ok s => return s
    | .error _ => throwError "kernel cannot normalize a binder's type"

/-- Head normal form (C1): metadata, `let`, β, and δ of `inU` definitions within `gas`. -/
partial def domainHead (inU : Name → Bool) (gas : IO.Ref Nat) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .letE _ _ v b _ := e then return ← domainHead inU gas (b.instantiate1 v)
  let f := e.getAppFn.consumeMData
  match f with
  | .lam .. => domainHead inU gas (mkAppN f e.getAppArgs).headBeta
  | .letE _ _ v b _ => domainHead inU gas (mkAppN (b.instantiate1 v) e.getAppArgs)
  | .const n us =>
    if inU n then
      if let some ci@(.defnInfo _) := (← getEnv).find? n then
        let k ← gas.get
        if k == 0 then throwError "more than {domainBound} definitions unfolded"
        gas.set (k - 1)
        return ← domainHead inU gas (mkAppN (ci.instantiateValueLevelParams! us) e.getAppArgs)
    return e
  | _ => return e

/-- The closed obligation of one path: `xs` = its binders, outermost first. -/
def closePath (xs : Array Expr) : MetaM (Option Expr) := do
  let mut acc : Option Expr := none
  for x in xs.reverse do
    let a ← inferType x
    let s ← kernelSort a
    let isProp := s == .sort .zero
    let body := acc.getD (mkConst ``True)
    if isProp && !(acc.any (·.containsFVar x.fvarId!)) then
      acc := some (match acc with | some w => mkApp2 (mkConst ``And) a w | none => a)
    else
      let .sort u := s | throwError "binder type is not a sort"
      acc := some (mkApp2 (.const ``Exists [u]) a (← mkLambdaFVars #[x] body))
  return acc

/-- The obligations of every conclusion path under binders `xs`. -/
partial def domainPaths (inU : Name → Bool) (gas : IO.Ref Nat) (xs : Array Expr) (e : Expr) :
    MetaM (Array Expr) := do
  let e ← domainHead inU gas e
  match e with
  | .forallE n a b bi =>
    let a := a.headBeta
    withLocalDecl n bi a fun x => do
      let body := b.instantiate1 x
      if (← kernelSort a) == .sort .zero then
        if (← domainHead inU gas body).isConstOf ``False then
          return (← closePath xs).toArray
      domainPaths inU gas (xs.push x) body
  | _ =>
    if e.isAppOfArity ``And 2 then
      return (← domainPaths inU gas xs (e.getArg! 0)) ++ (← domainPaths inU gas xs (e.getArg! 1))
    return (← closePath xs).toArray

/-- C1: the domain obligation of claim `c` (a definition), its paths conjoined in order. -/
def obligation (inU : Name → Bool) (c : Name) : MetaM Obligation := do
  let some ci := (← getEnv).find? c | return .unavailable s!"{c} is not declared"
  unless ci.levelParams.isEmpty do return .unavailable "universe-polymorphic claim"
  let gas ← IO.mkRef domainBound
  try
    let ps ← domainPaths inU gas #[] (mkConst c)
    match ps.toList with
    | [] => return .notRequired
    | p :: rest => return .required (rest.foldl (fun acc q => mkApp2 (mkConst ``And) acc q) p)
  catch e => return .unavailable (← e.toMessageData.toString)

end FVA.Trust
