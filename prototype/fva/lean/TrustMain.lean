import Lean
open Lean

/-!
`fva-trust`: what must a human read to believe a project's claims, and do the proofs hold?

Usage: `lake env fva-trust --spec-module M [--subject M]… [--base M]…`, run in the target
project; JSON on stdout, rendered by `fva trust`.

- Claim = a `Prop`-valued definition in the spec module; proof = any theorem whose type is that
  claim constant. A theorem declared in the spec module counts as a claim proven in place.
- Review modules = the spec module's import closure minus Lean core (`Init`/`Std`/`Lean`), base
  (FVA trusted semantics) + subject (lifted implementation) modules; each is read whole, since
  the spec text parses under every macro, notation + instance they declare. Proofs therefore
  live downstream (`Proof` imports `Spec`, never the reverse); a review module that extends
  syntax is flagged.
- Statement closure = constants the claims mention, transitively through definition bodies,
  stopping at subject/base/core; it reports which subject, base + core names the spec uses.
- Audit closure = types + values of everything outside Lean core reachable from the proofs.
-/

structure Opts where
  subjects : Array Name := #[]
  base : Array Name := #[`FVA.Wasm.Semantics]
  specModule : Name := .anonymous

def parseArgs : List String → Opts → Opts
  | "--subject" :: m :: r, o => parseArgs r { o with subjects := o.subjects.push m.toName }
  | "--base" :: m :: r, o => parseArgs r { o with base := o.base.push m.toName }
  | "--spec-module" :: m :: r, o => parseArgs r { o with specModule := m.toName }
  | _ :: r, o => parseArgs r o
  | [], o => o

inductive Cat where
  | spec | subject | base | core
  deriving BEq

def modOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def classifyMod (o : Opts) (m : Name) : Cat :=
  if [`Init, `Std, `Lean].contains m.getRoot then .core
  else if o.subjects.contains m then .subject
  else if o.base.contains m then .base
  else .spec

def kindStr : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

/-- A definition's meaning = its body; an inductive's = its constructors. -/
def meaningDeps (ci : ConstantInfo) : Array Name :=
  let ty := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => ty ++ d.value.getUsedConstants
  | .inductInfo i => ty ++ i.ctors.toArray
  | _ => ty

/-- Worklist closure: `expand c` = successors of `c`, `none` = stop at `c`. -/
partial def closure (roots : Array Name) (expand : Name → Option (Array Name)) : Array Name :=
  go roots.toList {} #[]
where
  go : List Name → Std.HashSet Name → Array Name → Array Name
    | [], _, out => out
    | c :: rest, seen, out =>
      if seen.contains c then go rest seen out
      else go (((expand c).getD #[]).toList ++ rest) (seen.insert c) (out.push c)

def auditFlags (env : Environment) (c : Name) (ci : ConstantInfo) : Array String := Id.run do
  let mut fs := #[]
  if (Compiler.implementedByAttr.getParam? env c).isSome then fs := fs.push "implemented_by"
  if isExtern env c then fs := fs.push "extern"
  if ci.isUnsafe then fs := fs.push "unsafe"
  if ci.isPartial then fs := fs.push "partial"
  if let .opaqueInfo _ := ci then fs := fs.push "opaque"
  return fs

/-- Generated equation lemmas (`f.eq_1`, `f.eq_def`, `f.eq_unfold`) land in whichever module
first unfolds `f`; they are not user claims. -/
def isEqnLemma : Name → Bool
  | .str _ s => s == "eq_def" || s == "eq_unfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- Syntax extensions leave constants typed `ParserDescr`/`TrailingParserDescr` (syntax, notation)
or `Macro`/`*Elab` handlers (`macro_rules`, `elab_rules`) in their module. -/
def isSyntaxExt (ci : ConstantInfo) : Bool :=
  match ci.type.getAppFn.constName? with
  | some n => [``ParserDescr, ``TrailingParserDescr, ``Macro, ``Elab.Term.TermElab,
      ``Elab.Command.CommandElab, ``Elab.Tactic.Tactic].contains n
  | none => false

def moduleConsts (env : Environment) (m : Name) : Array Name :=
  match env.header.moduleNames.idxOf? m with
  | some i => env.header.moduleData[i]!.constNames
  | none => #[]

def importClosure (env : Environment) (m : Name) : Array Name :=
  closure #[m] fun n => (env.header.moduleNames.idxOf? n).map fun i =>
    env.header.moduleData[i]!.imports.map (·.module)

def report (o : Opts) : CoreM Json := do
  let env ← getEnv
  let cls := fun c => classifyMod o (modOf env c)
  let userNames := (moduleConsts env o.specModule).filter fun n => !n.isInternal && !isEqnLemma n
  let isProp := fun (n : Name) => match env.find? n with
    | some (.defnInfo d) => d.type == .sort .zero | _ => false
  let isThm := fun (n : Name) => match env.find? n with | some (.thmInfo _) => true | _ => false
  let mut proofsOf : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .thmInfo t := ci then
      if let .const c [] := t.type then
        proofsOf := proofsOf.insert c ((proofsOf.getD c #[]).push n)
  let claims := userNames.filter isProp ++ userNames.filter isThm
  let specExpand := fun c => match env.find? c with
    | some ci => if cls c == Cat.spec then some (meaningDeps ci) else none
    | none => none
  let mut claimsJ := #[]
  let mut proofs := #[]
  let mut allAx : Array Name := #[]
  for c in claims do
    let ci := (env.find? c).get!
    let prfs := if isThm c then #[c] else proofsOf.getD c #[]
    let stmt := closure (if isThm c then ci.type.getUsedConstants else meaningDeps ci) specExpand
    let subjects := ((stmt.filter fun n => cls n == Cat.subject).map (modOf env)).toList.eraseDups
    let mut prfJ := #[]
    for p in prfs do
      let ax ← collectAxioms p
      allAx := ax.foldl (fun a x => if a.contains x then a else a.push x) allAx
      proofs := proofs.push p
      prfJ := prfJ.push <| Json.mkObj [("name", toJson p), ("module", toJson (modOf env p)),
        ("axioms", toJson ax)]
    let r ← findDeclarationRanges? c
    claimsJ := claimsJ.push <| Json.mkObj [("name", toJson c), ("kind", toJson (kindStr ci)),
      ("subjects", toJson subjects), ("proofs", Json.arr prfJ),
      ("start", toJson (r.map (·.range.pos.line))), ("end", toJson (r.map (·.range.endPos.line)))]
  let stmt := closure (claims.foldl (fun a c => a ++ meaningDeps (env.find? c).get!) #[]) specExpand
  let used := fun (k : Cat) => (stmt.filter fun n => cls n == k && !n.isInternal).map toJson
  let full := closure proofs fun c => match env.find? c with
    | some ci => if cls c == Cat.core then none
                 else some (ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[])
    | none => none
  let mut flags := #[]
  for c in full do
    if let some ci := env.find? c then
      if cls c != Cat.core then
        for f in auditFlags env c ci do
          flags := flags.push <| Json.mkObj [("name", toJson c), ("module", toJson (modOf env c)),
            ("issue", toJson f)]
  let reviewMods := (importClosure env o.specModule).filter fun m => classifyMod o m == .spec
  let modsJ := reviewMods.map fun m =>
    let cs := moduleConsts env m
    Json.mkObj [("module", toJson m),
      ("decls", toJson (cs.filter fun n => !n.isInternal && !isEqnLemma n)),
      ("syntaxExtensions", toJson (cs.filter fun n => ((env.find? n).map isSyntaxExt).getD false))]
  return Json.mkObj [("claims", Json.arr claimsJ), ("allAxioms", toJson allAx),
    ("reviewModules", Json.arr modsJ), ("baseUsed", Json.arr (used .base)),
    ("coreUsed", Json.arr (used .core)), ("proofs", toJson proofs),
    ("auditClosureSize", toJson full.size), ("flags", Json.arr flags)]

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  if o.specModule.isAnonymous then
    IO.eprintln "fva-trust: --spec-module M required"
    return 2
  initSearchPath (← findSysroot)
  -- import the library root too, so proofs downstream of the spec module are visible
  let root := o.specModule.getRoot
  let env ← importModules #[{ module := o.specModule }, { module := root }] {}
  let ctx : Core.Context := { fileName := "<fva-trust>", fileMap := default }
  let (j, _) ← (report o).toIO ctx { env }
  IO.println j.compress
  return 0
