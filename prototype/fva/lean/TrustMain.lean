import Lean
open Lean

/-!
`fva-trust`: what must a human read to believe the given theorems?

Usage: `lake env fva-trust --import M… [--subject M]… [--base M]… THEOREM…`, run in the
target project. Emits JSON on stdout; `fva trust` renders it + counts lines.

Spec surface = statement closure of the theorems: constants their types mention, then
transitively through bodies of definitions (a definition's meaning = its body), never through
theorem proofs. Expansion stops at subject modules (the lifted implementation the theorems
constrain), base modules (FVA trusted semantics) + Lean core (`Init`/`Std`/`Lean`).
Audit closure = types + values of everything outside Lean core.
-/

structure Opts where
  imports : Array Name := #[]
  subjects : Array Name := #[]
  base : Array Name := #[`FVA.Wasm.Semantics]
  theorems : Array Name := #[]
  specModules : Array Name := #[]

def parseArgs : List String → Opts → Opts
  | "--import" :: m :: r, o => parseArgs r { o with imports := o.imports.push m.toName }
  | "--subject" :: m :: r, o => parseArgs r { o with subjects := o.subjects.push m.toName }
  | "--spec-module" :: m :: r, o =>
    parseArgs r { o with specModules := o.specModules.push m.toName, imports := o.imports.push m.toName }
  | "--base" :: m :: r, o => parseArgs r { o with base := o.base.push m.toName }
  | t :: r, o => parseArgs r { o with theorems := o.theorems.push t.toName }
  | [], o => o

inductive Cat where
  | spec | subject | base | core
  deriving BEq

def Cat.str : Cat → String
  | .spec => "spec" | .subject => "subject" | .base => "base" | .core => "core"

def modOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def classify (o : Opts) (env : Environment) (c : Name) : Cat :=
  let m := modOf env c
  if [`Init, `Std, `Lean].contains m.getRoot then .core
  else if o.subjects.contains m then .subject
  else if o.base.contains m then .base
  else .spec

def kindStr : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

/-- Constants a reader must understand to understand `ci`: its type, plus the body of a
definition, plus the constructors of an inductive. -/
def meaningDeps (ci : ConstantInfo) : Array Name :=
  let ty := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => ty ++ d.value.getUsedConstants
  | .inductInfo i => ty ++ i.ctors.toArray
  | _ => ty

/-- Worklist closure: `expand c` = successors of `c`, `none` = stop at `c`. -/
def closure (roots : Array Name) (expand : Name → Option (Array Name)) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut order := #[]
  let mut work := roots.toList
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if seen.contains c then continue
      seen := seen.insert c
      order := order.push c
      if let some next := expand c then work := next.toList ++ work
  return order

def auditFlags (env : Environment) (c : Name) (ci : ConstantInfo) : Array String := Id.run do
  let mut fs := #[]
  if (Compiler.implementedByAttr.getParam? env c).isSome then fs := fs.push "implemented_by"
  if isExtern env c then fs := fs.push "extern"
  if ci.isUnsafe then fs := fs.push "unsafe"
  if ci.isPartial then fs := fs.push "partial"
  if let .opaqueInfo _ := ci then fs := fs.push "opaque"
  return fs

def report (o : Opts) : CoreM Json := do
  let env ← getEnv
  let cls := classify o env
  let specExpand := fun c => match env.find? c with
    | some ci => if cls c == Cat.spec then some (meaningDeps ci) else none
    | none => none
  let stmtOf := fun (t : Name) => closure (env.find? t).get!.type.getUsedConstants specExpand
  let mut thms := #[]
  let mut allAx : Array Name := #[]
  for t in o.theorems do
    let ax ← collectAxioms t
    allAx := ax.foldl (fun a x => if a.contains x then a else a.push x) allAx
    let mentions := (stmtOf t).any fun c => cls c == Cat.subject
    let r : Option DeclarationRanges ← findDeclarationRanges? t
    thms := thms.push <| Json.mkObj [("name", toJson t), ("module", toJson (modOf env t)),
      ("axioms", toJson ax), ("mentionsSubject", toJson mentions),
      ("start", toJson (r.map (·.range.pos.line))), ("end", toJson (r.map (·.range.endPos.line)))]
  let stmt := closure (o.theorems.foldl (fun acc t => acc ++ (env.find? t).get!.type.getUsedConstants) #[])
    specExpand
  let full := closure o.theorems fun c => match env.find? c with
    | some ci => if cls c == Cat.core then none
                 else some (ci.type.getUsedConstants ++ ((ci.value?).map Expr.getUsedConstants).getD #[])
    | none => none
  let mut flags := #[]
  for c in full do
    if let some ci := env.find? c then
      if cls c != Cat.core then
        for f in auditFlags env c ci do
          flags := flags.push <| Json.mkObj [("name", toJson c), ("module", toJson (modOf env c)),
            ("issue", toJson f)]
  let mut decls := #[]
  for c in stmt do
    let ci := (env.find? c).get!
    let r : Option DeclarationRanges ← findDeclarationRanges? c
    decls := decls.push <| Json.mkObj [("name", toJson c), ("module", toJson (modOf env c)),
      ("category", toJson (cls c).str), ("kind", toJson (kindStr ci)),
      ("start", toJson (r.map (·.range.pos.line))), ("end", toJson (r.map (·.range.endPos.line)))]
  return Json.mkObj [("theorems", Json.arr thms), ("allAxioms", toJson allAx),
    ("statementClosure", Json.arr decls), ("auditClosureSize", toJson full.size),
    ("flags", Json.arr flags)]

/-- Generated equation lemmas (`f.eq_1`, `f.eq_def`, `f.eq_unfold`) land in whichever module
first unfolds `f`; they are not user claims. -/
def isEqnLemma : Name → Bool
  | .str _ s => s == "eq_def" || s == "eq_unfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- User-facing theorems declared in `m`. -/
def theoremsOf (env : Environment) (m : Name) : Array Name := Id.run do
  let some i := env.header.moduleNames.idxOf? m | return #[]
  env.header.moduleData[i]!.constNames.filter fun n =>
    !n.isInternal && !isEqnLemma n && match env.find? n with | some (.thmInfo _) => true | _ => false

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  initSearchPath (← findSysroot)
  let env ← importModules (o.imports.map ({ module := · })) {}
  let o := { o with theorems := o.specModules.foldl (fun a m => a ++ theoremsOf env m) o.theorems }
  if o.theorems.isEmpty then
    IO.eprintln "fva-trust: no theorems (pass names or --spec-module M)"
    return 2
  for t in o.theorems do
    unless env.contains t do
      IO.eprintln s!"fva-trust: unknown theorem {t}"
      return 2
  let ctx : Core.Context := { fileName := "<fva-trust>", fileMap := default }
  let (j, _) ← (report o).toIO ctx { env }
  IO.println j.compress
  return 0
