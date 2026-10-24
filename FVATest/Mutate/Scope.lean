import Lean

/-!
# Environment facts for the mutation runner

From the imported environment of the package's build roots (one `importModules` per process):
the declarations of each package module with their line ranges + kinds (a downstream error
location maps to the declaration around it, contract K4/K5), the Prop-valued definitions
(never mutated, S1) and the spec definitions an implementation reaches (`helpers`, S1).
-/

namespace FVA.Mutate

open Lean

/-- A declaration's lines and kind. -/
structure DeclRange where
  /-- First line (1-based). -/
  first : Nat
  /-- Last line. -/
  last : Nat
  /-- `theorem` `def` `type` `other`. -/
  kind : String
  /-- Constant name. -/
  name : Name

/-- `true` when `t = ∀ …, Prop`. -/
partial def resultIsProp : Expr → Bool
  | .forallE _ _ b _ => resultIsProp b
  | .sort .zero => true
  | _ => false

/-- Facts about the package modules in an environment. -/
structure EnvFacts where
  /-- Module → its declarations with ranges. -/
  ranges : Std.HashMap Name (Array DeclRange)
  /-- Definitions whose type is Prop-valued. -/
  propDefs : NameSet
  /-- Constant → defining module (package constants only). -/
  moduleOf : Std.HashMap Name Name
  /-- The environment itself (reachability). -/
  env : Environment

/-- Import `mods` and index the declarations of `pkg` modules. Needs the search path
initialized and initializers enabled. -/
def loadFacts (mods : Array Name) (pkg : NameSet) : IO EnvFacts := do
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  let mut ranges : Std.HashMap Name (Array DeclRange) := {}
  let mut propDefs : NameSet := {}
  let mut moduleOf := {}
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless pkg.contains m do continue
    moduleOf := moduleOf.insert c m
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ | .opaqueInfo _ => "def"
      | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => "type"
      | .axiomInfo _ => "other"
    if kind == "def" && resultIsProp ci.type then propDefs := propDefs.insert c
    let r? := declRangeExt.find? (level := .exported) env c <|>
      declRangeExt.find? (level := .server) env c
    if let some r := r? then
      ranges := ranges.insert m ((ranges.getD m #[]).push
        { first := r.range.pos.line, last := r.range.endPos.line, kind, name := c })
  return { ranges, propDefs, moduleOf, env }

/-- Kind of the innermost declaration of module `m` around `line`, if any. -/
def EnvFacts.kindAt (f : EnvFacts) (m : Name) (line : Nat) : Option (String × Name) :=
  let hits := (f.ranges.getD m #[]).filter fun d => d.first ≤ line && line ≤ d.last
  let best := hits.foldl (fun (acc : Option DeclRange) d => match acc with
    | some a => if d.last - d.first < a.last - a.first then some d else some a
    | none => some d) none
  best.map fun d => (d.kind, d.name)

/-- Constants of modules satisfying `inScope` that the values of the definitions of `roots`
reach, transitively through definitions of those modules; Prop-valued ones excluded. -/
def EnvFacts.reach (f : EnvFacts) (roots : NameSet) (inScope : Name → Bool) : NameSet := Id.run do
  let mut todo : Array Name := #[]
  for (c, m) in f.moduleOf.toList do
    if roots.contains m then
      if let some v := (f.env.find? c).bind (·.value?) then todo := todo ++ v.getUsedConstants
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some m := f.moduleOf.get? c | continue
    unless inScope m do continue
    if let some (.defnInfo d) := f.env.find? c then
      unless f.propDefs.contains c do out := out.insert c
      todo := todo ++ d.value.getUsedConstants
  return out

end FVA.Mutate
