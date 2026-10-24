import Lean

/-!
# Package module graph

Imports within the package (from each file's header, `Lean.parseImports`), upstream closures
(dependency digests, contract R2) and downstream modules in a fixed order (the `proofs` stage,
contract K3: topological, ties broken lexicographically, so the first failing module is
deterministic).
-/

namespace FVA.Mutate

open Lean

/-- Module name of a repo-relative `.lean` path. -/
def modOfPath (p : String) : Name :=
  ((p.dropEnd 5).toString.splitOn "/").foldl Name.str .anonymous

/-- Repo-relative path of a module. -/
def pathOfMod (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

/-- Every `.lean` file under the given roots (directories or files), repo-relative, sorted. -/
partial def leanFiles (root : System.FilePath) (roots : List String) : IO (Array String) := do
  let mut out := #[]
  for r in roots do
    let p := root / r
    if ← p.isDir then
      for e in ← p.walkDir do
        if e.extension == some "lean" && !(← e.isDir) then
          out := out.push ((e.toString.drop (root.toString.length + 1)).toString)
    else if ← p.pathExists then out := out.push r
  return out.qsort (· < ·)

/-- Package modules and their package-internal imports. -/
structure Graph where
  /-- Direct imports of each module, within the package. -/
  imports : Std.HashMap Name (Array Name)
  /-- Every package module, sorted. -/
  mods : Array Name

/-- Build the graph of the `.lean` files under `srcRoots`, minus paths under `exclude`. -/
def Graph.build (root : System.FilePath) (srcRoots : List String) (exclude : List String := []) :
    IO Graph := do
  let files := (← leanFiles root srcRoots).filter fun f => !exclude.any (f.startsWith ·)
  let mods := files.map modOfPath
  let set : NameSet := mods.foldl (·.insert ·) {}
  let mut imports := {}
  for f in files do
    let (imps, _, _) ← Lean.Elab.parseImports (← IO.FS.readFile (root / f)) f
    imports := imports.insert (modOfPath f) ((imps.map (·.module)).filter set.contains)
  return { imports, mods }

/-- `m` and every package module it imports transitively, sorted. -/
partial def Graph.upstream (g : Graph) (m : Name) : Array Name :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | x :: rest =>
      if seen.contains x then go rest seen
      else go ((g.imports.getD x #[]).toList ++ rest) (seen.insert x)
  (go [m] {}).toArray.qsort Name.lt

/-- The union of the upstream closures of `roots`. -/
def Graph.closure (g : Graph) (roots : Array Name) : NameSet :=
  roots.foldl (fun s r => (g.upstream r).foldl (·.insert ·) s) {}

/-- Modules of `within` that import `m` transitively (`m` excluded), each after its imports,
ties broken lexicographically. -/
partial def Graph.downstream (g : Graph) (m : Name) (within : NameSet) : Array Name := Id.run do
  let down := within.toArray.filter fun p => p != m && (g.upstream p).contains m
  let downSet : NameSet := down.foldl (·.insert ·) {}
  let mut done : NameSet := {}
  let mut out := #[]
  let mut left := down.qsort Name.lt
  while !left.isEmpty do
    let ready := left.filter fun p =>
      (g.imports.getD p #[]).all fun q => !downSet.contains q || done.contains q
    let some next := ready[0]? | break
    out := out.push next
    done := done.insert next
    left := left.filter (· != next)
  return out

end FVA.Mutate
