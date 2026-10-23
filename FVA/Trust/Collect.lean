import Lean
import FVA.Spec.Trust
import FVA.Tool.Lift
import FVA.Tool.Blob
import FVA.Spec.Cert

/-!
# Trust facts from the environment (trusted glue)

Imports the spec module + the project's library root and collects the facts `FVA.Trust.Pass`
judges (contract F1–F4): claims and their proofs + axiom closures, statement closures (which
subjects a claim mentions), overrides in the audited closure, syntax extensions of review
modules, the official-prelude rule, the review surface, and each lifted module's link facts.
Origin is decided by where a module's `.olean` lies, never by its name (contract F2).
-/

namespace FVA.Trust

open Lean

/-- Where a module comes from (contract F2). -/
inductive Origin where
  | core | mathlib | base | subject | project
deriving Repr, DecidableEq, Inhabited

/-- What `fva trust` was asked to judge. -/
structure Input where
  /-- Project root (absolute). -/
  root : System.FilePath
  /-- Module holding the claims. -/
  specModule : Name
  /-- Module importing every proof (the library root). -/
  rootModule : Name
  /-- Declared Lean-native subject modules (exact names, D8). -/
  subjects : Array Name := #[]
  /-- FVA base modules (the reviewed-once spec set). -/
  base : NameSet := {}
  /-- Resolved package directories whose modules count as Mathlib (`trustedPackages`). -/
  trustedPkgs : Array System.FilePath := #[]

/-- The kernel's fixed bundle (Lake `Check.lean` primitive + builtin targets): constants the
kernel treats specially, which must come from the official prelude. -/
def fixedBundle : Array Name :=
  #[``Nat, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq,
    ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String,
    ``String.mk, ``String.ofList, ``Char, ``Char.ofNat, ``List, ``eagerReduce, ``optParam,
    ``autoParam, ``semiOutParam, ``outParam, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]

/-- The module defining `c`, if imported. -/
def modOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- Constants declared by module `m`. -/
def moduleConsts (env : Environment) (m : Name) : Array Name :=
  match env.header.moduleNames.idxOf? m with
  | some i => env.header.moduleData[i]!.constNames
  | none => #[]

/-- Direct imports of module `m`. -/
def moduleImports (env : Environment) (m : Name) : Array Name :=
  match env.header.moduleNames.idxOf? m with
  | some i => env.header.moduleData[i]!.imports.map (·.module)
  | none => #[]

/-- Worklist closure: `expand c` = successors, `none` = stop at `c`. -/
partial def closure (roots : Array Name) (expand : Name → Option (Array Name)) : Array Name :=
  go roots.toList {} #[]
where
  go : List Name → NameSet → Array Name → Array Name
    | [], _, out => out
    | c :: rest, seen, out =>
      if seen.contains c then go rest seen out
      else go (((expand c).getD #[]).toList ++ rest) (seen.insert c) (out.push c)

/-- `p` lies under directory `dir` (both resolved). -/
def under (dir p : System.FilePath) : Bool :=
  p.normalize.toString.startsWith (dir.normalize.toString ++ "/")

/-- `name ↦ (url, rev)` of a Lake manifest's git packages, with its packages directory. -/
def manifestPins (path : System.FilePath) :
    IO (String × Std.HashMap String (String × String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let dir := (j.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  let mut out := {}
  for p in ← IO.ofExcept (j.getObjValAs? (Array Json) "packages") do
    if (p.getObjValAs? String "type").toOption == some "git" then
      out := out.insert (← IO.ofExcept (p.getObjValAs? String "name"))
        (← IO.ofExcept (p.getObjValAs? String "url"), ← IO.ofExcept (p.getObjValAs? String "rev"))
  return (dir, out)

/-- Package directories whose modules count as Mathlib (contract F2): a package the project's
manifest pins at the URL + revision FVA's own manifest pins, checked out (detached `.git/HEAD`)
at that revision. Any other package, a local or forked one included, is project code. The
checkout's files + `.olean`s are trusted state of the environment: `fva trust` runs no `git`
in them (repository config can run commands) and never re-hashes their bytes. -/
def trustedPackages (root fvaRoot : System.FilePath) : IO (Array System.FilePath) := do
  let (_, pins) ← manifestPins (fvaRoot / "lake-manifest.json")
  let (dir, pkgs) ← manifestPins (root / "lake-manifest.json")
  let mut out := #[]
  for (name, pin) in pkgs.toList do
    unless pins.get? name == some pin do continue
    let d := root / dir / name
    let head := d / ".git" / "HEAD"
    unless ← head.pathExists do continue
    if (← IO.FS.readFile head).trimAscii.toString == pin.2 then
      out := out.push (← IO.FS.realPath d)
  return out

/-- Origin of every imported module: core by the sysroot, Mathlib (+ its dependencies) by the
trusted package directories, then base, subject (declared, lifted or a blob), project. -/
def origins (env : Environment) (input : Input) (generated : NameSet) :
    IO (Std.HashMap Name Origin) := do
  let sys ← IO.FS.realPath ((← findSysroot) / "lib" / "lean")
  let mut out := {}
  for m in env.header.moduleNames do
    let f ← IO.FS.realPath (← findOLean m)
    let o :=
      if under sys f then .core
      else if input.trustedPkgs.any (under · f) then .mathlib
      else if input.subjects.contains m || generated.contains m then .subject
      else if input.base.contains m then .base
      else .project
    out := out.insert m o
  return out

/-- A definition's meaning = its type + body; an inductive's = its type + constructors. -/
def meaningDeps (ci : ConstantInfo) : Array Name :=
  let ty := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => ty ++ d.value.getUsedConstants
  | .inductInfo i => ty ++ i.ctors.toArray
  | _ => ty

/-- Overrides that change what compiled code runs or hide a definition from the kernel. -/
def overrides (env : Environment) (c : Name) (ci : ConstantInfo) : Array String := Id.run do
  let mut fs := #[]
  if (Compiler.implementedByAttr.getParam? env c).isSome then fs := fs.push "implemented_by"
  if isExtern env c then fs := fs.push "extern"
  if ci.isUnsafe then fs := fs.push "unsafe"
  if ci.isPartial then fs := fs.push "partial"
  if let .opaqueInfo _ := ci then fs := fs.push "opaque"
  return fs

/-- Syntax extensions leave constants typed `ParserDescr`/`TrailingParserDescr` (syntax,
notation) or `Macro`/elaborator handlers (`macro_rules`, `elab_rules`) in their module. -/
def isSyntaxExt (ci : ConstantInfo) : Bool :=
  match ci.type.getAppFn.constName? with
  | some n => [``ParserDescr, ``TrailingParserDescr, ``Macro, ``Elab.Term.TermElab,
      ``Elab.Command.CommandElab, ``Elab.Tactic.Tactic].contains n
  | none => false

/-- Generated equation lemmas land in whichever module first unfolds a definition. -/
def isEqnLemma : Name → Bool
  | .str _ s =>
    s == "eq_def" || s == "eq_unfold" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- Lifted modules (`fva lift` output): a theorem `<ns>.decode_eq` of type
`decode <ns>.bytes <ns>.len = .ok <ns>.module`; returns module ↦ namespace. -/
def liftedModules (env : Environment) : Std.HashMap Name Name := Id.run do
  let mut out := {}
  for m in env.header.moduleNames do
    for c in moduleConsts env m do
      if let .str ns "decode_eq" := c then
        if let some (.thmInfo t) := env.find? c then
          if decodeEqShape ns t.type then out := out.insert m ns
  return out
where
  decodeEqShape (ns : Name) (ty : Expr) : Bool :=
    match ty.eq? with
    | some (_, lhs, rhs) =>
      lhs.isAppOfArity `FVA.Wasm.Decode.decode 2 &&
        lhs.appFn!.appArg! == .const (ns ++ `bytes) [] && lhs.appArg! == .const (ns ++ `len) [] &&
        rhs.isAppOf ``Except.ok && rhs.appArg! == .const (ns ++ `module) []
    | none => false

/-- The value of a definition whose body is a raw natural literal. -/
def natValue (env : Environment) (c : Name) : Option Nat :=
  match env.find? c with
  | some (.defnInfo d) => d.value.nat?.orElse fun _ => d.value.rawNatLit?
  | _ => none

/-- The value of a definition whose body is a string literal. -/
def strValue (env : Environment) (c : Name) : Option String :=
  match env.find? c with
  | some (.defnInfo d) => match d.value with
    | .lit (.strVal s) => some s
    | _ => none
  | _ => none

/-- Little-endian packing of file bytes (`FVA.Wasm.Binary.pack` on bytes); written apart from
the lifter's packer (`FVA.Tool.packBytes`), so one packing bug cannot pass both sides. -/
def packBytes (bs : ByteArray) : Nat :=
  bs.data.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The source file of module `m`: under the package its `.olean` belongs to (the path above
`.lake/build/lib/lean/`), in a source directory of `LEAN_SRC_PATH` (set by `lake env`). -/
def sourceOf (m : Name) : IO (Option System.FilePath) := do
  let rel := "/".intercalate (m.components.map (·.toString))
  let some olean ← (do return some (← IO.FS.realPath (← findOLean m))) <|> pure none
    | return none
  let tail := s!"/.lake/build/lib/lean/{rel}.olean"
  let o := olean.toString
  unless o.endsWith tail do return none
  let pkg : System.FilePath := (o.dropEnd tail.length).toString
  let dirs := ((← IO.getEnv "LEAN_SRC_PATH").getD "").splitOn ":" |>.filter (!·.isEmpty)
  for d in dirs do
    let some d ← (do return some (← IO.FS.realPath d)) <|> pure none | continue
    if d == pkg || under pkg d then
      let f := d / (rel ++ ".lean")
      if ← f.pathExists then return some f
  return none

/-- The artifact a lifted module's `source` names, if it lies inside the project (`root`
resolved): a relative path without `..` that stays inside after symlinks. An absent file
passes here and is reported as absent. -/
def artifactPath (root : System.FilePath) (src : String) : IO (Option System.FilePath) := do
  let rel : System.FilePath := src
  if rel.isAbsolute || rel.components.contains ".." then return none
  let path := root / rel
  if ← path.pathExists then
    return if under root (← IO.FS.realPath path) then some path else none
  return some path

/-- Link facts of one lifted module (contract F4). -/
def linkOf (env : Environment) (root : System.FilePath) (m ns : Name) : IO Link := do
  let file := m.toString
  let none' (file : String) : Link :=
    { file, kind := .wasm, present := false, bytesMatch := false, lenMatch := false,
      decodeEq := true, regenerates := false }
  let some src := strValue env (ns ++ `source) | return none' file
  let some path ← artifactPath root src | return none' s!"{file} ({src}: outside the project)"
  unless ← path.pathExists do return none' s!"{file} ({src})"
  let bs ← IO.FS.readBinFile path
  -- the module's file must be exactly what `fva lift` writes for these bytes: nothing added
  let regenerates ← match FVA.Wasm.Decode.decode (packBytes bs) bs.size, ← sourceOf m with
    | .ok mod, some f => do
      pure ((← IO.FS.readFile f) == FVA.Tool.Lift.file ns.toString bs mod src)
    | _, _ => pure false
  return { file := s!"{file} ({src})", kind := .wasm, present := true,
           bytesMatch := natValue env (ns ++ `bytes) == some (packBytes bs),
           lenMatch := natValue env (ns ++ `len) == some bs.size,
           decodeEq := true, regenerates }

/-- Blob modules (`fva blob`: a certificate's input or output file): module → namespace, for
every module declaring `<ns>.blob : FVA.Cert.Blob := ⟨<ns>.bytes, <ns>.len⟩`. -/
def blobModules (env : Environment) : Std.HashMap Name Name := Id.run do
  let mut out := {}
  for m in env.header.moduleNames do
    for c in moduleConsts env m do
      if let .str ns "blob" := c then
        if let some (.defnInfo d) := env.find? c then
          if d.type == .const ``FVA.Cert.Blob [] &&
              d.value == mkApp2 (.const ``FVA.Cert.Blob.mk []) (.const (ns ++ `bytes) [])
                (.const (ns ++ `len) []) then
            out := out.insert m ns
  return out

/-- Link facts of one blob module: the file present inside the project, the numeral and length
equal to its bytes, the module exactly `fva blob`'s output. -/
def blobLinkOf (env : Environment) (root : System.FilePath) (m ns : Name) : IO Link := do
  let file := m.toString
  let none' (file : String) : Link :=
    { file, kind := .blob, present := false, bytesMatch := false, lenMatch := false,
      decodeEq := false, regenerates := false }
  let some src := strValue env (ns ++ `source) | return none' file
  let some path ← artifactPath root src | return none' s!"{file} ({src}: outside the project)"
  unless ← path.pathExists do return none' s!"{file} ({src})"
  let bs ← IO.FS.readBinFile path
  let regenerates ← match ← sourceOf m with
    | some f => pure ((← IO.FS.readFile f) == FVA.Tool.Blob.file ns.toString bs src)
    | none => pure false
  return { file := s!"{file} ({src})", kind := .blob, present := true,
           bytesMatch := natValue env (ns ++ `bytes) == some (packBytes bs),
           lenMatch := natValue env (ns ++ `len) == some bs.size,
           decodeEq := false, regenerates }

/-- A character that continues an identifier, so a following `'` is a prime, not a char
literal (non-ASCII counts: misreading a literal only overcounts). -/
def idChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c.toNat ≥ 0x80

/-- Which characters of a Lean source lie inside a comment or docstring (D11): `--` to the line
end, `/-` … `-/` nested (docstrings included), neither inside a string, raw string, char or
`«…»` literal. Every misread marks too little, never too much. -/
def commentMask (src : String) : Array Bool := Id.run do
  let cs := src.toList.toArray
  let at_ (k : Nat) : Char := cs[k]?.getD ' '
  let mut mask := Array.replicate cs.size false
  let mut i := 0
  let mut depth := 0
  -- inside a literal: `"` string, `r#…"` raw string (hash count), `«` quoted name
  let mut str := false
  let mut raw : Option Nat := none
  let mut quoted := false
  while i < cs.size do
    let c := cs[i]!
    if c == '\n' then
      i := i + 1
    else if depth > 0 then
      mask := mask.set! i true
      if c == '/' && at_ (i + 1) == '-' then
        mask := mask.set! (i + 1) true; depth := depth + 1; i := i + 2
      else if c == '-' && at_ (i + 1) == '/' then
        mask := mask.set! (i + 1) true; depth := depth - 1; i := i + 2
      else i := i + 1
    else if str then
      if c == '\\' then i := i + 2
      else
        if c == '"' then str := false
        i := i + 1
    else if let some h := raw then
      if c == '"' && (List.range h).all (fun k => at_ (i + 1 + k) == '#') then
        raw := none; i := i + 1 + h
      else i := i + 1
    else if quoted then
      if c == '»' then quoted := false
      i := i + 1
    else if c == '-' && at_ (i + 1) == '-' then
      while i < cs.size && cs[i]! != '\n' do
        mask := mask.set! i true; i := i + 1
    else if c == '/' && at_ (i + 1) == '-' then
      mask := (mask.set! i true).set! (i + 1) true; depth := 1; i := i + 2
    else
      let prevId := i > 0 && idChar cs[i - 1]!
      if c == '"' then str := true; i := i + 1
      else if c == '«' then quoted := true; i := i + 1
      else if c == 'r' && !prevId &&
          (at_ (i + 1) == '"' || at_ (i + 1) == '#') then
        let mut h := 0
        while at_ (i + 1 + h) == '#' do h := h + 1
        if at_ (i + 1 + h) == '"' then raw := some h; i := i + 2 + h
        else i := i + 1
      else if c == '\'' && !prevId then
        -- char literal: `'x'` or an escape `'\…'` closed within a few characters
        if at_ (i + 1) == '\\' then
          let mut j := i + 3
          while j < i + 12 && j < cs.size && cs[j]! != '\'' && cs[j]! != '\n' do j := j + 1
          i := if j < cs.size && cs[j]! == '\'' then j + 1 else i + 1
        else if at_ (i + 2) == '\'' && at_ (i + 1) != '\n' then i := i + 3
        else i := i + 1
      else i := i + 1
  return mask

/-- Code lines of a Lean source (D11): lines holding a non-blank character outside comments and
docstrings (`commentMask`); string, char and `«…»` contents count as code. -/
def codeLines (src : String) : Nat := Id.run do
  let mask := commentMask src
  let mut n := 0
  let mut code := false
  for (c, k) in src.toList.zipIdx do
    if c == '\n' then
      if code then n := n + 1
      code := false
    else if !c.isWhitespace && !mask[k]! then code := true
  if code then n := n + 1
  return n

/-- A Lean source without its comments and docstrings (`commentMask`), line breaks kept. -/
def stripComments (src : String) : String :=
  let mask := commentMask src
  String.ofList <| src.toList.zipIdx.filterMap fun (c, k) =>
    if mask[k]! && c != '\n' then none else some c

/-- Every environment fact of the report (build, replay, canaries and budget are set later). -/
def collect (input : Input) : CoreM Report := do
  let env ← getEnv
  let lifted := liftedModules env
  let blobs := blobModules env
  let generated : NameSet :=
    blobs.fold (fun s m _ => s.insert m) (lifted.fold (fun s m _ => s.insert m) {})
  let orig ← origins env input generated
  let originOf (c : Name) : Origin := ((modOf env c).bind orig.get?).getD .project
  let trusted (c : Name) : Bool := originOf c == .core || originOf c == .mathlib
  -- claims: Prop-valued definitions of the spec module; a theorem there = a claim proven in place
  let userNames := (moduleConsts env input.specModule).filter fun n =>
    !n.isInternal && !isEqnLemma n
  -- a claim's type is `Prop` up to unfolding (`def MyProp := Prop` hides no claim)
  let isProp (n : Name) : CoreM Bool := do
    match env.find? n with
    | some (.defnInfo d) => return (← (Meta.whnf d.type).run') == .sort .zero
    | _ => return false
  let isThm (n : Name) : Bool := match env.find? n with
    | some (.thmInfo _) => true
    | _ => false
  let mut proofsOf : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .thmInfo t := ci then
      if let .const c [] := t.type then
        proofsOf := proofsOf.insert c ((proofsOf.getD c #[]).push n)
  let stopAt (c : Name) : Bool := originOf c != .project
  let statementClosure (roots : Array Name) : Array Name :=
    closure roots fun c => match env.find? c with
      | some ci => if stopAt c then none else some (meaningDeps ci)
      | none => none
  let statementSubjects (roots : Array Name) : List String :=
    (((statementClosure roots).filter fun n => originOf n == .subject).filterMap
      (modOf env)).toList.eraseDups.map (·.toString)
  let mut claims := #[]
  let mut stmtRoots := #[]
  let mut proofNames := #[]
  for c in ← userNames.filterM fun n => return isThm n || (← isProp n) do
    let ci := (env.find? c).get!
    let thm := isThm c
    let prfs := if thm then #[c] else proofsOf.getD c #[]
    let mut ps := #[]
    for p in prfs do
      let ax ← collectAxioms p
      ps := ps.push { name := p.toString, axioms := (ax.map (·.toString)).toList }
      proofNames := proofNames.push p
    let roots := if thm then ci.type.getUsedConstants else meaningDeps ci
    stmtRoots := stmtRoots ++ roots
    claims := claims.push { name := c.toString, provenInSpec := thm, proofs := ps.toList,
                            subjects := statementSubjects roots }
  -- audited closure: everything outside core + Mathlib reachable from the claims + proofs
  let claimNames := (claims.map (·.name.toName))
  let audit := closure (claimNames ++ proofNames) fun c =>
    if trusted c then none
    else (env.find? c).map fun ci =>
      ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map
        Expr.getUsedConstants).getD #[]
  let mut flags := #[]
  for c in audit do
    if trusted c then continue
    if let some ci := env.find? c then
      for k in overrides env c ci do
        flags := flags.push
          { decl := c.toString, module := ((modOf env c).getD .anonymous).toString, kind := k }
  -- official prelude: the fixed bundle from the sysroot; every non-core module imports `Init`
  let mut prelude := #[]
  for c in fixedBundle do
    if env.contains c && originOf c != .core then
      prelude := prelude.push s!"{c} comes from {(modOf env c).getD .anonymous}, not Lean core"
  -- one pass: `moduleNames` lists every module after its imports
  let mut withInit : NameSet := {}
  for m in env.header.moduleNames do
    if m == `Init || (moduleImports env m).any fun i => i == `Init || withInit.contains i then
      withInit := withInit.insert m
    else if orig.get? m != some .core then
      prelude := prelude.push s!"{m} does not import Init (prelude module)"
  -- review surface: project modules in the spec module's import closure, read whole
  let specClosure := closure #[input.specModule] fun n => some (moduleImports env n)
  let mut reviewModules := #[]
  let mut subjectSyntax := #[]
  for m in specClosure do
    let exts := (moduleConsts env m).filter fun n => ((env.find? n).map isSyntaxExt).getD false
    if orig.get? m == some .subject then
      subjectSyntax := subjectSyntax ++ exts.map fun n => s!"{m}: {n}"
    unless orig.get? m == some .project do continue
    let src ← sourceOf m
    let lines ← match src with
      | some f => pure (codeLines (← IO.FS.readFile f))
      | none => pure 0
    reviewModules := reviewModules.push { module := m.toString, codeLines := lines,
                                          found := src.isSome,
                                          syntaxExts := (exts.map (·.toString)).toList }
  -- vocabulary (D10): the statement closure's frontier outside the project and the subjects,
  -- minus generated names (instances by Lean's `inst…` naming, internals, constructors, matchers)
  let mut vocabulary := #[]
  for n in (statementClosure stmtRoots).qsort Name.lt do
    let o := originOf n
    if o == .project || o == .subject || n.isInternal || isEqnLemma n then continue
    if let .str _ s := n then
      let generatedInst := s.startsWith "inst" && ((s.drop 4).front.isUpper)
      if generatedInst || s.startsWith "match_" || s.startsWith "proof_" then continue
    match env.find? n with
    | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) | none => continue
    | _ => pure ()
    let doc := ((← findDocString? env n).getD "").trimAscii.toString.splitOn "\n" |>.head!
    let origin := match o with
      | .core => "core"
      | .mathlib => "mathlib"
      | _ => "base"
    vocabulary := vocabulary.push
      { name := n.toString, module := ((modOf env n).getD .anonymous).toString, origin, doc }
  let mut links := #[]
  for (m, ns) in lifted.toList do
    if specClosure.contains m then links := links.push (← linkOf env input.root m ns)
  for (m, ns) in blobs.toList do
    if specClosure.contains m then links := links.push (← blobLinkOf env input.root m ns)
  return { built := true, claims := claims.toList, flags := flags.toList,
           reviewModules := reviewModules.toList, subjectSyntax := subjectSyntax.toList,
           vocabulary := vocabulary.toList,
           prelude := prelude.toList,
           needsLink := input.subjects.isEmpty, links := links.toList, exportOk := false,
           replay := [], canaries := [], canarySet := [], budget := none }

end FVA.Trust
