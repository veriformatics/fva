import Lean

/-!
# Mutation sites

Lists the mutants of one Lean file (contract `docs/contracts/U12-mutation.md`, S2, O, M): the
file is elaborated command by command with Lean's own frontend, so local and imported notation
parse as they do in a build; each definition body (`def`, `abbrev`, `instance` values, equation
RHSs, `where` helpers) is walked, skipping patterns, binders, the type side of ascriptions, `by`
blocks and termination clauses; each operator variant yields one mutant = byte edits on the
original file. Also reports every command's byte range + kind (error locations map to
declarations through them) and every declaration's site count (zero-site ones included).
One file per process: a second `importModules` in the same process breaks elaboration.
-/

namespace FVA.Mutate

open Lean Elab

/-- Replace bytes `[start, stop)` of the file with `text`. -/
structure Edit where
  /-- First byte. -/
  start : Nat
  /-- One past the last byte. -/
  stop : Nat
  /-- Replacement text. -/
  text : String
deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- One first-order mutant. -/
structure Mutant where
  /-- File path, repo-relative. -/
  file : String
  /-- The declaration whose body holds the site. -/
  decl : String
  /-- Operator name (contract O1–O12). -/
  op : String
  /-- Index among this operator's mutants in this declaration. -/
  k : Nat
  /-- The edits, non-overlapping, ascending. -/
  edits : List Edit
  /-- Original text of the site. -/
  orig : String
  /-- Replacement text of the site. -/
  repl : String
  /-- 1-based line of the site. -/
  line : Nat
deriving Repr, Inhabited, ToJson, FromJson

/-- `<file>:<decl>:<op>:<k>`. -/
def Mutant.id (m : Mutant) : String := s!"{m.file}:{m.decl}:{m.op}:{m.k}"

/-- A command: byte range, kind tag and the declarations it introduces. -/
structure CmdInfo where
  /-- First byte. -/
  start : Nat
  /-- One past the last byte. -/
  stop : Nat
  /-- `def` `abbrev` `instance` `theorem` `example` `guard` `type` `other`. -/
  kind : String
  /-- Declared names (definitions and theorems; empty for other commands). -/
  names : List String
deriving Repr, Inhabited, ToJson, FromJson

/-- A declaration of the file and its number of sites (after `keep`). -/
structure DeclInfo where
  /-- Declared name. -/
  name : String
  /-- Kind tag, as in `CmdInfo`. -/
  kind : String
  /-- Mutants listed for it; `none` = not in scope (`keep` rejected it or not mutable). -/
  sites : Option Nat
deriving Repr, ToJson, FromJson

/-- Everything one file yields. -/
structure Listing where
  /-- The mutants, in id order within each declaration. -/
  mutants : Array Mutant
  /-- Every command. -/
  commands : Array CmdInfo
  /-- Every declaration with its site count. -/
  decls : Array DeclInfo
  /-- Frontend errors (the file must elaborate cleanly). -/
  errors : List String
deriving ToJson, FromJson

/-- A site before numbering: operator, edits, original + replacement text, start byte. -/
structure Site where
  /-- Operator name (`ROR`, `GIB`, …). -/
  op : String
  /-- Byte-range replacements that make the mutant. -/
  edits : List Edit
  /-- Original text of the mutated span. -/
  orig : String
  /-- Replacement text of the mutated span. -/
  repl : String
  /-- Start byte of the mutated span. -/
  pos : Nat

/-- Binary operator token → (operator name, replacements). -/
def binOps : List (String × String × List String) :=
  [("<", "ROR", ["≤"]), ("≤", "ROR", ["<"]), ("<=", "ROR", ["<"]), (">", "ROR", ["≥"]),
   ("≥", "ROR", [">"]), (">=", "ROR", [">"]),
   ("==", "EQN", ["!="]), ("!=", "EQN", ["=="]), ("=", "EQN", ["≠"]), ("≠", "EQN", ["="]),
   ("&&", "LCR", ["||"]), ("||", "LCR", ["&&"]), ("∧", "LCR", ["∨"]), ("∨", "LCR", ["∧"]),
   ("+", "AOR", ["-"]), ("-", "AOR", ["+"]), ("*", "AOR", ["/"]), ("/", "AOR", ["*"]),
   ("%", "AOR", ["/"]),
   ("&&&", "BIT", ["|||"]), ("|||", "BIT", ["&&&"]), ("^^^", "BIT", ["|||"]),
   ("<<<", "BIT", [">>>"]), (">>>", "BIT", ["<<<"])]

/-- Function name → (operator name, replacement). -/
def fnOps : List (Name × String × Name) :=
  [(`Nat.blt, "ROR", `Nat.ble), (`Nat.ble, "ROR", `Nat.blt), (`Nat.beq, "ROR", `Nat.blt),
   (`Nat.add, "AOR", `Nat.sub), (`Nat.sub, "AOR", `Nat.add), (`Nat.mul, "AOR", `Nat.div),
   (`Nat.div, "AOR", `Nat.mul), (`Nat.mod, "AOR", `Nat.div), (`min, "AOR", `max),
   (`max, "AOR", `min),
   (`Nat.land, "BIT", `Nat.lor), (`Nat.lor, "BIT", `Nat.land), (`Nat.xor, "BIT", `Nat.lor),
   (`Nat.shiftLeft, "BIT", `Nat.shiftRight), (`Nat.shiftRight, "BIT", `Nat.shiftLeft),
   (`true, "BOOL", `false), (`false, "BOOL", `true)]

/-- Last name component → replacement, any qualifier or method spelling (`Int.tdiv a b`,
`a.tdiv b`, `(e).tdiv b`): truncating vs floor/Euclidean integer division. -/
def fieldOps : List (String × String) :=
  [("tdiv", "fdiv"), ("fdiv", "tdiv"), ("tmod", "fmod"), ("fmod", "tmod"), ("ediv", "tdiv"),
   ("emod", "tmod")]

/-- Byte range of a syntax node with original source positions. -/
def range? (stx : Syntax) : Option (Nat × Nat) := do
  let r ← stx.getRange?
  return (r.start.byteIdx, r.stop.byteIdx)

/-- Source bytes `[a, b)`. -/
def slice (src : String) (a b : Nat) : String :=
  String.Pos.Raw.extract src ⟨a⟩ ⟨b⟩

/-- `n + 1` in the base of the literal `lit` (`0x`, `0b`, `0o` or decimal). -/
def bumpLit (lit : String) : Option String :=
  let digits (base : Nat) (s : String) : Option Nat :=
    s.foldl (fun acc c => acc.bind fun n =>
      let d := if c.isDigit then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none
      d.bind fun d => if d < base then some (n * base + d) else none) (some 0)
  let render (base : Nat) (pre : String) (s : String) : Option String := do
    let n ← digits base s
    let ds := Nat.toDigits base (n + 1)
    let ds := if s.any Char.isUpper then ds.map Char.toUpper else ds
    return pre ++ String.ofList ds
  let pre := (lit.take 2).toString
  let rest := (lit.drop 2).toString
  if pre == "0x" || pre == "0X" then render 16 pre rest
  else if pre == "0b" || pre == "0B" then render 2 pre rest
  else if pre == "0o" || pre == "0O" then render 8 pre rest
  else render 10 "" lit

/-- One-edit site replacing node `stx` with `text`. -/
def replaceNode (src : String) (op : String) (stx : Syntax) (text : String) : Option Site := do
  let (a, b) ← range? stx
  return { op, edits := [⟨a, b, text⟩], orig := slice src a b, repl := text, pos := a }

/-- Site deleting the prefix token of `node` (`!e`, `-e`): keeps its operand. -/
def dropPrefix (src : String) (op : String) (node : Syntax) : Option Site := do
  let (a, _) ← range? (← node.getArgs[0]?)
  let (ea, eb) ← range? (← node.getArgs[1]?)
  return { op, edits := [⟨a, ea, ""⟩], orig := slice src a eb, repl := slice src ea eb, pos := a }

/-- Sites of an identifier: function-name swaps, `true`/`false`, the division family's last
component, and a dropped trailing `.reverse`. -/
def identSites (src : String) (stx : Syntax) : List Site :=
  let n := stx.getId
  let fn := (fnOps.filter (·.1 == n)).filterMap fun (_, op, n') =>
    replaceNode src op stx n'.toString
  let field := match n with
    | .str p s =>
      if s == "reverse" then
        -- a capitalized qualifier is a namespace (`List.reverse`), not a receiver
        let ns := match p with
          | .str _ q => q.front.isUpper
          | _ => true
        if ns then [] else (replaceNode src "LST" stx p.toString).toList
      else if fn.isEmpty then
        (fieldOps.filter (·.1 == s)).filterMap fun (_, s') =>
          replaceNode src "AOR" stx (Name.str p s').toString
      else []
    | _ => []
  fn ++ field

/-- Sites at one node (not its children). -/
def sitesAt (src : String) (stx : Syntax) : List Site :=
  match stx with
  | .ident .. => identSites src stx
  | .node _ k args =>
    if k == `num then
      match (args[0]? : Option Syntax) with
      | some (Syntax.atom _ lit) =>
        let up := (bumpLit lit).bind (replaceNode src "LIT" stx ·)
        let down := if lit == "1" then replaceNode src "LIT" stx "0" else none
        up.toList ++ down.toList
      | _ => []
    else if k == ``boolIfThenElse || k == ``termIfThenElse then swap (args[3]?) (args[5]?)
    else if k == ``termDepIfThenElse then swap (args[5]?) (args[7]?)
    else if k == ``Lean.Parser.Term.matchAlts then
      let alts := ((args[0]? : Option Syntax).map (·.getArgs)).getD #[]
      let rhs := alts.toList.filterMap fun alt => alt.getArgs.back?
      (rhs.zip (rhs.drop 1)).filterMap fun (prev, cur) => do
        let (pa, pb) ← range? prev
        replaceNode src "GME" cur (slice src pa pb)
    else if k == `«term!_» then (dropPrefix src "BOOL" stx).toList
    else if k == `«term-_» then (dropPrefix src "NEG" stx).toList
    else if k == `«term[_]» then
      if (((args[1]? : Option Syntax).map (·.getArgs.size)).getD 0) > 0 then
        (replaceNode src "LST" stx "[]").toList
      else []
    else if k == ``Lean.Parser.Term.proj then
      let site : Option Site := do
        let e ← args[0]?
        let fld ← args[2]?
        let (ea, eb) ← range? e
        match fld.getId with
        | .str .anonymous "reverse" => replaceNode src "LST" stx (slice src ea eb)
        | .str .anonymous s => do
          let (_, s') ← fieldOps.find? (·.1 == s)
          replaceNode src "AOR" fld s'
        | _ => none
      site.toList
    else if k == ``Lean.Parser.Term.app then
      match (args[0]? : Option Syntax), ((args[1]? : Option Syntax).map (·.getArgs)) with
      | some f, some #[x] =>
        let fname := f.getId
        if fname == `some || fname == `Option.some ||
            (f.getKind == ``Lean.Parser.Term.dotIdent && f[1].getId == `some) then
          (replaceNode src "OPT" stx "none").toList
        else if fname == `List.reverse then
          match range? x with
          | some (xa, xb) => (replaceNode src "LST" stx (slice src xa xb)).toList
          | none => []
        else []
      | _, _ => []
    else if args.size == 3 then
      match (args[0]! : Syntax), (args[1]! : Syntax), (args[2]! : Syntax) with
      | l, Syntax.atom _ tok, r =>
        if tok == "::" then (replaceNode src "LST" stx (text r)).toList
        else if tok == "++" then
          [replaceNode src "LST" stx s!"{text r} ++ {text l}",
           replaceNode src "LST" stx (text l), replaceNode src "LST" stx (text r)].filterMap id
        else
          (binOps.filter (·.1 == tok)).flatMap fun (_, op, outs) =>
            outs.filterMap fun o => replaceNode src op args[1]! o
      | _, _, _ => []
    else []
  | _ => []
where
  /-- Source text of `s`, empty without a range. -/
  text (s : Syntax) : String := match range? s with
    | some (a, b) => slice src a b
    | none => ""
  /-- `GIB`: the two branches of an `if` exchanged. -/
  swap (t e : Option Syntax) : List Site := match t, e with
    | some t, some e => match range? t, range? e with
      | some (ta, tb), some (ea, eb) =>
        [{ op := "GIB", edits := [⟨ta, tb, slice src ea eb⟩, ⟨ea, eb, slice src ta tb⟩],
           orig := slice src ta eb, repl := slice src ea eb ++ slice src tb ea ++ slice src ta tb,
           pos := ta }]
      | _, _ => []
    | _, _ => []

/-- Children of `stx` that hold mutable terms: patterns, binders, types, proofs and termination
clauses are skipped. -/
def termChildren (stx : Syntax) : Array Syntax :=
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``Lean.Parser.Term.matchAlt then args.extract 3 4
  else if k == ``Lean.Parser.Term.matchDiscr then args.extract 1 2
  else if k == ``Lean.Parser.Term.basicFun then args.extract 3 4
  else if k == ``Lean.Parser.Term.letIdDecl || k == ``Lean.Parser.Term.letPatDecl ||
      k == ``Lean.Parser.Term.letEqnsDecl then
    args.extract (args.size - 1) args.size
  else if k == ``Lean.Parser.Term.typeAscription then args.extract 1 2
  else if k == ``Lean.Parser.Term.show then args.extract 2 3
  else if k == ``Lean.Parser.Term.doIdDecl then args.extract 3 4
  else if k == ``Lean.Parser.Term.doPatDecl then args.extract 3 5
  else if k == ``Lean.Parser.Term.byTactic || k == ``Lean.Parser.Term.byTactic' ||
      k == ``Lean.Parser.Term.motive || k == ``Lean.Parser.Termination.suffix ||
      k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder ||
      k == ``Lean.Parser.Term.instBinder || k == ``Lean.Parser.Term.strictImplicitBinder ||
      k == ``Lean.Parser.Term.typeSpec || k == ``Lean.Parser.Term.dotIdent then #[]
  else args

/-- Every site in the term `stx`, unordered. -/
partial def sitesIn (src : String) (stx : Syntax) : Array Site :=
  (termChildren stx).foldl (fun acc c => acc ++ sitesIn src c) (sitesAt src stx).toArray

/-- Kind tag of a declaration node (the second child of a `declaration` command). -/
def declKind (d : Syntax) : String :=
  let k := d.getKind
  if k == ``Lean.Parser.Command.definition then "def"
  else if k == ``Lean.Parser.Command.«abbrev» then "abbrev"
  else if k == ``Lean.Parser.Command.«instance» then "instance"
  else if k == ``Lean.Parser.Command.«theorem» || k.toString.endsWith "lemma" then "theorem"
  else if k == ``Lean.Parser.Command.«example» then "example"
  else if k == ``Lean.Parser.Command.«structure» || k == ``Lean.Parser.Command.«inductive» ||
      k == ``Lean.Parser.Command.classInductive then "type"
  else "other"

/-- The declarations of a command: (kind, declId syntax, body nodes). Bodies are empty for
every kind but `def`, `abbrev` and `instance`. -/
partial def declsOf (cmd : Syntax) : Array (String × Syntax × Array Syntax) :=
  let k := cmd.getKind
  if k == ``Lean.Parser.Command.mutual then (cmd[1].getArgs).flatMap declsOf
  else if k == ``Lean.Parser.Command.declaration then
    let d := cmd[1]
    match declKind d with
    | "def" => #[("def", d[1], valBodies d[3])]
    | "abbrev" => #[("abbrev", d[1], valBodies d[3])]
    | "instance" => #[("instance", d[3], valBodies d[5])]
    | "example" => #[("example", Syntax.missing, #[])]
    | kd => #[(kd, d[1], #[])]
  else #[]
where
  /-- `:= body [termination] [where …]` | `| pat => rhs …` | `where fields`. -/
  valBodies (v : Syntax) : Array Syntax :=
    let vk := v.getKind
    if vk == ``Lean.Parser.Command.declValSimple then #[v[1], v[3]]
    else if vk == ``Lean.Parser.Command.declValEqns then #[v[0]]
    else if vk == ``Lean.Parser.Command.whereStructInst then #[v[1], v[2]]
    else #[]

/-- Kind tag of a whole command. -/
def cmdKind (cmd : Syntax) : String :=
  match (declsOf cmd).toList with
  | (kd, _, _) :: _ => kd
  | [] =>
    match cmd.getAtomVal with
    | "#guard" | "#guard_expr" | "#guard_msgs" => "guard"
    | _ => if (cmd.getArg 0).getAtomVal.startsWith "#guard" then "guard" else "other"

/-- A command with its namespace and the constants it added. -/
structure Cmd where
  /-- The command's syntax. -/
  stx : Syntax
  /-- Namespace the command elaborated in. -/
  ns : Name
  /-- Constants the command added to the environment. -/
  newConsts : Array Name

/-- Elaborate `path` command by command; return the commands and the error messages. Needs the
search path initialized and initializers enabled (`unsafe` caller). -/
def elabFile (path : String) (src : String) : IO (Array Cmd × List String) := do
  let inputCtx := Parser.mkInputContext src path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let mut st : Frontend.State :=
    { commandState := Command.mkState env messages {}, parserState, cmdPos := parserState.pos }
  let mut cmds := #[]
  let mut done := false
  while !done do
    let ns := st.commandState.scopes.head!.currNamespace
    let before := st.commandState.env.constants.map₂
    let (d, st') ← (Frontend.processCommand.run { inputCtx }).run st
    st := st'
    done := d
    let new := st.commandState.env.constants.map₂.foldl
      (fun acc n _ => if before.contains n then acc else acc.push n) #[]
    cmds := cmds.push { stx := st.commands.back!, ns, newConsts := new }
  let errs ← st.commandState.messages.toList.filterMapM fun m => do
    if m.severity == .error then return some (← m.toString) else return none
  return (cmds, errs)

/-- Auxiliary constants Lean adds next to a declaration (matchers, equation lemmas, `_`-names,
private-name numerals). -/
def isAux (n : Name) : Bool :=
  n.componentsRev.any fun c => match c with
    | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
        s.startsWith "eq_" || s == "brecOn" || s == "below"
    | _ => true

/-- The constant a declaration introduces: `declId` in namespace `ns` (`_root_` drops the
namespace), matched against the constants the command added (a private name ends with it);
an anonymous instance takes the first added non-auxiliary constant. -/
def declName (ns : Name) (declId : Syntax) (added : Array Name) : Name :=
  let declId := if declId.getKind == nullKind then declId[0] else declId
  if declId.isMissing || declId.getNumArgs == 0 then
    (added.find? (!isAux ·)).getD .anonymous
  else
    let raw := declId[0].getId
    let full := if raw.getRoot == `_root_ then raw.replacePrefix `_root_ .anonymous else ns ++ raw
    if added.contains full then full else (added.find? (full.isSuffixOf ·)).getD full

/-- Drop sites whose edits change nothing or repeat an earlier site's edits. -/
def dedup (src : String) (sites : Array Site) : Array Site := Id.run do
  let mut seen : Array (List Edit) := #[]
  let mut out := #[]
  for s in sites do
    if s.edits.all (fun e => slice src e.start e.stop == e.text) || seen.contains s.edits then
      continue
    seen := seen.push s.edits
    out := out.push s
  return out

/-- List `path`: mutants of the definitions `keep` accepts, every command, every declaration. -/
def listFile (path : String) (keep : Name → Bool) : IO Listing := do
  let src ← IO.FS.readFile path
  let (cmds, errors) ← elabFile path src
  let fileMap := FileMap.ofString src
  let mut mutants := #[]
  let mut commands := #[]
  let mut decls := #[]
  for c in cmds do
    let some (a, b) := range? c.stx | continue
    let ds := declsOf c.stx
    let names := ds.toList.map fun (_, declId, _) => (declName c.ns declId c.newConsts).toString
    commands := commands.push { start := a, stop := b, kind := cmdKind c.stx, names }
    for (kd, declId, bodies) in ds do
      let n := declName c.ns declId c.newConsts
      if bodies.isEmpty || !keep n then
        decls := decls.push { name := n.toString, kind := kd, sites := none }
        continue
      let sites := dedup src ((bodies.flatMap (sitesIn src)).qsort fun x y =>
        x.pos < y.pos || (x.pos == y.pos && (x.op < y.op || (x.op == y.op && x.repl < y.repl))))
      let mut counts : Std.HashMap String Nat := {}
      for s in sites do
        let k := counts.getD s.op 0
        counts := counts.insert s.op (k + 1)
        mutants := mutants.push
          { file := path, decl := n.toString, op := s.op, k := k, edits := s.edits,
            orig := s.orig, repl := s.repl, line := (fileMap.toPosition ⟨s.pos⟩).line }
      decls := decls.push { name := n.toString, kind := kd, sites := some sites.size }
  return { mutants, commands, decls, errors }

/-- Apply a mutant's edits to the original source. -/
def Mutant.apply (m : Mutant) (src : String) : String := Id.run do
  let mut out := ""
  let mut pos := 0
  for e in m.edits do
    out := out ++ slice src pos e.start ++ e.text
    pos := e.stop
  return out ++ slice src pos src.utf8ByteSize

end FVA.Mutate
