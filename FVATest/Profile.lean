import Lean.Data.Json
import FVA.Profile

/-!
# Profile classifier (unverified test glue, contract U28a E6)

Decides P′ membership from `wasm-tools print`'s text alone, independently of FVA's decoder, so
the decoder's verdict on the same bytes can be checked against it (test-decoder E2; the runner's
in-profile test, U28e). The text becomes s-expressions with strings, `$` identifiers and
comments dropped; a module is in P′ unless a node shows an excluded class; every class shown is
listed, since the decoder reports the first one it meets in byte order.
-/

namespace FVA.Test.Profile

open FVA.Profile

/-- WAT text as atoms and parenthesized lists. -/
inductive SExp where
  | atom (s : String)
  | list (xs : List SExp)

/-- Characters that end an atom. -/
def stop (c : Char) : Bool := c.isWhitespace || c == '(' || c == ')' || c == '"' || c == ';'

/-- The index after a string literal opening at `i` (`"` at `i`; `\` escapes one character). -/
partial def skipString (s : Array Char) (i : Nat) : Nat :=
  let rec go (j : Nat) : Nat :=
    if h : j < s.size then
      if s[j] == '\\' then go (j + 2) else if s[j] == '"' then j + 1 else go (j + 1)
    else j
  go (i + 1)

/-- The index after a block comment opening at `i` (`(;` at `i`; comments nest). -/
partial def skipBlock (s : Array Char) (i : Nat) : Nat :=
  let rec go (j depth : Nat) : Nat :=
    if j + 1 < s.size then
      if s[j]! == '(' && s[j + 1]! == ';' then go (j + 2) (depth + 1)
      else if s[j]! == ';' && s[j + 1]! == ')' then
        (if depth == 1 then j + 2 else go (j + 2) (depth - 1))
      else go (j + 1) depth
    else s.size
  go i 0

/-- Tokens: `(`, `)` and atoms; strings, `$` identifiers and comments dropped. -/
partial def tokens (text : String) : Array String := Id.run do
  let s := text.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < s.size do
    let c := s[i]!
    if c.isWhitespace then i := i + 1
    else if c == '(' && i + 1 < s.size && s[i + 1]! == ';' then i := skipBlock s i
    else if c == ';' && i + 1 < s.size && s[i + 1]! == ';' then
      while i < s.size && s[i]! != '\n' do i := i + 1
    else if c == '(' || c == ')' then
      out := out.push c.toString
      i := i + 1
    else if c == '"' then i := skipString s i
    else if c == '$' && i + 1 < s.size && s[i + 1]! == '"' then i := skipString s (i + 1)
    else
      let start := i
      while i < s.size && !stop s[i]! do i := i + 1
      if i == start then i := i + 1
      else if c != '$' then out := out.push (String.ofList (s.extract start i).toList)
  return out

/-- Parse tokens into the list of top-level expressions (unbalanced input: best effort). -/
def parse (ts : Array String) : List SExp := Id.run do
  let mut stack : List (List SExp) := [[]]
  for t in ts do
    if t == "(" then stack := [] :: stack
    else if t == ")" then
      match stack with
      | top :: parent :: rest => stack := (SExp.list top.reverse :: parent) :: rest
      | _ => pure ()
    else
      match stack with
      | top :: rest => stack := (SExp.atom t :: top) :: rest
      | [] => pure ()
  -- unclosed lists close at the end of the text
  let mut st := stack
  for _ in [0:stack.length] do
    match st with
    | top :: parent :: rest => st := (SExp.list top.reverse :: parent) :: rest
    | _ => pure ()
  match st with
  | top :: _ => top.reverse
  | [] => []

mutual
/-- Every atom of an expression, in order. -/
def SExp.atoms : SExp → List String
  | .atom s => [s]
  | .list xs => atomsL xs
/-- Every atom of a list of expressions. -/
def atomsL : List SExp → List String
  | [] => []
  | x :: xs => x.atoms ++ atomsL xs
end

mutual
/-- Every list node of an expression, the expression itself first. -/
def SExp.lists : SExp → List (List SExp)
  | .atom _ => []
  | .list xs => xs :: listsL xs
/-- Every list node of a list of expressions. -/
def listsL : List SExp → List (List SExp)
  | [] => []
  | x :: xs => x.lists ++ listsL xs
end

/-- Atoms only GC types spell (`final` alone: a final type without supertypes prints as a bare
function type, so `sub` marks every excluded sub type). -/
def gcTypeAtoms : List String :=
  ["sub", "struct", "array", "field", "i8", "i16", "any", "eq", "i31", "none", "anyref", "eqref",
   "i31ref", "structref", "arrayref", "nullref"]

/-- Atoms naming a bottom heap type. -/
def bottomAtoms : List String :=
  ["nofunc", "noextern", "noexn", "nullfuncref", "nullexternref", "nullexnref"]

/-- An atom naming a GC instruction. -/
def gcInstr (a : String) : Bool :=
  ["struct.", "array.", "i31.", "ref.i31", "ref.test", "ref.cast", "br_on_cast",
   "any.convert_extern", "extern.convert_any"].any (fun p => a.startsWith p) || a == "ref.eq"

/-- An atom naming a SIMD type or instruction. -/
def simdAtom (a : String) : Bool :=
  a == "v128" || ["v128.", "i8x16.", "i16x8.", "i32x4.", "i64x2.", "f32x4.", "f64x2."].any
    fun p => a.startsWith p

/-- An atom naming a shared memory or an atomic instruction. -/
def threadsAtom (a : String) : Bool :=
  a == "shared" || (a.splitOn ".atomic.").length > 1 || a.startsWith "atomic." ||
    a.startsWith "memory.atomic."

/-- A memory or table declaration (or import) whose address type is `i64`. -/
def addr64 (xs : List SExp) : Bool :=
  match xs with
  | .atom h :: rest => (h == "memory" || h == "table") &&
    (match rest with | .atom "i64" :: _ => true | _ => false)
  | _ => false

/-- A decimal atom (an index the printer writes, `wasm-tools print` omitting memory 0). -/
def index? (a : String) : Bool := !a.isEmpty && a.all Char.isDigit

/-- Load and store mnemonics (`i32.load8_u`, `f64.store`, …), whose memory index the printer
writes right after the mnemonic. -/
def memAccess (a : String) : Bool :=
  ["i32.", "i64.", "f32.", "f64."].any (fun p => a.startsWith p) &&
    ((a.splitOn ".load").length > 1 || (a.splitOn ".store").length > 1)

/-- An instruction naming a memory other than 0: `memory.size/grow/fill/copy` or a load/store
followed by an index, `memory.init` followed by two (memory, data). -/
def otherMemory : List String → Bool
  | a :: b :: c :: rest =>
    ((a == "memory.size" || a == "memory.grow" || a == "memory.fill" || a == "memory.copy" ||
        memAccess a) && index? b) ||
      (a == "memory.init" && index? b && index? c) || otherMemory (b :: c :: rest)
  | [a, b] =>
    (a == "memory.size" || a == "memory.grow" || a == "memory.fill" || a == "memory.copy" ||
      memAccess a) && index? b
  | _ => false

/-- Memories the module declares or imports (more than one = validation's exclusion, which the
runner's in-profile test adds, U28e). -/
def memoryCount (top : List SExp) : Nat :=
  let modBody := match top with
    | [.list (.atom "module" :: body)] => body
    | _ => top
  modBody.foldl (fun n x => match x with
    | .list (.atom "memory" :: _) => n + 1
    | .list (.atom "import" :: rest) =>
      n + (rest.filter fun y =>
        match y with | .list (.atom "memory" :: _) => true | _ => false).length
    | _ => n) 0

/-- Every excluded class the parsed module text shows, the decoder's syntax boundary; `[]` = P′
syntax. -/
def classify (top : List SExp) : List Excluded :=
  let atoms := atomsL top
  let lists := listsL top
  let shows : Excluded → Bool
    | .gcTypes => atoms.any gcTypeAtoms.contains
    | .bottomTypes => atoms.any bottomAtoms.contains
    | .gcInstrs => atoms.any gcInstr
    | .simd => atoms.any simdAtom
    | .threads => atoms.any threadsAtom
    | .memory64 => lists.any addr64
    | .multiMemory => otherMemory atoms
    | .legacyEh => atoms.any fun a => a == "try" || a == "delegate" || a == "rethrow"
  Excluded.all.filter shows

/-- The manifest as JSON (`fvatest profile`). -/
def manifest : Lean.Json :=
  Lean.Json.mkObj
    [ ("version", Lean.toJson version), ("spec", Lean.toJson specPin),
      ("testsuite", Lean.toJson testsuitePin), ("included", Lean.toJson included),
      ("excluded", Lean.toJson (Excluded.all.map Excluded.id)),
      ("wasmToolsFeatures", Lean.toJson wasmToolsFeatures),
      ("wasmtimeFlags", Lean.toJson wasmtimeFlags) ]

/-- `fvatest classify <file.wasm>…`: `file<TAB>verdict<TAB>memories` per file, the verdict =
`p-prime`, `print-failed` or the excluded classes joined by `,`; memories = the declared + imported
memory count (U28e's static profile; `-` when printing failed). Custom sections are stripped
first: with a name section the printer names a memory (`i32.load $two`), and names carry no index
the classifier could read. -/
def run (files : List String) : IO UInt32 := do
  for f in files do
    let out ← IO.FS.withTempFile fun _ tmp => do
      let strip ← IO.Process.output
        { cmd := "wasm-tools", args := #["strip", "--all", f, "-o", tmp.toString] }
      if strip.exitCode != 0 then return strip
      IO.Process.output { cmd := "wasm-tools", args := #["print", tmp.toString] }
    let (verdict, mems) := if out.exitCode != 0 then ("print-failed", "-") else
      let top := parse (tokens out.stdout)
      (match classify top with
        | [] => "p-prime"
        | cs => ",".intercalate (cs.map Excluded.id), toString (memoryCount top))
    IO.println s!"{f}\t{verdict}\t{mems}"
  return 0

end FVA.Test.Profile
