/-!
# Trust verdict specification (reviewed once)

What a `fva trust` PASS means (contract `docs/contracts/U7-trust.md`, V1–V3): the report's facts
satisfy every rule below. The facts are collected by unverified glue (`FVA.Trust.Collect`,
`FVA.Trust.Replay`); the verdict over them is computed by `FVA.Trust.verdict`, proven equal to
`Pass` (`FVA.Trust.verdict_pass_iff`). Names are plain strings, so this file imports nothing:
it enters every project's import closure through the FVA root.
-/

namespace FVA.Trust

/-- The axioms a proof may use: Lean's three standard axioms. -/
def standardAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

/-- One theorem whose type is a claim constant. -/
structure Proof where
  /-- Theorem name. -/
  name : String
  /-- Every axiom its value depends on, transitively. -/
  axioms : List String
deriving Repr, Inhabited

/-- One claim: a Prop-valued definition of the spec module. -/
structure Claim where
  /-- Claim constant. -/
  name : String
  /-- A theorem declared in the spec module proves it (its proof text would be reviewed). -/
  provenInSpec : Bool
  /-- Its proofs. -/
  proofs : List Proof
  /-- The subject modules its statement closure mentions. -/
  subjects : List String
deriving Repr, Inhabited

/-- `implemented_by`, `extern`, `unsafe`, `partial` or `opaque` on a declaration outside Lean
core that a claim or proof reaches. -/
structure Flag where
  /-- Declaration. -/
  decl : String
  /-- Its module. -/
  module : String
  /-- Which override. -/
  kind : String
deriving Repr, Inhabited

/-- Commands and terms that run code while a module elaborates (`#eval`, `run_cmd`, `by_elab`,
Mathlib's `eval%`, …) or when a later module imports it (`initialize`), stop its elaboration
(`#exit`), change how it elaborates (`set_option`, `unlock_limits`), mark code for compile-time
use (`meta`, `unsafe`), declare syntax, macros, elaborators or notation, or read a file into a
term (`include_str`). The reviewed text must be the spec, so none belongs in a review module. -/
def commandTokens : List String :=
  ["#eval", "#eval!", "#exit", "run_cmd", "run_elab", "run_meta", "run_tac", "run_tacq",
   "by_elab", "by_elabq", "eval%", "include_str", "set_option", "unlock_limits", "meta",
   "unsafe", "initialize", "builtin_initialize", "syntax", "macro", "macro_rules", "elab",
   "elab_rules", "notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix",
   "declare_syntax_cat", "binder_predicate"]

/-- Attribute names that register code run while later text elaborates or prints: macros,
tactics, delaborators, formatters, initializers, `do`-element and `grind` extensions. -/
def attributeTokens : List String :=
  ["macro", "tactic", "delab", "init", "formatter", "parenthesizer", "doElem_control_info",
   "sym_simproc", "sym_dsimproc", "sym_discharger"]

/-- Name suffixes of the same attribute families (`term_elab`, `command_parser`, `grind_tactic`,
`app_unexpander`, `combinator_formatter`, …). -/
def attributeSuffixes : List String :=
  ["_elab", "_parser", "_tactic", "_delab", "_unexpander", "_formatter", "_parenthesizer"]

/-- An attribute that registers such code: listed, of a listed family, or one of Lean's own
`builtin_` registrations. -/
def registersCode (a : String) : Bool :=
  attributeTokens.contains a || attributeSuffixes.any (fun s => a.endsWith s) ||
    a.startsWith "builtin_"

/-- A module of the review surface. -/
structure ReviewModule where
  /-- Module name. -/
  module : String
  /-- Syntax, macro, elaborator and initializer declarations in it. -/
  syntaxExts : List String
  /-- Each place its source code (comments and doc comments aside; the terms interpolated into
  string literals included) uses a token of `commandTokens` or, as an attribute name, one that
  `registersCode` accepts: the token and its line. -/
  commands : List String
  /-- Its source file was found and read (else its lines are unknown). -/
  found : Bool
  /-- Code lines a reviewer reads. -/
  codeLines : Nat
deriving Repr, Inhabited

/-- A name outside the project that a claim's statement uses: its meaning is read from its
documentation, not from the review surface (D10). -/
structure Term where
  /-- Constant. -/
  name : String
  /-- Its module. -/
  module : String
  /-- `core`, `mathlib` or `base`. -/
  origin : String
  /-- First line of its docstring (empty when it has none). -/
  doc : String
deriving Repr, Inhabited

/-- What a link binds: a WebAssembly artifact the claims are about (`fva lift`), or a file a
certificate accepts as its input or output (`fva blob`). -/
inductive LinkKind where
  | wasm | blob
deriving Repr, DecidableEq, Inhabited

/-- One generated module and the file it claims to hold. -/
structure Link where
  /-- The generated module, with the file it names. -/
  file : String
  /-- A lifted artifact or a certificate blob. -/
  kind : LinkKind
  /-- The file exists inside the project. -/
  present : Bool
  /-- The `bytes` numeral packs exactly the file's bytes. -/
  bytesMatch : Bool
  /-- `len` = the file's size. -/
  lenMatch : Bool
  /-- For a lifted module: `decode_eq : decode bytes len = .ok module` exists with exactly that
  type (a blob has none). -/
  decodeEq : Bool
  /-- The module is exactly its generator's output for the file (no added declaration or
  syntax). -/
  regenerates : Bool
deriving Repr, Inhabited

/-- What a kernel said about an export. -/
inductive Status where
  | accept | reject | decline | crash | timeout
deriving Repr, DecidableEq, Inhabited

/-- One kernel run on the project's export. -/
structure KernelRun where
  /-- Kernel name. -/
  kernel : String
  /-- Implementation lineage: `"lean"` for Lean's own kernel family. -/
  lineage : String
  /-- Its verdict. -/
  status : Status
deriving Repr, Inhabited

/-- One kernel run on a canary (a known-false export). -/
structure CanaryRun where
  /-- Kernel name. -/
  kernel : String
  /-- Canary name (an entry of `Report.canarySet`). -/
  canary : String
  /-- Its verdict. -/
  status : Status
  /-- The canary table lists this acceptance as a known defect of this kernel. -/
  knownAccept : Bool
deriving Repr, Inhabited

/-- Every fact the verdict depends on. -/
structure Report where
  /-- The project built. -/
  built : Bool
  /-- The spec module's claims. -/
  claims : List Claim
  /-- Overrides in the audited closure. -/
  flags : List Flag
  /-- The review surface. -/
  reviewModules : List ReviewModule
  /-- Syntax, macro, elaborator and initializer declarations in subject modules the spec module
  imports (unreviewed text that could change how the spec reads). -/
  subjectSyntax : List String
  /-- `Prop` definitions of the spec module without `@[fva_claim]` (informational, D13): read as
  vocabulary, never proven. -/
  unmarked : List String
  /-- Instances and coercions of subject modules that the claims' statements use (D8):
  unreviewed definitions that fix what notation and casts in the spec mean. An instance passed
  straight to a subject function is that function's input; `Decidable` instances are
  subsingletons. Neither is listed. -/
  subjectMeaning : List String
  /-- Names outside the project the claims' statements use (informational, D10). -/
  vocabulary : List Term
  /-- `[prelude]` violations: fixed-bundle constants outside the sysroot, modules without `Init`. -/
  prelude : List String
  /-- `[olean]` violations: imported modules counted as Mathlib or FVA base whose compiled files
  are not the pinned bytes (FVA's Mathlib cache, FVA's own build of its base), and the spec
  module + its imports outside Lean core, Mathlib and FVA base whose compiled files are not
  FVA's build of their source. -/
  tampered : List String
  /-- The project's subjects are generated modules (Lean-native subjects need no link). -/
  needsLink : Bool
  /-- Its generated modules (lifted artifacts and certificate blobs). -/
  links : List Link
  /-- The export of claims, proofs and the fixed bundle succeeded. -/
  exportOk : Bool
  /-- Kernel runs on the export. -/
  replay : List KernelRun
  /-- Kernel runs on the canaries. -/
  canaries : List CanaryRun
  /-- The pinned canary set: every run-set kernel must decide each (a timeout decides none). -/
  canarySet : List String
  /-- The surface budget, if any. -/
  budget : Option Nat
deriving Repr, Inhabited

/-- The review surface's size in code lines. -/
def Report.surfaceLines (r : Report) : Nat := (r.reviewModules.map (·.codeLines)).sum

/-- A status that withholds acceptance without refuting it. -/
def Status.Bad (s : Status) : Prop := s = .reject ∨ s = .crash ∨ s = .timeout

/-- The PASS rules (contract V2, one conjunct per tag). -/
structure Pass (r : Report) : Prop where
  build : r.built = true
  claims : r.claims ≠ []
  unproven : ∀ c ∈ r.claims, c.proofs ≠ []
  axiom_ : ∀ c ∈ r.claims, ∀ p ∈ c.proofs, ∀ a ∈ p.axioms, a ∈ standardAxioms
  vacuous : ∀ c ∈ r.claims, c.subjects ≠ []
  layout : ∀ c ∈ r.claims, c.provenInSpec = false
  override : r.flags = []
  syntax_ : (∀ m ∈ r.reviewModules, m.syntaxExts = [] ∧ m.commands = []) ∧ r.subjectSyntax = []
  subject : r.subjectMeaning = []
  prelude : r.prelude = []
  olean : r.tampered = []
  link : (r.needsLink = true → r.links ≠ []) ∧
    ∀ l ∈ r.links, l.present = true ∧ l.bytesMatch = true ∧ l.lenMatch = true ∧
      (l.kind = .wasm → l.decodeEq = true) ∧ l.regenerates = true
  replay : r.exportOk = true ∧ (∀ k ∈ r.replay, ¬ k.status.Bad) ∧
    ∃ k ∈ r.replay, k.status = .accept ∧ k.lineage ≠ "lean"
  checker : r.canarySet ≠ [] ∧
    (∀ k ∈ r.replay, ∀ n ∈ r.canarySet,
      ∃ c ∈ r.canaries, c.kernel = k.kernel ∧ c.canary = n ∧ c.status ≠ .timeout) ∧
    ∀ c ∈ r.canaries, c.status = .accept →
      c.knownAccept = true ∧ ∃ d ∈ r.canaries, d.canary = c.canary ∧ d.status = .reject
  surface : (∀ m ∈ r.reviewModules, m.found = true) ∧
    ∀ b, r.budget = some b → r.surfaceLines ≤ b

end FVA.Trust
