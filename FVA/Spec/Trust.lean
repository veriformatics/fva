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

/-- A module of the review surface. -/
structure ReviewModule where
  /-- Module name. -/
  module : String
  /-- Syntax, macro or elaborator declarations in it. -/
  syntaxExts : List String
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

/-- One lifted module and the artifact it claims to be. -/
structure Link where
  /-- The `Lifted.lean` file. -/
  file : String
  /-- The `.wasm` file exists. -/
  wasmPresent : Bool
  /-- The `bytes` numeral packs exactly the file's bytes. -/
  bytesMatch : Bool
  /-- `len` = the file's size. -/
  lenMatch : Bool
  /-- `decode_eq : decode bytes len = .ok module` exists with exactly that type. -/
  decodeEq : Bool
  /-- The file is exactly `fva lift`'s output for the `.wasm` (no added declaration or syntax). -/
  relifts : Bool
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
  /-- Syntax, macro or elaborator declarations in subject modules the spec module imports
  (unreviewed text that could change how the spec reads). -/
  subjectSyntax : List String
  /-- Names outside the project the claims' statements use (informational, D10). -/
  vocabulary : List Term
  /-- `[prelude]` violations: fixed-bundle constants outside the sysroot, modules without `Init`. -/
  prelude : List String
  /-- The project's subjects are lifted artifacts (Lean-native subjects need no link). -/
  needsLink : Bool
  /-- Its lifted modules. -/
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
  syntax_ : (∀ m ∈ r.reviewModules, m.syntaxExts = []) ∧ r.subjectSyntax = []
  prelude : r.prelude = []
  link : (r.needsLink = true → r.links ≠ []) ∧
    ∀ l ∈ r.links, l.wasmPresent = true ∧ l.bytesMatch = true ∧ l.lenMatch = true ∧
      l.decodeEq = true ∧ l.relifts = true
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
