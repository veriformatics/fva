import FVA.Spec.Trust

/-!
# Trust verdict (verified implementation)

`issues r` lists every violated rule of `FVA.Trust.Pass` with its tag; `verdict r` passes iff
there is none. `FVA.Proof.Trust` proves `verdict r = .pass ↔ Pass r`, so the verdict is exactly
the reviewed spec over the collected facts.
-/

namespace FVA.Trust

/-- One violated rule: its tag and what violates it. -/
structure Issue where
  /-- Rule tag (contract V2). -/
  tag : String
  /-- The violating fact. -/
  detail : String
deriving Repr, Inhabited

/-- The verdict. -/
inductive Verdict where
  | pass | fail
deriving Repr, DecidableEq, Inhabited

/-- `Status.Bad`, decided. -/
def Status.bad : Status → Bool
  | .reject | .crash | .timeout => true
  | .accept | .decline => false

/-- Status name for reports. -/
def Status.name : Status → String
  | .accept => "accepted"
  | .reject => "rejected"
  | .decline => "declined"
  | .crash => "crashed"
  | .timeout => "timed out"

/-- The failed parts of a link check, for the report. -/
def Link.problems (l : Link) : List String :=
  (if l.present then [] else ["the file is missing or outside the project"]) ++
  (if l.bytesMatch then [] else ["`bytes` is not the file's bytes"]) ++
  (if l.lenMatch then [] else ["`len` is not the file's size"]) ++
  (if l.kind != .wasm || l.decodeEq then [] else ["`decode_eq` is missing or mistyped"]) ++
  (if l.regenerates then [] else ["the module is not its generator's output for the file"])

/-- A link check passes. -/
def Link.ok (l : Link) : Bool :=
  l.present && l.bytesMatch && l.lenMatch && (l.kind != .wasm || l.decodeEq) && l.regenerates

/-- A canary accepted by `c.kernel` is covered: a known defect another kernel rejects. -/
def canaryCovered (cs : List CanaryRun) (c : CanaryRun) : Bool :=
  c.knownAccept && cs.any fun d => d.canary == c.canary && d.status == .reject

/-! ## One function per rule of `Pass` (contract V2), each listing its violations -/

/-- `[build]`. -/
def ruleBuild (r : Report) : List Issue :=
  if r.built then [] else [⟨"build", "the project does not build"⟩]

/-- No claim at all. -/
def ruleClaims (r : Report) : List Issue :=
  if r.claims.isEmpty then [⟨"claims", "the spec module declares no claim"⟩] else []

/-- `[unproven]`. -/
def ruleUnproven (r : Report) : List Issue :=
  r.claims.flatMap fun c =>
    if c.proofs.isEmpty then [⟨"unproven", s!"{c.name} has no proof"⟩] else []

/-- `[axiom]`. -/
def ruleAxiom (r : Report) : List Issue :=
  r.claims.flatMap fun c => c.proofs.flatMap fun p =>
    (p.axioms.filter (!standardAxioms.contains ·)).map fun a =>
      ⟨"axiom", s!"{p.name} (proof of {c.name}) depends on {a}"⟩

/-- `[vacuous]`. -/
def ruleVacuous (r : Report) : List Issue :=
  r.claims.flatMap fun c =>
    if c.subjects.isEmpty then [⟨"vacuous", s!"{c.name} never mentions a subject"⟩] else []

/-- `[layout]`. -/
def ruleLayout (r : Report) : List Issue :=
  r.claims.flatMap fun c =>
    if c.provenInSpec then [⟨"layout", s!"{c.name} is proven inside the spec module"⟩] else []

/-- `[override]`. -/
def ruleOverride (r : Report) : List Issue :=
  r.flags.map fun f => ⟨"override", s!"{f.decl} ({f.module}) is {f.kind}"⟩

/-- `[syntax]`. -/
def ruleSyntax (r : Report) : List Issue :=
  r.reviewModules.flatMap (fun m =>
    if m.syntaxExts.isEmpty then []
    else [⟨"syntax", s!"{m.module} extends syntax: {", ".intercalate m.syntaxExts}"⟩]) ++
  if r.subjectSyntax.isEmpty then []
  else [⟨"syntax", s!"subject modules extend syntax: {", ".intercalate r.subjectSyntax}"⟩]

/-- `[prelude]`. -/
def rulePrelude (r : Report) : List Issue :=
  r.prelude.map fun p => ⟨"prelude", p⟩

/-- `[link]`. -/
def ruleLink (r : Report) : List Issue :=
  (if r.needsLink && r.links.isEmpty then [⟨"link", "no generated module in the project"⟩]
   else []) ++
  r.links.flatMap fun l =>
    if l.ok then [] else [⟨"link", s!"{l.file}: {"; ".intercalate l.problems}"⟩]

/-- `[replay]`. -/
def ruleReplay (r : Report) : List Issue :=
  [if r.exportOk then [] else [⟨"replay", "the export failed"⟩],
   r.replay.flatMap (fun k =>
     if k.status.bad then [⟨"replay", s!"{k.kernel} {k.status.name} the export"⟩] else []),
   if r.replay.any (fun k => k.status == .accept && k.lineage != "lean") then []
   else [⟨"replay", "no kernel outside Lean's own lineage accepted the export"⟩]].flatten

/-- Pinned canaries run-set kernel `k` did not decide (never run, or timed out). -/
def untested (r : Report) (k : KernelRun) : List String :=
  r.canarySet.filter fun n =>
    !r.canaries.any fun c => c.kernel == k.kernel && c.canary == n && c.status != .timeout

/-- `[checker]`. -/
def ruleChecker (r : Report) : List Issue :=
  (if r.canarySet.isEmpty then [⟨"checker", "no pinned canary set: the kernels are untested"⟩]
   else []) ++
  r.replay.flatMap (fun k => match untested r k with
    | [] => []
    | n :: ns => [⟨"checker", s!"{k.kernel} did not decide {ns.length + 1} pinned canaries " ++
        s!"(first: {n}; missing file: scripts/fetch-canaries; timeout: --canary-limit)"⟩]) ++
  r.canaries.flatMap fun c =>
    if c.status == .accept && !canaryCovered r.canaries c then
      [⟨"checker", s!"{c.kernel} accepted the known-false canary {c.canary}"⟩]
    else []

/-- `[surface]`: a review module whose source was not read. -/
def ruleSources (r : Report) : List Issue :=
  r.reviewModules.flatMap fun m =>
    if m.found then [] else [⟨"surface", s!"{m.module}: source file not found"⟩]

/-- `[surface]`: the budget. -/
def ruleBudget (r : Report) : List Issue :=
  match r.budget with
  | some b =>
    if r.surfaceLines ≤ b then []
    else [⟨"surface", s!"{r.surfaceLines} code lines to review, budget {b}"⟩]
  | none => []

/-- `[surface]`. -/
def ruleSurface (r : Report) : List Issue := ruleSources r ++ ruleBudget r

/-- Every violated rule, in tag order. -/
def issues (r : Report) : List Issue :=
  [ruleBuild r, ruleClaims r, ruleUnproven r, ruleAxiom r, ruleVacuous r, ruleLayout r,
   ruleOverride r, ruleSyntax r, rulePrelude r, ruleLink r, ruleReplay r, ruleChecker r,
   ruleSurface r].flatten

/-- PASS iff no rule is violated. -/
def verdict (r : Report) : Verdict := if (issues r).isEmpty then .pass else .fail

end FVA.Trust
