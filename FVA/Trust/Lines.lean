import Lean
import FVA.Spec.Trust

/-!
# Code lines and listed commands of a Lean source (trusted glue, D11, U36)

Read by Lean's own tokenizer: `Lean.Parser.whitespace` skips whitespace and comments exactly as
Lean's parser does, `Lean.Parser.tokenFn` reads one token (string, char and raw-string literals,
`«…»` names, identifiers, numbers, the token table's symbols). Doc comments (`/-- … -/`,
`/-! … -/`) are tokens to Lean but comments to a reader. A character the tokenizer rejects counts
as code: the collector imports no parser extension, so a symbol of Mathlib notation is unknown to
its table, and Mathlib's keywords read as identifiers of the same text.
-/

namespace FVA.Trust

open Lean Parser

/-- A byte range of a source. -/
abbrev Span := String.Pos.Raw × String.Pos.Raw

/-- One tokenizer step: the end of input, a character or doc comment skipped (and where to go
on), or a code token's span and the position after it. -/
inductive Step where
  | stop
  | skip (next : String.Pos.Raw)
  | token (a b next : String.Pos.Raw)

/-- The tokenizer step from `pos` in `ictx` by token table `tokens`. -/
def step (env : Environment) (tokens : TokenTable) (ictx : InputContext) (pos : String.Pos.Raw) :
    Step :=
  let run (p : ParserFn) (pos : String.Pos.Raw) : ParserState :=
    p.run ictx { env, options := {} } tokens ((mkParserState ictx.inputString).setPos pos)
  if ictx.atEnd pos then .stop
  else
    let s := run whitespace pos
    let p := s.pos
    if ictx.atEnd p then .stop
    -- a tab or carriage return outside a literal (Lean rejects the file): skip it
    else if s.hasError then .skip (ictx.next p)
    else if ictx.get p == '/' && ictx.get (ictx.next p) == '-' &&
        (ictx.get (ictx.next (ictx.next p)) == '-' || ictx.get (ictx.next (ictx.next p)) == '!')
    then
      let s := run (finishCommentBlock (pushMissingOnError := false) 1) (ictx.next (ictx.next p))
      if s.hasError then .stop else .skip s.pos
    else
      let s := run (tokenFn []) p
      match s.hasError, s.stxStack.back.getPos?, s.stxStack.back.getTailPos? with
      | false, some a, some b => .token a b s.pos
      | _, _, _ => .token p (ictx.next p) (ictx.next p)

/-- Byte ranges of the code tokens of `src`, in order, by `env`'s token table. -/
partial def codeSpans (env : Environment) (src : String) : Array Span :=
  let ictx := mkInputContext src "<source>" (normalizeLineEndings := false)
  let tokens := getTokenTable env
  let rec go (pos : String.Pos.Raw) (acc : Array Span) :=
    match step env tokens ictx pos with
    | .stop => acc
    | .skip n => go n acc
    | .token a b n => go n (acc.push (a, b))
  go 0 #[]

/-- Each character of `src` with whether it lies inside a code span. -/
def withSpans (env : Environment) (src : String) : List (Char × Bool) := Id.run do
  let spans := codeSpans env src
  let mut out := #[]
  let mut k := 0
  let mut p : Nat := 0
  for c in src.toList do
    -- past the spans that end by `p` (a bounded walk: each span once)
    for _ in [k:spans.size] do
      if (spans[k]?.map fun sp => decide (sp.2.byteIdx ≤ p)).getD false then k := k + 1 else break
    out := out.push (c, (spans[k]?.map fun sp => decide (sp.1.byteIdx ≤ p)).getD false)
    p := p + c.utf8Size
  return out.toList

/-- Code lines of a Lean source (D11): lines holding a non-blank character of a code token;
comments and doc comments count nothing, string, char and `«…»` contents count as code. -/
def codeLines (env : Environment) (src : String) : Nat := Id.run do
  let mut n := 0
  let mut code := false
  for (c, inCode) in withSpans env src do
    if c == '\n' then
      if code then n := n + 1
      code := false
    else if inCode && !c.isWhitespace then code := true
  if code then n := n + 1
  return n

/-- A Lean source without its comments and doc comments, line breaks kept: outside the code
spans lie only whitespace and comments, so a line or block comment opener there always opens one. -/
def stripComments (env : Environment) (src : String) : String := Id.run do
  let mut out := ""
  let mut depth := 0
  let mut line := false
  let mut prev := ' '
  for (c, inCode) in withSpans env src do
    if inCode then
      out := out.push c; prev := ' '; continue
    else if line then
      if c == '\n' then line := false; out := out.push c
    else if depth > 0 then
      if c == '\n' then out := out.push c
      if prev == '/' && c == '-' then depth := depth + 1; prev := ' '; continue
      if prev == '-' && c == '/' then depth := depth - 1; prev := ' '; continue
    else if prev == '-' && c == '-' then
      line := true; out := out.dropEnd 1 |>.toString
    else if prev == '/' && c == '-' then
      depth := 1; out := out.dropEnd 1 |>.toString; prev := ' '; continue
    else out := out.push c
    prev := c
  return out

/-! ## Listed commands (`[syntax]`, contract U36 C3) -/

/-- The tokens of an interpolated term from `pos` up to its closing `}` (the first `}` outside
`{ }` pairs; the end of input closes it too), and the position after that `}`. -/
partial def termSpans (env : Environment) (tokens : TokenTable) (ictx : InputContext)
    (pos : String.Pos.Raw) (depth : Nat := 0) (acc : Array Span := #[]) :
    Array Span × String.Pos.Raw :=
  match step env tokens ictx pos with
  | .stop => (acc, ⟨ictx.inputString.utf8ByteSize⟩)
  | .skip n => termSpans env tokens ictx n depth acc
  | .token a b n =>
    match String.Pos.Raw.extract ictx.inputString a b with
    | "}" =>
      if depth == 0 then (acc, b) else termSpans env tokens ictx n (depth - 1) (acc.push (a, b))
    | "{" => termSpans env tokens ictx n (depth + 1) (acc.push (a, b))
    | _ => termSpans env tokens ictx n depth (acc.push (a, b))

/-- The terms interpolated into the string literal spanning `[a, b)` (`s!"x = {x}"`: Lean's
tokenizer reads the whole literal as one string token), each as its tokens: every `{` the
literal holds outside a `\` escape opens one. -/
partial def interpolated (env : Environment) (tokens : TokenTable) (ictx : InputContext)
    (a b : String.Pos.Raw) : Array (Array Span) :=
  let rec go (p : String.Pos.Raw) (acc : Array (Array Span)) :=
    if b.byteIdx ≤ p.byteIdx then acc
    else match ictx.get p with
      | '\\' => go (ictx.next (ictx.next p)) acc
      | '{' => let (ts, e) := termSpans env tokens ictx (ictx.next p); go e (acc.push ts)
      | _ => go (ictx.next p) acc
  go (ictx.next a) #[]

/-- Listed tokens among `spans` as `(byte position, token)`: a token of `commandTokens`; `eval`
directly followed by `%` (Mathlib's `eval%`, which a table without Mathlib's tokens splits);
with `attrs`, the name of each attribute inside `@[ … ]` and `attribute [ … ]` that
`registersCode` accepts (after `local`, `scoped` or `-`; `«»` dropped; its arguments are not
names); and the same, `attrs` aside, in each term interpolated into a string literal. -/
partial def listedIn (env : Environment) (tokens : TokenTable) (ictx : InputContext)
    (spans : Array Span) (attrs : Bool) (hits : Array (Nat × String) := #[]) :
    Array (Nat × String) := Id.run do
  let mut hits := hits
  -- bracket depth inside an attribute list; whether the next token names an attribute
  let mut depth := 0
  let mut name := false
  let mut prev := ""
  for (a, b) in spans do
    let t := String.Pos.Raw.extract ictx.inputString a b
    if t.startsWith "\"" then
      for ts in interpolated env tokens ictx a b do hits := listedIn env tokens ictx ts false hits
    if commandTokens.contains t then hits := hits.push (a.byteIdx, t)
    if t == "eval" && ictx.get b == '%' then hits := hits.push (a.byteIdx, "eval%")
    if attrs then
      if depth == 0 then
        if t == "@[" || (t == "[" && prev == "attribute") then depth := 1; name := true
      else if t == "[" || t == "@[" then depth := depth + 1
      else if t == "]" then depth := depth - 1
      else if depth == 1 && t == "," then name := true
      else if name && !["local", "scoped", "-"].contains t then
        let n := (t.replace "«" "").replace "»" ""
        if registersCode n then hits := hits.push (a.byteIdx, n)
        name := false
    prev := t
  return hits

/-- Each place the code of `src` uses a listed token (`listedIn` over `codeSpans`), once per
position, in source order: the token and its 1-based line. -/
def listedTokens (env : Environment) (src : String) : Array (String × Nat) := Id.run do
  let ictx := mkInputContext src "<source>" (normalizeLineEndings := false)
  let hits := (listedIn env (getTokenTable env) ictx (codeSpans env src) true).qsort
    (·.1 < ·.1)
  let mut out := #[]
  let mut last : Option Nat := none
  for (p, t) in hits do
    if last == some p then continue
    last := some p
    let line := (String.Pos.Raw.extract src 0 ⟨p⟩).foldl
      (fun n c => if c == '\n' then n + 1 else n) 1
    out := out.push (t, line)
  return out

end FVA.Trust
