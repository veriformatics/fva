import Lean

/-!
# Code lines of a Lean source (trusted glue, D11)

Read by Lean's own tokenizer: `Lean.Parser.whitespace` skips whitespace and comments exactly as
Lean's parser does, `Lean.Parser.tokenFn` reads one token (string, char and raw-string literals,
`«…»` names, identifiers, numbers, the token table's symbols). Doc comments (`/-- … -/`,
`/-! … -/`) are tokens to Lean but comments to a reader. A character the tokenizer rejects counts
as code: the collector imports no parser extension, so a symbol of Mathlib notation is unknown to
its table.
-/

namespace FVA.Trust

open Lean Parser

/-- Byte ranges of the code tokens of `src`, in order, by `env`'s token table. -/
partial def codeSpans (env : Environment) (src : String) :
    Array (String.Pos.Raw × String.Pos.Raw) :=
  let ictx := mkInputContext src "<source>" (normalizeLineEndings := false)
  let tokens := getTokenTable env
  let run (p : ParserFn) (pos : String.Pos.Raw) : ParserState :=
    p.run ictx { env, options := {} } tokens ((mkParserState ictx.inputString).setPos pos)
  let rec go (pos : String.Pos.Raw) (acc : Array (String.Pos.Raw × String.Pos.Raw)) :=
    if ictx.atEnd pos then acc
    else
      let s := run whitespace pos
      let p := s.pos
      if ictx.atEnd p then acc
      -- a tab or carriage return outside a literal (Lean rejects the file): skip it
      else if s.hasError then go (ictx.next p) acc
      else if ictx.get p == '/' && ictx.get (ictx.next p) == '-' &&
          (ictx.get (ictx.next (ictx.next p)) == '-' || ictx.get (ictx.next (ictx.next p)) == '!')
      then
        let s := run (finishCommentBlock (pushMissingOnError := false) 1)
          (ictx.next (ictx.next p))
        if s.hasError then acc else go s.pos acc
      else
        let s := run (tokenFn []) p
        match s.hasError, s.stxStack.back.getPos?, s.stxStack.back.getTailPos? with
        | false, some a, some b => go s.pos (acc.push (a, b))
        | _, _, _ => go (ictx.next p) (acc.push (p, ictx.next p))
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

end FVA.Trust
