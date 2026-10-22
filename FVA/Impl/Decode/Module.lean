import FVA.Impl.Decode.Instr

/-!
# Module decoding

Sections are read in the spec's order; each section's content is a sub-reader of exactly its
declared size, which must be consumed completely. Custom sections may appear anywhere and are
skipped after their name is checked.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- Run `p` on `r` and require it to consume all of `r`. -/
def whole {α : Type} (p : Reader → Res α) (r : Reader) : Except DecodeError α := do
  let (a, r') ← p r
  if r'.len = 0 then .ok a else .error (.malformed r'.pos "section size mismatch")

/-- Limits: flag `0x00` (min) or `0x01` (min, max); other flags are outside the profile. -/
def limits (r : Reader) : Res Limits := do
  let (f, r') ← r.byte
  if f.toNat = 0 then do
    let (n, r') ← u32 r'
    .ok ({ min := n, max := none }, r')
  else if f.toNat = 1 then do
    let (n, r') ← u32 r'
    let (m, r') ← u32 r'
    .ok ({ min := n, max := some m }, r')
  else if f.toNat < 8 then r.unsup "shared memory or 64-bit limits"
  else r.bad "integer too large"

/-- Function types: `0x60 vec(valtype) vec(valtype)`. -/
def funcType (r : Reader) : Res FuncType := do
  let (b, r') ← r.byte
  if b.toNat = 0x60 then do
    let (ps, r') ← vec valType r'
    let (rs, r') ← vec valType r'
    .ok ({ params := ps, results := rs }, r')
  else if b.toNat = 0x4E ∨ b.toNat = 0x4F ∨ b.toNat = 0x50 ∨ b.toNat = 0x5E ∨ b.toNat = 0x5F then
    r.unsup "GC types"
  else r.bad "integer representation too long"

/-- Table types: `reftype limits`. -/
def tableType (r : Reader) : Res TableType := do
  let (t, r) ← refType r
  let (l, r) ← limits r
  .ok ({ limits := l, elem := t }, r)

/-- Global types: `valtype mut`. -/
def globalType (r : Reader) : Res GlobalType := do
  let (t, r) ← valType r
  let (m, r') ← r.byte
  if m.toNat = 0 then .ok ({ mutability := .const, val := t }, r')
  else if m.toNat = 1 then .ok ({ mutability := .var, val := t }, r')
  else r.bad "malformed mutability"

/-- Imports. -/
def import_ (r : Reader) : Res Import := do
  let (md, r) ← name r
  let (nm, r) ← name r
  let (k, r') ← r.byte
  let (d, r') ←
    (if k.toNat = 0 then do let (x, r') ← u32 r'; .ok (ImportDesc.func x, r')
     else if k.toNat = 1 then do let (t, r') ← tableType r'; .ok (.table t, r')
     else if k.toNat = 2 then do let (t, r') ← limits r'; .ok (.mem t, r')
     else if k.toNat = 3 then do let (t, r') ← globalType r'; .ok (.global t, r')
     else if k.toNat = 4 then r.unsup "exception handling (tag import)"
     else r.bad "malformed import kind" : Res ImportDesc)
  .ok ({ module := md, name := nm, desc := d }, r')

/-- Exports. -/
def export_ (r : Reader) : Res Export := do
  let (nm, r) ← name r
  let (k, r') ← r.byte
  let (x, r') ← u32 r'
  let d : Option ExportDesc :=
    if k.toNat = 0 then some (.func x) else if k.toNat = 1 then some (.table x)
    else if k.toNat = 2 then some (.mem x) else if k.toNat = 3 then some (.global x) else none
  match d with
  | some d => .ok ({ name := nm, desc := d }, r')
  | none => if k.toNat = 4 then r.unsup "exception handling (tag export)"
            else r.bad "malformed export kind"

/-- Globals. -/
def global (r : Reader) : Res Global := do
  let (t, r) ← globalType r
  let (e, r) ← expr r
  .ok ({ type := t, init := e }, r)

/-- `elemkind`: only `0x00` (funcref). -/
def elemKind (r : Reader) : Res RefType := do
  let (b, r') ← r.byte
  if b.toNat = 0 then .ok (.funcref, r') else r.bad "malformed element kind"

/-- `(ref.func y) end` initializers from function indices. -/
def funcInits (ys : List Nat) : List Expr := ys.map fun y => .cons (Instr.refFunc y) .nil

/-- Element segments (eight encodings). -/
def elem (r : Reader) : Res Elem := do
  let (f, r) ← u32 r
  if f = 0 then do
    let (e, r) ← expr r
    let (ys, r) ← vec u32 r
    .ok ({ type := .funcref, init := funcInits ys, mode := .active 0 e }, r)
  else if f = 1 then do
    let (t, r) ← elemKind r
    let (ys, r) ← vec u32 r
    .ok ({ type := t, init := funcInits ys, mode := .passive }, r)
  else if f = 2 then do
    let (x, r) ← u32 r
    let (e, r) ← expr r
    let (t, r) ← elemKind r
    let (ys, r) ← vec u32 r
    .ok ({ type := t, init := funcInits ys, mode := .active x e }, r)
  else if f = 3 then do
    let (t, r) ← elemKind r
    let (ys, r) ← vec u32 r
    .ok ({ type := t, init := funcInits ys, mode := .declarative }, r)
  else if f = 4 then do
    let (e, r) ← expr r
    let (es, r) ← vec expr r
    .ok ({ type := .funcref, init := es, mode := .active 0 e }, r)
  else if f = 5 then do
    let (t, r) ← refType r
    let (es, r) ← vec expr r
    .ok ({ type := t, init := es, mode := .passive }, r)
  else if f = 6 then do
    let (x, r) ← u32 r
    let (e, r) ← expr r
    let (t, r) ← refType r
    let (es, r) ← vec expr r
    .ok ({ type := t, init := es, mode := .active x e }, r)
  else if f = 7 then do
    let (t, r) ← refType r
    let (es, r) ← vec expr r
    .ok ({ type := t, init := es, mode := .declarative }, r)
  else r.bad "malformed elements segment kind"

/-- Data segments (three encodings). -/
def data (r : Reader) : Res Data := do
  let (f, r) ← u32 r
  if f = 0 then do
    let (e, r) ← expr r
    let (n, r) ← u32 r
    let (bs, r) ← bytesList n r
    .ok ({ init := bs, mode := .active 0 e }, r)
  else if f = 1 then do
    let (n, r) ← u32 r
    let (bs, r) ← bytesList n r
    .ok ({ init := bs, mode := .passive }, r)
  else if f = 2 then do
    let (x, r) ← u32 r
    let (e, r) ← expr r
    let (n, r) ← u32 r
    let (bs, r) ← bytesList n r
    .ok ({ init := bs, mode := .active x e }, r)
  else r.bad "malformed data segment kind"

/-- A run of locals. -/
def localsRun (r : Reader) : Res (Nat × ValType) := do
  let (n, r) ← u32 r
  let (t, r) ← valType r
  .ok ((n, t), r)

/-- A code entry: size-delimited locals and body; at most 2^32 − 1 locals in total. -/
def code (r : Reader) : Res (List ValType × Expr) := do
  let (sz, r) ← u32 r
  let (c, r') ← r.take sz
  let (groups, c) ← vec localsRun c
  if 2 ^ 32 ≤ (groups.map Prod.fst).sum then c.bad "too many locals" else do
  let (e, c) ← expr c
  if c.len = 0 then .ok ((groups.flatMap fun g => List.replicate g.1 g.2, e), r')
  else c.bad "section size mismatch"

mutual
/-- Whether an instruction uses a data index (`memory.init`, `data.drop`), possibly nested. -/
def usesData : Instr → Bool
  | .memoryInit _ | .dataDrop _ => true
  | .block _ b | .loop _ b => usesDataList b
  | .if_ _ t e => usesDataList t || usesDataList e
  | _ => false
/-- Whether any instruction in the sequence uses a data index. -/
def usesDataList : Instrs → Bool
  | .nil => false
  | .cons i is => usesData i || usesDataList is
end

/-- Canonical position of each known section id in the module (custom = 0). -/
def sectionRank (id : Nat) : Option Nat :=
  if id = 1 then some 1 else if id = 2 then some 2 else if id = 3 then some 3
  else if id = 4 then some 4 else if id = 5 then some 5 else if id = 6 then some 6
  else if id = 7 then some 7 else if id = 8 then some 8 else if id = 9 then some 9
  else if id = 12 then some 10 else if id = 10 then some 11 else if id = 11 then some 12
  else none

/-- Section contents gathered so far. -/
structure Acc where
  /-- The module fields decoded so far. -/
  m : Module := {}
  /-- Function section type indices. -/
  typeIdxs : List Nat := []
  /-- Code section entries. -/
  codes : List (List ValType × Expr) := []
  /-- Data count, when the section is present. -/
  dataCount : Option Nat := none

/-- Decode one non-custom section's content into the accumulator. -/
def sectionInto (id : Nat) (c : Reader) (a : Acc) : Except DecodeError Acc := do
  if id = 1 then do let ts ← whole (vec funcType) c; .ok { a with m := { a.m with types := ts } }
  else if id = 2 then do
    let is ← whole (vec import_) c; .ok { a with m := { a.m with imports := is } }
  else if id = 3 then do let xs ← whole (vec u32) c; .ok { a with typeIdxs := xs }
  else if id = 4 then do
    let ts ← whole (vec tableType) c; .ok { a with m := { a.m with tables := ts } }
  else if id = 5 then do let ms ← whole (vec limits) c; .ok { a with m := { a.m with mems := ms } }
  else if id = 6 then do
    let gs ← whole (vec global) c; .ok { a with m := { a.m with globals := gs } }
  else if id = 7 then do
    let es ← whole (vec export_) c; .ok { a with m := { a.m with exports := es } }
  else if id = 8 then do let x ← whole u32 c; .ok { a with m := { a.m with start := some x } }
  else if id = 9 then do let es ← whole (vec elem) c; .ok { a with m := { a.m with elems := es } }
  else if id = 12 then do let n ← whole u32 c; .ok { a with dataCount := some n }
  else if id = 10 then do let cs ← whole (vec code) c; .ok { a with codes := cs }
  else do let ds ← whole (vec data) c; .ok { a with m := { a.m with datas := ds } }

/-- Read sections until the input ends; `last` = rank of the last non-custom section.
Structural on `fuel` (callers pass the byte count; each section takes ≥ 2 bytes). -/
def sections : Nat → Nat → Reader → Acc → Except DecodeError Acc
  | 0, _, r, a => if r.len = 0 then .ok a else .error (.malformed r.pos "unexpected end")
  | fuel + 1, last, r, a =>
    if r.len = 0 then .ok a else do
    let (idb, r₁) ← r.byte
    let id := idb.toNat
    let (sz, r₂) ← u32 r₁
    let (c, r₃) ← r₂.take sz
    if id = 0 then do
      let _ ← (name c : Res String)
      sections fuel last r₃ a
    else match sectionRank id with
      | none =>
        if id = 13 then .error (.unsupported r.pos "exception handling (tag section)")
        else .error (.malformed r.pos "malformed section id")
      | some rank =>
        if rank ≤ last then .error (.malformed r.pos "unexpected content after last section")
        else do
          let a ← sectionInto id c a
          sections fuel rank r₃ a

/-- Decode a whole module from `len` bytes packed little-endian in `bytes` (spec §5.5.16). -/
def decode (bytes len : Nat) : Except DecodeError Module := do
  let r : Reader := ⟨bytes, len, 0⟩
  let (magic, r) ← leNat 4 r
  if magic ≠ 0x6D736100 then .error (.malformed 0 "magic header not detected") else do
  let (version, r) ← leNat 4 r
  if version ≠ 1 then .error (.malformed 4 "unknown binary version") else do
  let a ← sections r.len 0 r {}
  if a.typeIdxs.length ≠ a.codes.length then
    .error (.malformed len "function and code section have inconsistent lengths")
  else if a.dataCount.isSome ∧ a.dataCount ≠ some a.m.datas.length then
    .error (.malformed len "data count and data section have inconsistent lengths")
  else if a.dataCount.isNone ∧ a.codes.any (fun c => usesDataList c.2) then
    .error (.malformed len "data count section required")
  else .ok { a.m with
    funcs := List.zipWith (fun t c => { type := t, locals := c.1, body := c.2 }) a.typeIdxs
        a.codes }

end FVA.Wasm.Decode
