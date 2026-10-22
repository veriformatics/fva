import FVA.Impl.Decode.Instr
import FVA.Spec.Binary.Types

/-!
# Module decoding

Sections are read in the spec's order; each section's content is a sub-input of exactly its
declared size, which must be consumed completely. Custom sections may appear anywhere and are
skipped after their name is checked. Data segment bytes stay one numeral (`leBytes k lit`), so a
20 KB segment costs the kernel a single `&&&` instead of a byte list.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- Limits: flag `0x00` (min) or `0x01` (min, max); flags up to `0x07` are outside the
profile (shared memory, 64-bit). -/
def limits (v n : Nat) : Res Limits :=
  (byte v n).bind fun f v' n' =>
  bif Nat.beq f 0 then (u32 v' n').bind fun a v n => .ok { min := a, max := none } v n
  else bif Nat.beq f 1 then
    (u32 v' n').bind fun a v n => (u32 v n).bind fun b v n => .ok { min := a, max := some b } v n
  else bif Nat.blt f 8 then .unsup n "shared memory or 64-bit limits"
  else .bad n "integer too large"

/-- Function types: `0x60 vec(valtype) vec(valtype)`. -/
def funcType (v n : Nat) : Res FuncType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0x60 then
    (vec valType v' n').bind fun ps v n => (vec valType v n).bind fun rs v n =>
    .ok { params := ps, results := rs } v n
  else bif Nat.beq b 0x4E || Nat.beq b 0x4F || Nat.beq b 0x50 || Nat.beq b 0x5E ||
      Nat.beq b 0x5F then .unsup n "GC types"
  else .bad n "integer representation too long"

/-- Table types: `reftype limits`. -/
def tableType (v n : Nat) : Res TableType :=
  (refType v n).bind fun t v n => (limits v n).bind fun l v n => .ok { limits := l, elem := t } v n

/-- Global types: `valtype mut`. -/
def globalType (v n : Nat) : Res GlobalType :=
  (valType v n).bind fun t v n => (byte v n).bind fun m v' n' =>
  bif Nat.beq m 0 then .ok { mutability := .const, val := t } v' n'
  else bif Nat.beq m 1 then .ok { mutability := .var, val := t } v' n'
  else .bad n "malformed mutability"

/-- Imports. -/
def import_ (v n : Nat) : Res Import :=
  (name v n).bind fun md v n => (name v n).bind fun nm v n => (byte v n).bind fun k v' n' =>
  let desc : Res ImportDesc :=
    bif Nat.beq k 0 then (u32 v' n').bind fun x v n => .ok (.func x) v n
    else bif Nat.beq k 1 then (tableType v' n').bind fun t v n => .ok (.table t) v n
    else bif Nat.beq k 2 then (limits v' n').bind fun t v n => .ok (.mem t) v n
    else bif Nat.beq k 3 then (globalType v' n').bind fun t v n => .ok (.global t) v n
    else bif Nat.beq k 4 then .unsup n "exception handling (tag import)"
    else .bad n "malformed import kind"
  desc.bind fun d v n => .ok { module := md, name := nm, desc := d } v n

/-- Exports. -/
def export_ (v n : Nat) : Res Export :=
  (name v n).bind fun nm v n => (byte v n).bind fun k v' n' => (u32 v' n').bind fun x v'' n'' =>
  let ok (d : ExportDesc) : Res Export := .ok { name := nm, desc := d } v'' n''
  bif Nat.beq k 0 then ok (.func x) else bif Nat.beq k 1 then ok (.table x)
  else bif Nat.beq k 2 then ok (.mem x) else bif Nat.beq k 3 then ok (.global x)
  else bif Nat.beq k 4 then .unsup n "exception handling (tag export)"
  else .bad n "malformed export kind"

/-- Globals. -/
def global (v n : Nat) : Res Global :=
  (globalType v n).bind fun t v n => (expr v n).bind fun e v n => .ok { type := t, init := e } v n

/-- `elemkind`: only `0x00` (funcref). -/
def elemKind (v n : Nat) : Res RefType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0 then .ok .funcref v' n' else .bad n "malformed element kind"

/-- `(ref.func y) end` initializers from function indices. -/
def funcInits (ys : List Nat) : List Expr := ys.map fun y => [Instr.refFunc y]

/-- Element segments: the eight encodings selected by a `u32` flag. Bit 0 = passive or
declarative, bit 1 = explicit table index (active) or declarative (with bit 0), bit 2 =
initializers are expressions rather than function indices. -/
def elem (v n : Nat) : Res Elem :=
  (u32 v n).bind fun f v n =>
  bif Nat.blt 7 f then .bad n "malformed elements segment kind" else
  let exprs := Nat.ble 4 f
  let k := f % 4
  -- mode: active (k = 0 table 0, k = 2 explicit table), passive (k = 1), declarative (k = 3)
  let mode : Res (ElemMode × Bool) :=
    bif Nat.beq k 1 then .ok (.passive, true) v n
    else bif Nat.beq k 3 then .ok (.declarative, true) v n
    else bif Nat.beq k 0 then (expr v n).bind fun e v n => .ok (.active 0 e, false) v n
    else (u32 v n).bind fun x v n => (expr v n).bind fun e v n => .ok (.active x e, true) v n
  mode.bind fun (md, typed) v n =>
  let ty : Res RefType :=
    bif typed then (bif exprs then refType v n else elemKind v n) else .ok .funcref v n
  ty.bind fun t v n =>
  let inits : Res (List Expr) :=
    bif exprs then vec expr v n else (vec u32 v n).bind fun ys v n => .ok (funcInits ys) v n
  inits.bind fun es v n => .ok { type := t, init := es, mode := md } v n

/-- Data segments: three encodings selected by a `u32` flag; the bytes stay one numeral. -/
def data (v n : Nat) : Res Data :=
  (u32 v n).bind fun f v n =>
  let mode : Res DataMode :=
    bif Nat.beq f 0 then (expr v n).bind fun e v n => .ok (.active 0 e) v n
    else bif Nat.beq f 1 then .ok .passive v n
    else bif Nat.beq f 2 then
      (u32 v n).bind fun x v n => (expr v n).bind fun e v n => .ok (.active x e) v n
    else .bad n "malformed data segment kind"
  mode.bind fun md v n => (u32 v n).bind fun k v n => (leNat k v n).bind fun bs v n =>
  .ok { init := Binary.leBytes k bs, mode := md } v n

/-- A run of locals. -/
def localsRun (v n : Nat) : Res (Nat × ValType) :=
  (u32 v n).bind fun c v n => (valType v n).bind fun t v n => .ok (c, t) v n

/-- A code entry's content: local runs (at most 2^32 − 1 locals in total) and the body. -/
def codeBody (v n : Nat) : Res (List (Nat × ValType) × Expr) :=
  (vec localsRun v n).bind fun ls v n =>
  bif Nat.blt ((ls.map Prod.fst).sum) (2 ^ 32) then (expr v n).bind fun e v n => .ok (ls, e) v n
  else .bad n "too many locals"

/-- A code entry: `size:u32`, then exactly that many bytes of content. -/
def code (v n : Nat) : Res (List (Nat × ValType) × Expr) :=
  (u32 v n).bind fun k v n => sub k codeBody v n

mutual
/-- Whether an instruction uses a data index (`memory.init`, `data.drop`), possibly nested. -/
def usesData : Instr → Bool
  | .memoryInit _ | .dataDrop _ => true
  | .block _ b | .loop _ b => usesDataList b
  | .if_ _ t e => usesDataList t || usesDataList e
  | _ => false
/-- Whether any instruction in the sequence uses a data index. -/
def usesDataList : List Instr → Bool
  | [] => false
  | i :: is => usesData i || usesDataList is
end

/-- Section contents gathered so far. -/
structure Acc where
  /-- The module fields decoded so far. -/
  m : Module := {}
  /-- Function section type indices. -/
  typeIdxs : List Nat := []
  /-- Code section entries. -/
  codes : List (List (Nat × ValType) × Expr) := []
  /-- Data count, when the section is present. -/
  dataCount : Option Nat := none

/-- Canonical position of each known section id in the module (custom = 0). -/
def sectionRank (id : Nat) : Nat :=
  bif Nat.blt id 10 then id
  else bif Nat.beq id 12 then 10 else bif Nat.beq id 10 then 11 else bif Nat.beq id 11 then 12
  else 0

/-- Decode a non-custom section's content `(v, n)` into the accumulator. -/
def sectionInto (id : Nat) (a : Acc) (v n : Nat) : Res Acc :=
  bif Nat.beq id 10 then (vec code v n).bind fun cs v n => .ok { a with codes := cs } v n
  else bif Nat.beq id 1 then
    (vec funcType v n).bind fun ts v n => .ok { a with m := { a.m with types := ts } } v n
  else bif Nat.beq id 2 then
    (vec import_ v n).bind fun is v n => .ok { a with m := { a.m with imports := is } } v n
  else bif Nat.beq id 3 then (vec u32 v n).bind fun xs v n => .ok { a with typeIdxs := xs } v n
  else bif Nat.beq id 4 then
    (vec tableType v n).bind fun ts v n => .ok { a with m := { a.m with tables := ts } } v n
  else bif Nat.beq id 5 then
    (vec limits v n).bind fun ms v n => .ok { a with m := { a.m with mems := ms } } v n
  else bif Nat.beq id 6 then
    (vec global v n).bind fun gs v n => .ok { a with m := { a.m with globals := gs } } v n
  else bif Nat.beq id 7 then
    (vec export_ v n).bind fun es v n => .ok { a with m := { a.m with exports := es } } v n
  else bif Nat.beq id 8 then
    (u32 v n).bind fun x v n => .ok { a with m := { a.m with start := some x } } v n
  else bif Nat.beq id 9 then
    (vec elem v n).bind fun es v n => .ok { a with m := { a.m with elems := es } } v n
  else bif Nat.beq id 12 then (u32 v n).bind fun c v n => .ok { a with dataCount := some c } v n
  else (vec data v n).bind fun ds v n => .ok { a with m := { a.m with datas := ds } } v n

/-- Read sections until the input ends; `last` = rank of the last non-custom section.
Structural on `fuel` (callers pass the byte count; each section takes ≥ 2 bytes). -/
def sections : Nat → Nat → Acc → Nat → Nat → Res Acc
  | 0, _, a, v, n => bif Nat.beq n 0 then .ok a v n else .bad n "unexpected end"
  | fuel + 1, last, a, v, n =>
    bif Nat.beq n 0 then .ok a v n else
    (byte v n).bind fun id v₁ n₁ =>
    (u32 v₁ n₁).bind fun k v₂ n₂ =>
    bif Nat.beq id 0 then
      (sub k (fun v n => (name v n).bind fun _ _ _ => .ok () 0 0) v₂ n₂).bind fun _ v n =>
      sections fuel last a v n
    else
      let rank := sectionRank id
      bif Nat.beq rank 0 then
        (bif Nat.beq id 13 then .unsup n "exception handling (tag section)"
         else .bad n "malformed section id")
      else bif Nat.ble rank last then .bad n "unexpected content after last section"
      else (sub k (sectionInto id a) v₂ n₂).bind fun a v n => sections fuel rank a v n

/-- The module from its sections, after the cross-section checks of spec §5.5.16. -/
def finish (a : Acc) (n : Nat) : Res Module :=
  bif !Nat.beq a.typeIdxs.length a.codes.length then
    .bad n "function and code section have inconsistent lengths"
  else match a.dataCount with
    | some c =>
      bif Nat.beq c a.m.datas.length then .ok (assemble a) 0 n
      else .bad n "data count and data section have inconsistent lengths"
    | none =>
      bif a.codes.any (fun c => usesDataList c.2) then .bad n "data count section required"
      else .ok (assemble a) 0 n
where
  /-- Functions pair the function section's type indices with the code entries. -/
  assemble (a : Acc) : Module :=
    { a.m with
      funcs := List.zipWith (fun t c => { type := t, locals := c.1, body := c.2 }) a.typeIdxs
        a.codes }

/-- Decode a whole module from `len` bytes packed little-endian in `bytes` (spec §5.5.16). -/
def decode (bytes len : Nat) : Except DecodeError Module :=
  let r : Res Module :=
    (leNat 4 bytes len).bind fun magic v n =>
    bif !Nat.beq magic 0x6D736100 then .bad len "magic header not detected" else
    (leNat 4 v n).bind fun version v n =>
    bif !Nat.beq version 1 then .bad (len - 4) "unknown binary version" else
    (sections n 0 {} v n).bind fun a _ n => finish a n
  match r with
  | .ok m _ _ => .ok m
  | .bad rem msg => .error (.malformed (len - rem) msg)
  | .unsup rem msg => .error (.unsupported (len - rem) msg)

end FVA.Wasm.Decode
