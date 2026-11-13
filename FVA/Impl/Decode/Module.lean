import FVA.Impl.Decode.Instr
import FVA.Spec.Binary.Types

/-!
# Module decoding

Sections are read slot by slot in the spec's order; each section's content is a sub-input of
exactly its declared size, which must be consumed completely. Custom sections may appear
anywhere and are skipped after their name is checked. Data segment bytes stay one numeral
(`leBytes k lit`), so a 20 KB segment costs the kernel a single `Nat.land` instead of a byte
list.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- Limits: flag `0x00` (min) or `0x01` (min, max), each a `u64`; shared (`0x02`, `0x03`,
`0x06`, `0x07`) and 64-bit (`0x04`, `0x05`) limits are outside the profile. -/
def limits (v n : Nat) : Res Limits :=
  (byte v n).bind fun f v' n' =>
  bif Nat.beq f 0 then (u64 v' n').bind fun a v n => .ok { min := a, max := none } v n
  else bif Nat.beq f 1 then
    (u64 v' n').bind fun a v n => (u64 v n).bind fun b v n => .ok { min := a, max := some b } v n
  else bif Nat.beq f 4 || Nat.beq f 5 then excluded .memory64 n "64-bit limits"
  else bif Nat.blt f 8 then excluded .threads n "shared limits"
  else .bad n "malformed limits flags"

/-- A function type after its `0x60`: `vec(valtype) vec(valtype)`. -/
def funcTypeBody (v n : Nat) : Res FuncType :=
  (vec valType v n).bind fun ps v n => (vec valType v n).bind fun rs v n =>
  .ok { params := ps, results := rs } v n

/-- A P′ sub type: a bare function type, or `0x4F` with no supertypes and a function type
(both final). Non-final sub types (`0x50`), declared supertypes and struct/array types
(`0x5F`/`0x5E`) are GC. -/
def subType (v n : Nat) : Res FuncType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0x60 then funcTypeBody v' n'
  else bif Nat.beq b 0x4F then
    (vec u32 v' n').bind fun xs v n =>
    bif !xs.isEmpty then excluded .gcTypes n "declared supertype" else
    (byte v n).bind fun c v' n' =>
    bif Nat.beq c 0x60 then funcTypeBody v' n'
    else bif Nat.beq c 0x5E || Nat.beq c 0x5F then excluded .gcTypes n "struct or array type"
    else .bad n "malformed composite type"
  else bif Nat.beq b 0x50 || Nat.beq b 0x5E || Nat.beq b 0x5F then
    excluded .gcTypes n "sub, struct or array type"
  else .bad n "malformed sub type"

/-- A recursive type: `0x4E vec(subtype)`, or one sub type alone. -/
def recType (v n : Nat) : Res RecType :=
  match n with
  | 0 => .bad 0 "unexpected end"
  | n' + 1 =>
    bif Nat.beq (Nat.land v 255) 0x4E then vec subType (Nat.shiftRight v 8) n'
    else (subType v (n' + 1)).bind fun ft v n => .ok [ft] v n

/-- Table types: `reftype limits`. -/
def tableType (v n : Nat) : Res TableType :=
  (refType v n).bind fun t v n => (limits v n).bind fun l v n => .ok { limits := l, elem := t } v n

/-- Tag types: `0x00` and a function type index. -/
def tagType (v n : Nat) : Res Nat :=
  (byte v n).bind fun a v' n' =>
  bif Nat.beq a 0 then u32 v' n' else .bad n "malformed tag attribute"

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
    else bif Nat.beq k 4 then (tagType v' n').bind fun x v n => .ok (.tag x) v n
    else .bad n "malformed import kind"
  desc.bind fun d v n => .ok { module := md, name := nm, desc := d } v n

/-- Exports. -/
def export_ (v n : Nat) : Res Export :=
  (name v n).bind fun nm v n => (byte v n).bind fun k v' n' => (u32 v' n').bind fun x v'' n'' =>
  let ok (d : ExportDesc) : Res Export := .ok { name := nm, desc := d } v'' n''
  bif Nat.beq k 0 then ok (.func x) else bif Nat.beq k 1 then ok (.table x)
  else bif Nat.beq k 2 then ok (.mem x) else bif Nat.beq k 3 then ok (.global x)
  else bif Nat.beq k 4 then ok (.tag x)
  else .bad n "malformed export kind"

/-- Globals. -/
def global (v n : Nat) : Res Global :=
  (globalType v n).bind fun t v n => (expr v n).bind fun e v n => .ok { type := t, init := e } v n

/-- Tables: a table type (elements start as its heap type's null), or `0x40 0x00`, the table
type and an initializer expression. -/
def table (v n : Nat) : Res Table :=
  match n with
  | 0 => .bad 0 "unexpected end"
  | n' + 1 =>
    bif Nat.beq (Nat.land v 255) 0x40 then
      (byte (Nat.shiftRight v 8) n').bind fun z v n =>
      bif !Nat.beq z 0 then .bad n "malformed table" else
      (tableType v n).bind fun t v n => (expr v n).bind fun e v n =>
      .ok { type := t, init := e } v n
    else (tableType v (n' + 1)).bind fun t v n =>
      .ok { type := t, init := [.refNull t.elem.heap] } v n

/-- Tags. -/
def tag (v n : Nat) : Res Tag := (tagType v n).bind fun x v n => .ok { type := x } v n

/-- `elemkind`: only `0x00`, `(ref func)`. -/
def elemKind (v n : Nat) : Res RefType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0 then .ok ⟨false, .abs .func⟩ v' n' else .bad n "malformed element kind"

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
  -- flag 0's implicit type = `(ref func)`, flag 4's = `(ref null func)`
  let ty : Res RefType :=
    bif typed then (bif exprs then refType v n else elemKind v n)
    else .ok (bif exprs then .funcref else ⟨false, .abs .func⟩) v n
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
  | .tryTable _ _ b => usesDataList b
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

/-- Decode a non-custom section's content `(v, n)` into the accumulator. -/
def sectionInto (id : Nat) (a : Acc) (v n : Nat) : Res Acc :=
  bif Nat.beq id 10 then (vec code v n).bind fun cs v n => .ok { a with codes := cs } v n
  else bif Nat.beq id 1 then
    (vec recType v n).bind fun ts v n => .ok { a with m := { a.m with types := ts } } v n
  else bif Nat.beq id 2 then
    (vec import_ v n).bind fun is v n => .ok { a with m := { a.m with imports := is } } v n
  else bif Nat.beq id 3 then (vec u32 v n).bind fun xs v n => .ok { a with typeIdxs := xs } v n
  else bif Nat.beq id 4 then
    (vec table v n).bind fun ts v n => .ok { a with m := { a.m with tables := ts } } v n
  else bif Nat.beq id 5 then
    (vec limits v n).bind fun ms v n => .ok { a with m := { a.m with mems := ms } } v n
  else bif Nat.beq id 13 then
    (vec tag v n).bind fun ts v n => .ok { a with m := { a.m with tags := ts } } v n
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

/-- Section ids in the order a module lists them (`Bmodule`): tags (13) between memories and
globals, data count (12) before code. -/
def slotIds : List Nat := [1, 2, 3, 4, 5, 13, 6, 7, 8, 9, 12, 10, 11]

/-- Custom sections while the next id byte is 0: names checked, contents skipped. Structural on
`fuel` (callers pass the byte count; each section takes ≥ 2 bytes). -/
def customs : Nat → Nat → Nat → Res Unit
  | 0, v, n => .ok () v n
  | fuel + 1, v, n =>
    bif Nat.beq n 0 || !Nat.beq (Nat.land v 255) 0 then .ok () v n else
    (byte v n).bind fun _ v n => (u32 v n).bind fun k v n =>
    (sub k (fun v n => (name v n).bind fun _ _ _ => .ok () 0 0) v n).bind fun _ v n =>
    customs fuel v n

/-- The optional sections `ids` in order, each after custom sections, then trailing custom
sections. A section out of order stays unread, and `decode` rejects the leftover input. Reading
in the spec's slot order (rather than tracking ranks) keeps the proof a slot-by-slot walk. -/
def slots : List Nat → Acc → Nat → Nat → Res Acc
  | [], a, v, n => (customs n v n).bind fun _ v n => .ok a v n
  | id :: ids, a, v, n =>
    (customs n v n).bind fun _ v n =>
    bif !Nat.beq n 0 && Nat.beq (Nat.land v 255) id then
      (byte v n).bind fun _ v n => (u32 v n).bind fun k v n =>
      (sub k (sectionInto id a) v n).bind fun a v n => slots ids a v n
    else slots ids a v n

/-- The module from its sections, after `Bmodule`'s cross-section checks. -/
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

/-- Decode a whole module from `len` bytes packed little-endian in `bytes` (`Bmodule`). -/
def decode (bytes len : Nat) : Except DecodeError Module :=
  let r : Res Module :=
    (leNat 4 bytes len).bind fun magic v n =>
    bif !Nat.beq magic 0x6D736100 then .bad len "magic header not detected" else
    (leNat 4 v n).bind fun version v n =>
    bif !Nat.beq version 1 then .bad (len - 4) "unknown binary version" else
    (slots slotIds {} v n).bind fun a v n =>
    bif Nat.beq n 0 then finish a n
    else bif Nat.blt 13 (Nat.land v 255) then .bad n "malformed section id"
    else .bad n "unexpected content after last section"
  match r with
  | .ok m _ _ => .ok m
  | .bad rem msg => .error (.malformed (len - rem) msg)
  | .unsup rem msg => .error (.unsupported (len - rem) msg)

end FVA.Wasm.Decode
