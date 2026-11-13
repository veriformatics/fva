import FVA.Spec.Types

/-!
# Runtime structure (reviewed spec)

Transcribes WebAssembly 2.0 §4.2 for FVA's profile, with Wasm 3.0's runtime structure
(SpecTec `859d3232` `4.0`/`4.1`) for profile P′: values (a payload-free null, exception
references), the store and its instances (tags, exceptions; every stored type closed), module
instances, frames (a local is unset until written when its type has no default), administrative
instructions, block contexts and configurations, plus the memory/table growth of §4.5.3. A
memory is extensional: a page count, an optional maximum and a byte function; growth appends zero
bytes, so bytes from `pages · 65536` on are never observed before they are written. Addresses
and indices are `Nat`. Numeric constants are values (§4.2.1); decoded constants carry canonical
bits (`< 2^N`), the form `Val.instr` produces.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- Reference values (3.0 `ref`): null (`REF.NULL_ADDR`: one null for every type), a function
address, an external address, an exception address. -/
inductive Ref where
  | null
  | func (a : Nat)
  | extern (a : Nat)
  | exn (a : Nat)
  deriving DecidableEq

/-- Values (§4.2.1); floats as their bit patterns (§4.3.1). -/
inductive Val where
  | i32 (v : BitVec 32)
  | i64 (v : BitVec 64)
  | f32 (v : BitVec 32)
  | f64 (v : BitVec 64)
  | ref (r : Ref)
  deriving DecidableEq

/-- `$default_` (3.0 `4.1`): zero bits, null for a nullable reference type, none for a non-null
one (such a local starts unset). -/
def _root_.FVA.Wasm.ValType.default : ValType → Option Val
  | .num .i32 => some (.i32 0)
  | .num .i64 => some (.i64 0)
  | .num .f32 => some (.f32 0)
  | .num .f64 => some (.f64 0)
  | .ref t => if t.null then some (.ref .null) else none

/-- External values (§4.2.11, 3.0 tags). -/
inductive ExternVal where
  | func (a : Nat)
  | table (a : Nat)
  | mem (a : Nat)
  | global (a : Nat)
  | tag (a : Nat)

/-- Export instances (§4.2.10). -/
structure ExportInst where
  /-- Name. -/
  name : String
  /-- Exported value. -/
  value : ExternVal

/-- Module instances (§4.2.5): the module's closed defined types and the store address of every
entity. -/
structure ModuleInst where
  /-- Defined types (`Module.defTypes`). -/
  types : List DefType := []
  /-- Tag addresses (imports first). -/
  tags : List Nat := []
  /-- Function addresses (imports first). -/
  funcs : List Nat := []
  /-- Table addresses. -/
  tables : List Nat := []
  /-- Memory addresses. -/
  mems : List Nat := []
  /-- Global addresses. -/
  globals : List Nat := []
  /-- Element segment addresses. -/
  elems : List Nat := []
  /-- Data segment addresses. -/
  datas : List Nat := []
  /-- Exports. -/
  exports : List ExportInst := []

/-- Function instances (§4.2.6): module code closed over its instance, or a host function named
by a `HostId` whose behavior is the host relation's (`Step`). -/
inductive FuncInst where
  | wasm (type : DefType) (inst : ModuleInst) (code : Func)
  | host (type : DefType) (id : Nat)

/-- The defined type of a function instance. -/
def FuncInst.type : FuncInst → DefType
  | .wasm t _ _ | .host t _ => t

/-- Table instances (§4.2.7). -/
structure TableInst where
  /-- Type (its `min` tracks the current size). -/
  type : TableType
  /-- Elements. -/
  elem : List Ref

/-- Memory instances (§4.2.8): `pages · 65536` bytes. -/
structure MemInst where
  /-- Current size in pages (the type's `min`). -/
  pages : Nat
  /-- Maximum size in pages. -/
  max : Option Nat
  /-- Byte contents. -/
  byte : Nat → UInt8

/-- Global instances (§4.2.9). -/
structure GlobalInst where
  /-- Type. -/
  type : GlobalType
  /-- Current value. -/
  value : Val

/-- Element instances (§4.2.10); a dropped segment has no elements. -/
structure ElemInst where
  /-- Reference type. -/
  type : RefType
  /-- Elements. -/
  elem : List Ref

/-- Data instances (§4.2.10); a dropped segment has no bytes. -/
structure DataInst where
  /-- Bytes. -/
  data : List UInt8

/-- Tag instances (3.0 `taginst`). -/
structure TagInst where
  /-- The tag's defined type (a function type with no results). -/
  type : DefType

/-- Exception instances (3.0 `exninst`): the tag address and the fields, in operand order. -/
structure ExnInst where
  /-- Tag address. -/
  tag : Nat
  /-- Fields. -/
  fields : List Val

/-- The store (§4.2.3, 3.0 tags + exceptions). -/
structure Store where
  /-- Tag instances. -/
  tags : List TagInst := []
  /-- Function instances. -/
  funcs : List FuncInst := []
  /-- Table instances. -/
  tables : List TableInst := []
  /-- Memory instances. -/
  mems : List MemInst := []
  /-- Global instances. -/
  globals : List GlobalInst := []
  /-- Element instances. -/
  elems : List ElemInst := []
  /-- Data instances. -/
  datas : List DataInst := []
  /-- Exception instances. -/
  exns : List ExnInst := []

/-- Frames (§4.2.12, 3.0 `LOCALS (val?)*`): locals and the instance of the running function. -/
structure Frame where
  /-- Local variables (parameters first); `none` = unset (a non-null local before its first
  write). -/
  locals : List (Option Val)
  /-- Module instance. -/
  inst : ModuleInst

/-- Administrative instructions (§4.2.13) over plain instructions. -/
inductive AInstr where
  /-- A plain instruction. -/
  | plain (i : Instr)
  /-- `ref func a`: a function reference value. -/
  | refFuncAddr (a : Nat)
  /-- `ref.extern a`: an external reference value. -/
  | refExternAddr (a : Nat)
  /-- The null reference value (3.0 `REF.NULL_ADDR`; `ref.null ht` steps to it). -/
  | refNullAddr
  /-- `ref.exn a`: an exception reference value. -/
  | refExnAddr (a : Nat)
  /-- `trap`. -/
  | trap
  /-- `invoke a`. -/
  | invoke (a : Nat)
  /-- `label_n{cont} body end`. -/
  | label (n : Nat) (cont : List Instr) (body : List AInstr)
  /-- `frame_n{f} body end`. -/
  | frame (n : Nat) (f : Frame) (body : List AInstr)
  /-- `handler_n{catch*} body end` (3.0 `HANDLER_`): a `try_table`'s catch clauses, outside its
  result label. -/
  | handler (n : Nat) (cs : List Catch) (body : List AInstr)
  /-- A tail call of function address `a` (3.0 `(REF.FUNC_ADDR a) (RETURN_CALL_REF yy)`: the
  callee instance's type gives the arity). -/
  | returnInvoke (a : Nat)

/-- The constant instruction denoting a value (§4.2.1: values are constants). -/
def Val.instr : Val → AInstr
  | .i32 v => .plain (.iconst .w32 v.toNat)
  | .i64 v => .plain (.iconst .w64 v.toNat)
  | .f32 v => .plain (.fconst .w32 v.toNat)
  | .f64 v => .plain (.fconst .w64 v.toNat)
  | .ref .null => .refNullAddr
  | .ref (.func a) => .refFuncAddr a
  | .ref (.extern a) => .refExternAddr a
  | .ref (.exn a) => .refExnAddr a

/-- A sequence of values as instructions (stack bottom first). -/
abbrev vals (vs : List Val) : List AInstr := vs.map Val.instr

/-- Block contexts `B^k` (§4.2.13): `val* [_] instr*` nested under `k` labels and any number of
handlers (3.0 `br-handler`, `return-handler`: a handler is no branch target), never frames. -/
inductive BlockCtx : Nat → Type where
  | base (vs : List Val) (rest : List AInstr) : BlockCtx 0
  | label {k : Nat} (vs : List Val) (n : Nat) (cont : List Instr) (inner : BlockCtx k)
      (rest : List AInstr) : BlockCtx (k + 1)
  | handler {k : Nat} (vs : List Val) (n : Nat) (cs : List Catch) (inner : BlockCtx k)
      (rest : List AInstr) : BlockCtx k

/-- `B^k[es]`. -/
def BlockCtx.fill : {k : Nat} → BlockCtx k → List AInstr → List AInstr
  | _, .base vs rest, es => vals vs ++ es ++ rest
  | _, .label vs n cont inner rest, es => vals vs ++ [.label n cont (inner.fill es)] ++ rest
  | _, .handler vs n cs inner rest, es => vals vs ++ [.handler n cs (inner.fill es)] ++ rest

/-- Evaluation contexts `E` (§4.2.13): `[_]`, `val* E instr*`, `label_n{instr*} E end`,
`handler_n{catch*} E end` (3.0 `trap-handler`: a trap passes every handler). -/
inductive EvalCtx where
  | hole
  | seq (vs : List Val) (inner : EvalCtx) (rest : List AInstr)
  | label (n : Nat) (cont : List Instr) (inner : EvalCtx)
  | handler (n : Nat) (cs : List Catch) (inner : EvalCtx)

/-- `E[es]`. -/
def EvalCtx.fill : EvalCtx → List AInstr → List AInstr
  | .hole, es => es
  | .seq vs inner rest, es => vals vs ++ inner.fill es ++ rest
  | .label n cont inner, es => [.label n cont (inner.fill es)]
  | .handler n cs inner, es => [.handler n cs (inner.fill es)]

/-- Configurations (§4.2.14): store, current frame, instruction sequence. -/
structure Config where
  /-- Store. -/
  store : Store
  /-- Frame. -/
  frame : Frame
  /-- Instructions. -/
  instrs : List AInstr

/-! ## Memory access and growth -/

namespace MemInst

/-- `|data|`, the size in bytes. -/
def size (m : MemInst) : Nat := m.pages * 65536

/-- The little-endian number in the `k` bytes at `ea` (`bytes_N⁻¹`, §4.3.1). -/
def read (m : MemInst) (ea : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (m.byte ea).toNat + 256 * m.read (ea + 1) k

/-- Store the `k` little-endian bytes of `v` at `ea` (`data[ea : k] = bytes_N(v)`). -/
def write (m : MemInst) (ea k v : Nat) : MemInst :=
  { m with byte := fun a => if ea ≤ a ∧ a < ea + k then UInt8.ofNat (v / 256 ^ (a - ea))
      else m.byte a }

/-- `growmem(m, n)` (§4.5.3.8): `n` zero pages appended; `none` past 2^16 pages or the
maximum. -/
def grow (m : MemInst) (n : Nat) : Option MemInst :=
  let len := m.pages + n
  if 2 ^ 16 < len ∨ m.max.any (· < len) then none
  else some { m with pages := len, byte := fun a => if a < m.size then m.byte a else 0 }

end MemInst

/-- `growtable(t, n, r)` (§4.5.3.7): `n` copies of `r` appended; `none` at 2^32 elements or past
the maximum. -/
def TableInst.grow (t : TableInst) (n : Nat) (r : Ref) : Option TableInst :=
  let len := t.elem.length + n
  if 2 ^ 32 ≤ len ∨ t.type.limits.max.any (· < len) then none
  else some { type := { t.type with limits := { t.type.limits with min := len } },
              elem := t.elem ++ List.replicate n r }

end FVA.Wasm.Exec
