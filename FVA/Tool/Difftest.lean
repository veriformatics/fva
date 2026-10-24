import FVA.Impl.Exec.Det
import FVA.Spec.Claims
import FVA.Tool.Decode
import FVA.Tool.Encode
import FVA.Tool.Pack
import FVA.Tool.Wast
import Std.Data.HashMap
import Lean.Data.Json

/-!
# `fva difftest`: Lean-predicted WAST checked by wasmtime

Per exported function, a WAST script whose expected results come from the reference stepper
(`FVA.Wasm.Exec.Ref`, proven sound against `Step`) on the command sequence wasmtime runs:
import providers, the subject, a probe module over its memory, then per case an optional input
fill and the call. Contract: `docs/contracts/U5-difftest.md`.

Memory = the spec's byte function, a closure chain over writes; the runner logs each store's
range and periodically rebuilds every memory as 4 KiB chunks read back through that function
(extensionally equal while the log is complete), so long runs keep reads cheap.
-/

namespace FVA.Tool.Difftest

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num FVA.Tool.Wast

/-! ## Memory mirror -/

/-- Bytes per mirror chunk. -/
def chunk : Nat := 4096

/-- A memory's bytes `[0, size)` in chunks. -/
abbrev Chunks := Array ByteArray

/-- A zero chunk. -/
def zeroChunk : ByteArray := ⟨Array.replicate chunk 0⟩

/-- The byte at `a` (zero past the chunks). -/
def Chunks.byte (ch : Chunks) (a : Nat) : UInt8 :=
  match ch[a / chunk]? with
  | some b => b.get! (a % chunk)
  | none => 0

/-- Extend `ch` to the memory's size and copy the bytes of `ranges` (start, length) read through
the memory's own byte function; the result's byte function is the chunk lookup. -/
def flushMem (ch : Chunks) (m : MemInst) (ranges : Array (Nat × Nat)) : Chunks × MemInst :=
  Id.run do
    let mut ch := ch
    while ch.size < m.size / chunk do ch := ch.push zeroChunk
    for (ea, k) in ranges do
      for a in [ea:min (ea + k) m.size] do
        ch := ch.modify (a / chunk) fun b => b.set! (a % chunk) (m.byte a)
    let out := ch
    return (out, { m with byte := out.byte })

/-! ## Runner -/

/-- The redex `Ref.seq` steps next: its frame, the instruction, the values before it (top
first). -/
partial def redex (f : Frame) (vs : List Val) : List AInstr → Option (Frame × AInstr × List Val)
  | [] => none
  | e :: rest => match Ref.toVal e with
    | some v => redex f (v :: vs) rest
    | none => match e with
      | .label _ _ body => (redex f [] body).orElse fun _ => some (f, e, vs)
      | .frame _ fi body => (redex fi [] body).orElse fun _ => some (f, e, vs)
      | _ => some (f, e, vs)

/-- What the next step does, read off its redex (one walk): `Ref.seqTraps` (a pending trap) and
`Ref.uniqueStep` (choice points) in the cases the runner meets, plus the range a store writes. -/
inductive Effect where
  /-- A pending trap: every execution ends in a trap with this store (`must_trap`). -/
  | trap
  /-- A store to memory address `ma`: `k` bytes at `ea`. -/
  | write (ma ea k : Nat)
  /-- A memory or table growth (the stepper grows whenever the size fits). -/
  | grow
  /-- A numeric step whose result the spec may choose among NaNs. -/
  | nan
  /-- The spec's only step. -/
  | plain

/-- The effect of the next step of `c`. -/
def effect (c : Config) : Effect :=
  match redex c.frame [] c.instrs with
  | some (_, .trap, _) => .trap
  | some (f, .plain i, vs) =>
    match i, vs, f.inst.mems[0]? with
    | .store t m, _ :: .i32 a :: _, some ma => .write ma (a.toNat + m.offset) t.bytes
    | .storePacked _ p m, _ :: .i32 a :: _, some ma => .write ma (a.toNat + m.offset) (p.bits / 8)
    | .memoryGrow, _, _ | .tableGrow _, _, _ => .grow
    | _, _, _ => if Ref.instrUnique i vs then .plain else .nan
  | _ => .plain

/-- How a run ended. -/
inductive Outcome where
  | returned (vs : List Val)
  | trapped
  | exhausted
  | stuck
  deriving Inhabited

/-- Runner state: the configuration, the memory mirrors, the writes since the last flush and
since the run began, and whether the run passed a choice point. -/
structure Run where
  c : Config
  mirrors : Std.HashMap Nat Chunks
  pending : Array (Nat × Nat × Nat) := #[]
  writes : Array (Nat × Nat × Nat) := #[]
  nan : Bool := false
  grow : Bool := false

/-- Rebuild every mirrored memory from its pending writes (and any growth). -/
def Run.flush (r : Run) : Run := Id.run do
  let mut s := r.c.store
  let mut mirrors := r.mirrors
  for (ma, ch) in r.mirrors.toList do
    let ranges := r.pending.filterMap fun (a, ea, k) => if a == ma then some (ea, k) else none
    let some m := s.mems[ma]? | continue
    if ranges.isEmpty && ch.size * chunk == m.size then continue
    let (ch', m') := flushMem ch m ranges
    mirrors := mirrors.insert ma ch'
    s := s.setMem ma m'
  return { r with c := { r.c with store := s }, mirrors, pending := #[] }

/-- Writes between flushes: bounds the closure chain a memory read walks. -/
def flushEvery : Nat := 64

/-- Step `r` up to `fuel` times; a pending trap ends the run at once (`Ref.runDet`'s
normalization: the store is final). The result is flushed. -/
def Run.go : Nat → Run → Run × Outcome
  | 0, r => (r.flush, .exhausted)
  | n + 1, r =>
    let c := r.c
    match effect c with
    | .trap => ({ r with c := ⟨c.store, c.frame, [.trap]⟩ }.flush, .trapped)
    | eff =>
      match Ref.seq c.store c.frame [] c.instrs with
      | .step s f es =>
        let r := { r with c := ⟨s, f, es⟩ }
        let r := match eff with
          | .write ma ea k => { r with pending := r.pending.push (ma, ea, k),
                                       writes := r.writes.push (ma, ea, k) }
          | .grow => { r with grow := true }
          | .nan => { r with nan := true }
          | _ => r
        Run.go n (if r.pending.size ≥ flushEvery then r.flush else r)
      | .final =>
        (r.flush, if Ref.isTrapOnly c.instrs then .trapped else
          match c.instrs.mapM Ref.toVal with
          | some vs => .returned vs
          | none => .stuck)
      | _ => (r.flush, .stuck)

/-- A store with mirrored memories. -/
structure Eng where
  store : Store := {}
  mirrors : Std.HashMap Nat Chunks := {}

/-- Mirror the memories from address `lo` on, which allocation just created (all zero). -/
def Eng.mirrorFrom (e : Eng) (lo : Nat) : Eng := Id.run do
  let mut e := e
  for ma in [lo:e.store.mems.length] do
    let some m := e.store.mems[ma]? | continue
    let ch : Chunks := Array.replicate (m.size / chunk) zeroChunk
    e := { store := e.store.setMem ma { m with byte := ch.byte },
           mirrors := e.mirrors.insert ma ch }
  return e

/-- Invoke function address `a` on `args` within `fuel` steps. -/
def Eng.invoke (e : Eng) (fuel a : Nat) (args : List Val) : Eng × Run × Outcome :=
  let (r, o) := Run.go fuel { c := invokeConfig e.store a args, mirrors := e.mirrors }
  ({ store := r.c.store, mirrors := r.mirrors }, r, o)

/-- `Ref.instantiate` with the initialization code run by the mirrored runner. -/
def Eng.instantiate (e : Eng) (fuel : Nat) (m : Module) (imports : List ExternVal) :
    Except String (Eng × ModuleInst) := do
  let s := e.store
  let (s₀, inst₀) := allocModule s m imports (m.globals.map fun g => g.type.val.default)
    (m.elems.map fun _ => [])
  let consts (s : Store) (inst : ModuleInst) :=
    (m.globals.mapM fun g => Ref.evalConst fuel s inst g.init,
     m.elems.mapM fun el => el.init.mapM fun ex => Ref.evalConst fuel s inst ex >>= Ref.asRef)
  let (some gvals, some erefs) := consts s₀ inst₀ | throw "an initializer is not constant"
  let (s₁, inst) := allocModule s m imports gvals erefs
  unless consts s₁ inst == (some gvals, some erefs) do throw "initializers disagree"
  let e₁ := ({ e with store := s₁ } : Eng).mirrorFrom s.mems.length
  let (r, o) := Run.go fuel
    { c := ⟨e₁.store, ⟨[], inst⟩, (initCode m).map .plain⟩, mirrors := e₁.mirrors }
  match o with
  | .returned [] => return ({ store := r.c.store, mirrors := r.mirrors }, inst)
  | .trapped => throw "instantiation traps"
  | .exhausted => throw "instantiation exceeds the fuel"
  | _ => throw "instantiation is stuck"

/-! ## Fixture modules -/

/-- `fill(lo, len, seed)`: `len` xorshift32 bytes from `lo`. -/
def fillBody : List Instr :=
  let xs (k : Nat) (op : IBinOp) : List Instr :=
    [.localGet 2, .localGet 2, .iconst .w32 k, .ibinop .w32 op, .ibinop .w32 .xor, .localSet 2]
  [.localGet 2, .iconst .w32 1, .ibinop .w32 .or, .localSet 2,
   .block .empty [.loop .empty (
     [.localGet 1, .itestEqz .w32, .brIf 1] ++ xs 13 .shl ++ xs 17 (.shr .u) ++ xs 5 .shl ++
     [.localGet 0, .localGet 2, .storePacked .w32 .p8 ⟨0, 0⟩,
      .localGet 0, .iconst .w32 1, .ibinop .w32 .add, .localSet 0,
      .localGet 1, .iconst .w32 1, .ibinop .w32 .sub, .localSet 1, .br 0])]]

/-- FNV-1a 64 offset basis and prime. -/
def fnvBasis : UInt64 := 0xcbf29ce484222325
/-- See `fnvBasis`. -/
def fnvPrime : UInt64 := 0x100000001b3

/-- `digest(lo, len)`: FNV-1a 64 of the bytes `[lo, lo + len)`. -/
def digestBody : List Instr :=
  [.iconst .w64 fnvBasis.toNat, .localSet 2,
   .block .empty [.loop .empty
     [.localGet 1, .itestEqz .w32, .brIf 1,
      .localGet 2, .localGet 0, .loadPacked .w64 .p8 .u ⟨0, 0⟩, .ibinop .w64 .xor,
      .iconst .w64 fnvPrime.toNat, .ibinop .w64 .mul, .localSet 2,
      .localGet 0, .iconst .w32 1, .ibinop .w32 .add, .localSet 0,
      .localGet 1, .iconst .w32 1, .ibinop .w32 .sub, .localSet 1, .br 0]],
   .localGet 2]

/-- The probe: the subject's memory, imported from `(mod, name)`, with `fill` and `digest`. -/
def probe (mod name : String) : Module :=
  let i32 : ValType := .num .i32
  { types := [⟨[i32, i32, i32], []⟩, ⟨[i32, i32], [.num .i64]⟩],
    imports := [⟨mod, name, .mem ⟨0, none⟩⟩],
    funcs := [⟨0, [], fillBody⟩, ⟨1, [(1, .num .i64)], digestBody⟩],
    exports := [⟨"fill", .func 0⟩, ⟨"digest", .func 1⟩] }

/-- FNV-1a 64 of `[lo, lo + n)`, natively (the probe's `digest`). -/
def fnv (m : MemInst) (lo n : Nat) : UInt64 := Id.run do
  let mut h := fnvBasis
  for a in [lo:lo + n] do h := (h ^^^ (m.byte a).toUInt64) * fnvPrime
  return h

/-- The assertion that the probe `pname` digests `[lo, lo + n)` of `m` as Lean predicts. -/
def digestLine (pname : String) (m : MemInst) (lo n : Nat) : String :=
  s!"(assert_return (invoke {pname} \"digest\" (i32.const {lo}) (i32.const {n})) " ++
    s!"(i64.const {(fnv m lo n).toNat}))"

/-- A global's initial value in a provider: zero, except a mutable i32 `__stack_pointer`, which
starts at `sp` (the top of the first memory) so C stacks have room. -/
def providerInit (name : String) (sp : Nat) (gt : GlobalType) : Expr :=
  match gt.val with
  | .num .i32 =>
    [.iconst .w32 (if name == "__stack_pointer" && gt.mutability == .var then sp else 0)]
  | .num .i64 => [.iconst .w64 0]
  | .num .f32 => [.fconst .w32 0]
  | .num .f64 => [.fconst .w64 0]
  | .ref t => [.refNull t]

/-- A module supplying `ims` (one import module's entries), each exported under its import
name: functions trap, memories and tables take the import's limits. -/
def provider (types : List FuncType) (ims : List Import) (sp : Nat) : Module := Id.run do
  let mut md : Module := {}
  let mut seen : List String := []
  for im in ims do
    if seen.contains im.name then continue
    seen := im.name :: seen
    match im.desc with
    | .func x =>
      md := { md with types := md.types ++ [types[x]?.getD ⟨[], []⟩],
                      funcs := md.funcs ++ [⟨md.types.length, [], [.unreachable]⟩],
                      exports := md.exports ++ [⟨im.name, .func md.funcs.length⟩] }
    | .table tt =>
      md := { md with tables := md.tables ++ [tt],
                      exports := md.exports ++ [⟨im.name, .table md.tables.length⟩] }
    | .mem lim =>
      md := { md with mems := md.mems ++ [lim],
                      exports := md.exports ++ [⟨im.name, .mem md.mems.length⟩] }
    | .global gt =>
      md := { md with globals := md.globals ++ [⟨gt, providerInit im.name sp gt⟩],
                      exports := md.exports ++ [⟨im.name, .global md.globals.length⟩] }
  return md

/-- Encode a fixture and decode it back with the verified decoder, so Lean runs exactly the
bytes wasmtime gets. -/
def roundTrip (md : Module) : Except String (ByteArray × Module) :=
  let bs : ByteArray := ⟨(FVA.Tool.Encode.module md).toArray⟩
  match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
  | .ok m => .ok (bs, m)
  | .error e => .error s!"a fixture does not decode ({FVA.Tool.decodeError e})"

/-! ## WAST text -/

/-- A WAST string literal: printable ASCII as is, every other byte as `\hh`. -/
def wastString (bs : ByteArray) : String := Id.run do
  let mut out := "\""
  for b in bs.toList do
    let c := Char.ofNat b.toNat
    out := if 0x20 ≤ b && b < 0x7F && c != '"' && c != '\\' then out.push c
      else out ++ "\\" ++ hex b.toNat 2
  return out.push '"'

/-- A WAST name string. -/
def nameLit (s : String) : String := wastString s.toUTF8

/-- A value as a WAST constant; a function reference prints as the non-null pattern. -/
def valLit : Val → String
  | .i32 v => s!"(i32.const {v.toNat})"
  | .i64 v => s!"(i64.const {v.toNat})"
  | .f32 v => s!"(f32.const {lit f32fmt v.toNat})"
  | .f64 v => s!"(f64.const {lit f64fmt v.toNat})"
  | .ref (.null .funcref) => "(ref.null func)"
  | .ref (.null .externref) => "(ref.null extern)"
  | .ref (.func _) => "(ref.func)"
  | .ref (.extern a) => s!"(ref.extern {a})"

/-- An expected result after a choice point: a quiet NaN may be any arithmetic NaN. -/
def choiceLit : Val → String
  | .f32 v => match payload f32fmt v.toNat with
    | some p => if p ≥ f32fmt.canon then "(f32.const nan:arithmetic)" else valLit (.f32 v)
    | none => valLit (.f32 v)
  | .f64 v => match payload f64fmt v.toNat with
    | some p => if p ≥ f64fmt.canon then "(f64.const nan:arithmetic)" else valLit (.f64 v)
    | none => valLit (.f64 v)
  | v => valLit v

/-! ## Scripts -/

/-- Options. -/
structure Config where
  cases : Nat := 32
  seed : Nat := 1
  fuel : Nat := 300000
  initFuel : Nat := 10000000
  exports : List String := []

/-- A script line's meaning, for reporting wasmtime's first failing directive. -/
structure Line where
  text : String
  what : String

/-- One instantiation epoch: providers, subject and probe, live in the engine. -/
structure Epoch where
  lines : Array Line
  eng : Eng
  subject : ModuleInst
  subjectName : String
  /-- The probe's WAST name, instance, and the subject memory's address. -/
  probe : Option (String × ModuleInst × Nat)
  /-- Mutable exported globals: WAST instance name, export name, global address. -/
  globals : List (String × String × Nat)

/-- The exported external value `name` of `inst`. -/
def exported (inst : ModuleInst) (name : String) : Option ExternVal :=
  (inst.exports.find? (·.name == name)).map (·.value)

/-- A subject prepared for scripts: its bytes, module and fixture modules. -/
structure Subject where
  bytes : ByteArray
  module : Module
  /-- Import module name, WAST-ready bytes, decoded fixture. -/
  providers : List (String × ByteArray × Module)
  /-- Where the probe imports the memory from, if the memory is observable. -/
  memSource : Option (String × String)

/-- The register name of the subject instance. -/
def subjectRegister : String := "fva-subject"

/-- Prepare providers and the memory source of a decoded subject. -/
def Subject.make (bytes : ByteArray) (m : Module) : Except String Subject := do
  let memImport := m.imports.find? fun im => match im.desc with | .mem _ => true | _ => false
  let memMin := match memImport, m.mems with
    | some ⟨_, _, .mem lim⟩, _ => lim.min
    | _, lim :: _ => lim.min
    | _, _ => 0
  let sp := min (memMin * 65536) (2 ^ 32 - 16)
  let mods := m.imports.foldl
    (fun acc im => if acc.contains im.module then acc else acc ++ [im.module]) []
  let providers ← mods.mapM fun mod => do
    let (bs, pm) ← roundTrip (provider m.types (m.imports.filter (·.module == mod)) sp)
    return (mod, bs, pm)
  let memExport := m.exports.find? fun e => match e.desc with | .mem _ => true | _ => false
  let memSource := match memImport, memExport with
    | some im, _ => some (im.module, im.name)
    | none, some e => some (subjectRegister, e.name)
    | none, none => none
  return { bytes, module := m, providers, memSource }

/-- Instantiate providers, subject and probe as epoch `k` on top of `e`. -/
def Subject.epoch (sub : Subject) (cfg : Config) (k : Nat) (e : Eng) : Except String Epoch := do
  let mut e := e
  let mut lines : Array Line := #[]
  let mut reg : List (String × ModuleInst) := []
  let mut globals : List (String × String × Nat) := []
  let resolve (reg : List (String × ModuleInst)) (m : Module) : Except String (List ExternVal) :=
    m.imports.mapM fun im => match (reg.lookup im.module).bind (exported · im.name) with
      | some v => .ok v
      | none => .error s!"unresolved import {im.module}.{im.name}"
  let mutGlobals (wname : String) (inst : ModuleInst) (s : Store) : List (String × String × Nat) :=
    inst.exports.filterMap fun ex => match ex.value with
      | .global a => match s.globals[a]? with
        | some g => if g.type.mutability == .var then some (wname, ex.name, a) else none
        | none => none
      | _ => none
  for (mod, bs, pm, i) in sub.providers.zipIdx.map fun ((a, b, c), i) => (a, b, c, i) do
    let wname := s!"$P{i}_{k}"
    let (e', inst) ← e.instantiate cfg.initFuel pm (← resolve reg pm)
    e := e'
    reg := (mod, inst) :: reg
    lines := lines.push ⟨s!"(module {wname} binary {wastString bs})", s!"provider {mod}"⟩
      |>.push ⟨s!"(register {nameLit mod} {wname})", s!"provider {mod}"⟩
    globals := globals ++ mutGlobals wname inst e.store
  let sname := s!"$S{k}"
  let (e', subject) ← e.instantiate cfg.initFuel sub.module (← resolve reg sub.module)
  e := e'
  reg := (subjectRegister, subject) :: reg
  lines := lines.push ⟨s!"(module {sname} binary {wastString sub.bytes})", "subject"⟩
    |>.push ⟨s!"(register {nameLit subjectRegister} {sname})", "subject"⟩
  globals := globals ++ mutGlobals sname subject e.store
  let mut probeOut := none
  if let some (mod, name) := sub.memSource then
    let (bs, pm) ← roundTrip (probe mod name)
    let pname := s!"$Q{k}"
    let imports ← resolve reg pm
    let (e', pinst) ← e.instantiate cfg.initFuel pm imports
    e := e'
    lines := lines.push ⟨s!"(module {pname} binary {wastString bs})", "probe"⟩
    if let some (.mem ma) := imports.head? then probeOut := some (pname, pinst, ma)
  return { lines, eng := e, subject, subjectName := sname, probe := probeOut, globals }

/-- Boundary values of an integer width `N`. -/
def edges (N : Nat) : List Nat :=
  [0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 100, 127, 128, 255, 256, 1023, 1024, 4095, 4096,
    65535, 65536, 2 ^ (N - 1) - 1, 2 ^ (N - 1), 2 ^ N - 2, 2 ^ N - 1]

/-- Buffer-shaped integers of a case: input base `p` (filled), its length `len`, output base
`q`, capacity `cap`. -/
structure Shape where
  p : Nat
  len : Nat
  q : Nat
  cap : Nat

/-- An argument of type `t`. Integers: in a structured case, a buffer-shaped value or a small
one (C-ABI pointer/length parameters then mostly stay in bounds); otherwise a boundary, buffer,
small or random value. Floats: boundary-biased bit patterns. References: null. -/
def genArg (memSize : Nat) (sh : Shape) (structured : Bool) (t : ValType) : Gen Val := do
  let int (N : Nat) : Gen Nat := do
    if structured then
      match ← below 5 with
      | 0 => return sh.p
      | 1 => return sh.q
      | 2 => return sh.len
      | 3 => return sh.cap
      | _ => below 256
    else match ← below 8 with
      | 0 | 1 => let es := edges N; return es[← below es.length]!
      | 2 => return sh.p
      | 3 => return sh.len
      | 4 => return sh.p + sh.len
      | 5 => below 256
      | 6 => below (max memSize 65536)
      | _ => below (2 ^ N)
  match t with
  | .num .i32 => return .i32 (BitVec.ofNat 32 (← int 32))
  | .num .i64 => return .i64 (BitVec.ofNat 64 (← int 64))
  | .num .f32 => return .f32 (BitVec.ofNat 32 (← operand f32fmt none))
  | .num .f64 => return .f64 (BitVec.ofNat 64 (← operand f64fmt none))
  | .ref t => return .ref (.null t)

/-- A case's shape, input fill seed (if the memory is observable and the case fills) and
arguments. -/
def genCase (memSize : Nat) (params : List ValType) : Gen (Shape × Option Nat × List Val) := do
  let structured := (← below 2) == 0
  let len ← below 257
  let cap := len + (← below 1024)
  let room := memSize - min memSize (len + cap)
  let r ← below (max 1 room)
  let r' ← below (max 1 room)
  let coin ← below 2
  let seed ← below (2 ^ 32)
  let sh : Shape := { p := r / 8 * 8, len, q := r' / 8 * 8, cap }
  let args ← params.mapM (genArg memSize sh structured)
  return (sh, if room > 0 && (structured || coin == 0) then some seed else none, args)

/-- Merge write ranges (memory address, start, length) of memory `ma` within `size` into
sorted disjoint ranges; gaps under 64 bytes join. -/
def mergeRanges (ws : Array (Nat × Nat × Nat)) (ma size : Nat) : List (Nat × Nat) :=
  let rs := (ws.filterMap fun (a, ea, k) =>
    if a == ma && ea < size then some (ea, min (ea + k) size) else none).qsort (·.1 < ·.1)
  let merged := rs.foldl (fun (acc : List (Nat × Nat)) (lo, hi) => match acc with
    | (plo, phi) :: rest => if lo ≤ phi + 64 then (plo, max phi hi) :: rest else (lo, hi) :: acc
    | [] => [(lo, hi)]) []
  merged.reverse.map fun (lo, hi) => (lo, hi - lo)

/-- Per-function statistics. -/
structure Stats where
  cases : Nat := 0
  exhausted : Nat := 0
  choices : Nat := 0
  grows : Nat := 0
  assertions : Nat := 0
  epochs : Nat := 1

/-- A function's script, or the reason the Lean side could not produce one. -/
structure Script where
  name : String
  lines : Array Line
  stats : Stats
  error : Option String := none

/-- The script for export `name` (function address `a` of type `ft`) from epoch 0 `ep`. -/
def script (sub : Subject) (cfg : Config) (name : String) (ft : FuncType) (ep₀ : Epoch) :
    Script := Id.run do
  let mut ep := ep₀
  let mut lines := ep.lines
  let mut st : Stats := {}
  let mut g : UInt64 := (cfg.seed.toUInt64 * 0x9E3779B97F4A7C15) ^^^ hash name
  for _ in [0:cfg.cases] do
    let fail (e : String) : Script := { name, lines, stats := st, error := some e }
    let some (.func a) := exported ep.subject name | return fail "export vanished"
    let mem := ep.probe.bind fun (_, _, ma) => ep.eng.store.mems[ma]?
    let memSize := (mem.map (·.size)).getD 0
    let ((sh, fill, args), g') := (genCase memSize ft.params).run g
    g := g'
    let (p, len) := (sh.p, sh.len)
    -- input fill through the probe
    if let (some seed, some (pname, pinst, ma)) := (fill, ep.probe) then
      let some (.func fa) := exported pinst "fill" | return fail "probe lacks fill"
      let fargs := [p, len, seed].map fun n => Val.i32 (BitVec.ofNat 32 n)
      let (eng, _, o) := ep.eng.invoke cfg.fuel fa fargs
      let .returned [] := o | return fail "probe fill failed"
      ep := { ep with eng }
      let call := s!"(invoke {pname} \"fill\" {" ".intercalate (fargs.map valLit)})"
      lines := lines.push ⟨s!"(assert_return {call})", s!"case {st.cases}: fill [{p}, {p + len})"⟩
      st := { st with assertions := st.assertions + 1 }
      if let some m := eng.store.mems[ma]? then
        lines := lines.push
          ⟨digestLine pname m p len, s!"case {st.cases}: fill digest [{p}, {p + len})"⟩
        st := { st with assertions := st.assertions + 1 }
    let (eng, run, o) := ep.eng.invoke cfg.fuel a args
    let call :=
      s!"(invoke {ep.subjectName} {nameLit name}{String.join (args.map (" " ++ valLit ·))})"
    let what := s!"case {st.cases}: {call}"
    match o with
    | .exhausted => st := { st with exhausted := st.exhausted + 1 }; continue
    | .stuck => return { name, lines, stats := st,
                         error := some s!"the Lean stepper is stuck: {what}" }
    | .trapped =>
      lines := lines.push ⟨s!"(assert_trap {call} \"\")", what ++ " → trap"⟩
    | .returned vs =>
      let shown := String.join (vs.map fun v => " " ++ (if run.nan then choiceLit v else valLit v))
      lines := lines.push ⟨s!"(assert_return {call}{shown})", what ++ " →" ++ shown⟩
    st := { st with cases := st.cases + 1, assertions := st.assertions + 1,
                    grows := st.grows + (if run.grow then 1 else 0) }
    if run.nan then
      -- a NaN choice: memory and globals may differ legitimately; continue on fresh instances
      st := { st with choices := st.choices + 1, epochs := st.epochs + 1 }
      match sub.epoch cfg (st.epochs - 1) eng with
      | .ok ep' => ep := ep'; lines := lines ++ ep'.lines
      | .error e => return { name, lines, stats := st, error := some s!"re-instantiation: {e}" }
      continue
    ep := { ep with eng }
    if let some (pname, _, ma) := ep.probe then
      if let some m := eng.store.mems[ma]? then
        for (lo, n) in mergeRanges run.writes ma m.size do
          lines := lines.push ⟨digestLine pname m lo n, s!"{what}: memory digest [{lo}, {lo + n})"⟩
          st := { st with assertions := st.assertions + 1 }
    for (wname, gname, ga) in ep.globals do
      if let some gi := eng.store.globals[ga]? then
        lines := lines.push ⟨s!"(assert_return (get {wname} {nameLit gname}) {valLit gi.value})",
          s!"{what}: global {gname}"⟩
        st := { st with assertions := st.assertions + 1 }
  return { name, lines, stats := st }

/-! ## Driver -/

/-- A function's script and wasmtime's first failure on it (`none` = every directive passed). -/
structure Verdict where
  script : Script
  failure : Option String
  /-- wasmtime did not run the script (not spawned, or killed by a signal): no verdict. -/
  infra : Bool := false

/-- A module's verdicts, or why FVA could not script it. -/
structure ModuleReport where
  path : String
  size : Nat
  verdicts : Array Verdict := #[]
  error : Option String := none

/-- Script every selected export of a module, one task per function. -/
def scripts (cfg : Config) (bs : ByteArray) : Except String (Array Script) := do
  let m ← match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m => .ok m
    | .error e => .error s!"the file does not decode ({FVA.Tool.decodeError e})"
  let sub ← Subject.make bs m
  let ep ← sub.epoch cfg 0 {}
  let fns := ep.subject.exports.filterMap fun ex => match ex.value with
    | .func a => if cfg.exports.isEmpty || cfg.exports.contains ex.name then
        (ep.eng.store.funcs[a]?).map fun fi => (ex.name, fi.type) else none
    | _ => none
  let tasks := fns.map fun (name, ft) => Task.spawn fun _ => script sub cfg name ft ep
  return (tasks.map Task.get).toArray

/-- The line number of the first failing directive in `wasmtime wast` output. -/
def failedLine (out : String) : Option Nat := do
  let rest ← (out.splitOn "failed directive on ")[1]?
  let loc ← (rest.splitOn "\n").head?
  (loc.splitOn ":").getLast?.bind String.toNat?

/-- What failed: the directive's meaning and wasmtime's reason. -/
def explain (sc : Script) (out : String) : String :=
  let reason := (out.splitOn "\n").filter (fun l => !l.trimAscii.isEmpty && !l.startsWith "Error:")
  let head := match failedLine out with
    | some n => (sc.lines[n - 1]?.map (·.what)).getD s!"line {n}"
    | none => "wasmtime did not run the script"
  "\n".intercalate (head :: (reason.take 6).map ("    " ++ ·))

/-- Run `wasmtime wast` on each file, `jobs` at a time: exit code + output per file. -/
def runWast (files : Array System.FilePath) (jobs : Nat) : IO (Array (UInt32 × String)) := do
  let mut out := #[]
  let mut i := 0
  while i < files.size do
    let tasks ← (files.extract i (i + max jobs 1)).mapM fun f =>
      IO.asTask (IO.Process.output { cmd := "wasmtime", args := #["wast", f.toString] })
    for t in tasks do
      out := out.push <| match ← IO.wait t with
        | .ok o => (o.exitCode, o.stdout ++ o.stderr)
        | .error e => (127, s!"cannot run wasmtime: {e}")
    i := i + max jobs 1
  return out

/-- Script, run and judge every file; scripts go to `dir`. -/
def check (cfg : Config) (paths : List String) (dir : System.FilePath) (jobs : Nat) :
    IO (Array ModuleReport) := do
  let mut reports := #[]
  for (path, mi) in paths.zipIdx do
    let bs ← match ← (IO.FS.readBinFile path).toBaseIO with
      | .ok bs => pure bs
      | .error e =>
        let why := (toString e).replace "\n" "; "
        reports := reports.push { path, size := 0, error := some s!"cannot read the file ({why})" }
        continue
    match scripts cfg bs with
    | .error e => reports := reports.push { path, size := bs.size, error := some e }
    | .ok scs =>
      let files := scs.mapIdx fun fi _ => dir / s!"m{mi}-f{fi}.wast"
      for (sc, f) in scs.zip files do
        IO.FS.writeFile f ("\n".intercalate (sc.lines.map (·.text)).toList ++ "\n")
      let runs ← runWast files jobs
      let verdicts := (scs.zip runs).map fun (sc, rc, out) =>
        { script := sc, failure := if rc == 0 then none else some (explain sc out),
          infra := rc == 127 || rc ≥ 128 : Verdict }
      reports := reports.push { path, size := bs.size, verdicts }
  return reports

/-- A verdict's status: `pass`, `fail` (wasmtime disagrees) or `error` (no script). -/
def Verdict.status (v : Verdict) : String :=
  if v.script.error.isSome then "error" else if v.failure.isSome then "fail" else "pass"

/-- Every function of every module passed. -/
def allPass (rs : Array ModuleReport) : Bool :=
  rs.all fun r => r.error.isNone && r.verdicts.all (·.status == "pass")

/-- The plain-text report. -/
def render (header : String) (rs : Array ModuleReport) : String := Id.run do
  let mut out := header ++ "\n"
  let mut pass := 0
  let mut total := 0
  for r in rs do
    out := out ++ s!"{r.path} ({r.size} bytes)\n"
    if let some e := r.error then out := out ++ s!"  ✗ {e}\n"
    for v in r.verdicts do
      let st := v.script.stats
      let extra := [(st.exhausted, "out of fuel"), (st.choices, "NaN choice"), (st.grows, "growth")]
        |>.filter (·.1 > 0) |>.map fun (n, w) => s!"{n} {w}"
      let notes := if extra.isEmpty then "" else s!" ({", ".intercalate extra})"
      total := total + 1
      match v.script.error, v.failure with
      | some e, _ => out := out ++ s!"  ✗ {v.script.name}: {e}\n"
      | none, some f => out := out ++ s!"  ✗ {v.script.name}: {f}\n"
      | none, none =>
        pass := pass + 1
        out := out ++ s!"  ✓ {v.script.name}: {st.cases} cases, {st.assertions} assertions{notes}\n"
  let failed := total - pass + (rs.filter (·.error.isSome)).size
  out := out ++ (if failed == 0 then s!"Result: wasmtime agrees on all {total} functions.\n"
    else s!"Result: {failed} of {total + (rs.filter (·.error.isSome)).size} checks fail.\n")
  return out

open Lean in
/-- The JSON report. -/
def toJson (header : Json) (rs : Array ModuleReport) : Json :=
  let fn (v : Verdict) : Json :=
    let st := v.script.stats
    Json.mkObj [("name", v.script.name), ("status", v.status), ("cases", st.cases),
      ("assertions", st.assertions), ("exhausted", st.exhausted), ("nanChoices", st.choices),
      ("growths", st.grows), ("detail", match v.script.error, v.failure with
        | some e, _ => Json.str e | none, some f => Json.str f | none, none => Json.null)]
  Json.mkObj [("ok", allPass rs), ("run", header), ("modules", Json.arr (rs.map fun r =>
    Json.mkObj [("path", r.path), ("bytes", r.size),
      ("error", match r.error with | some e => Json.str e | none => Json.null),
      ("functions", Json.arr (r.verdicts.map fn))]))]

/-- Usage of `fva difftest`. -/
def usage : String :=
  "Usage: fva difftest <file.wasm>... [options]\n\n" ++
  "Run each exported function on generated inputs. The Lean semantics predicts every result,\n" ++
  "and wasmtime checks each prediction.\n\n" ++
  "Options:\n" ++
  "  --cases N      Run N cases for each function (default 32).\n" ++
  "  --seed S       Use seed S for the inputs (default 1).\n" ++
  "  --fuel F       Drop a case when the Lean run takes more than F steps (default 300000).\n" ++
  "  --export NAME  Test only the export NAME. You can give this option more than once.\n" ++
  "  --jobs J       Run J wasmtime processes at the same time (default 8).\n" ++
  "  --keep DIR     Write the WAST scripts to DIR and keep them.\n" ++
  "  --json         Write the report as JSON.\n\n" ++
  "Exit status: 0 when wasmtime agrees with every prediction, 1 when it does not or a file\n" ++
  "cannot be tested, 2 for a usage error, 3 when wasmtime cannot run (not found or crashed).\n"

/-- Parsed command line. -/
structure Args where
  cfg : Config := {}
  paths : List String := []
  keep : Option String := none
  jobs : Nat := 8
  json : Bool := false

/-- Parse `fva difftest` arguments. -/
def parseArgs : List String → Args → Except String Args
  | [], a => if a.paths.isEmpty then .error "no .wasm file given"
    else .ok { a with paths := a.paths.reverse }
  | "--json" :: rest, a => parseArgs rest { a with json := true }
  | opt :: v :: rest, a =>
    let num := v.toNat?
    match opt, num with
    | "--cases", some n => parseArgs rest { a with cfg := { a.cfg with cases := n } }
    | "--seed", some n => parseArgs rest { a with cfg := { a.cfg with seed := n } }
    | "--fuel", some n => parseArgs rest { a with cfg := { a.cfg with fuel := n } }
    | "--jobs", some n => parseArgs rest { a with jobs := n }
    | "--export", _ => parseArgs rest { a with cfg := { a.cfg with exports := v :: a.cfg.exports } }
    | "--keep", _ => parseArgs rest { a with keep := some v }
    | _, _ => if opt.startsWith "--" then .error s!"bad option {opt} {v}"
      else parseArgs (v :: rest) { a with paths := opt :: a.paths }
  | [p], a => if p.startsWith "--" then .error s!"bad option {p}"
    else parseArgs [] { a with paths := p :: a.paths }

/-- `fva difftest`. -/
def main (argv : List String) : IO UInt32 := do
  if argv.contains "--help" || argv.contains "-h" then
    IO.print usage
    return 0
  let a ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e =>
      IO.eprint s!"fva difftest: {e}\n\n{usage}"
      return 2
  let version ← try
      let o ← IO.Process.output { cmd := "wasmtime", args := #["--version"] }
      pure (o.stdout.trimAscii.toString)
    catch _ =>
      IO.eprintln "fva difftest: wasmtime is not on PATH. Install wasmtime, then try again."
      return 3
  let run (dir : System.FilePath) := check a.cfg a.paths dir a.jobs
  let reports ← match a.keep with
    | some d => do IO.FS.createDirAll d; run d
    | none => IO.FS.withTempDir run
  if a.json then
    IO.println (toJson (Lean.Json.mkObj [("wasmtime", version), ("seed", a.cfg.seed),
      ("cases", a.cfg.cases), ("fuel", a.cfg.fuel)]) reports).pretty
  else
    let header := s!"fva difftest: {version}; seed {a.cfg.seed}; {a.cfg.cases} cases per function"
    IO.print (render header reports)
  return if reports.any (·.verdicts.any (·.infra)) then 3 else if allPass reports then 0 else 1

end FVA.Tool.Difftest
