import FVA.Spec.Exec.Numeric

/-!
# Reduction (reviewed spec)

`Step H c c'`: one reduction step of WebAssembly 2.0 §4.4 for FVA's profile, rule by rule in the
spec's order, with the context rules of §4.2.13 and the host-call rules of §4.4.10. `H` is the
host relation: what each host function may do (`HostSem`). Every nondeterministic choice of the
spec stays a choice here: float NaN results (`numResults` sets), `memory.grow` / `table.grow`
failing (§4.4.6/§4.4.7: failure is always allowed), and host outcomes. Bulk memory and table
instructions expand into element-wise steps exactly as the spec's equations do.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- Outcomes of a host call (§4.4.10): a store + results, a trap, or divergence (`⊥`). -/
inductive HostOutcome where
  | returned (s : Store) (vs : List Val)
  | trapped (s : Store)
  | diverged

/-- Host semantics: the outcomes a host function (by `HostId`) may produce on a store and
arguments. -/
abbrev HostSem := Nat → Store → List Val → HostOutcome → Prop

/-- `expand_F(bt)` (§3.2.2): the function type of a block type. -/
def _root_.FVA.Wasm.BlockType.expand (f : Frame) : BlockType → Option FuncType
  | .empty => some ⟨[], []⟩
  | .val t => some ⟨[], [t]⟩
  | .idx x => f.inst.types[x]?

/-- The values a function's declared locals start with (`default_t^k`). -/
def _root_.FVA.Wasm.Func.localDefaults (code : Func) : List Val :=
  code.locals.flatMap fun (n, t) => List.replicate n t.default

/-- The instruction sequence of a numeric result: its value, or `trap`. -/
def numOut : Option Val → List AInstr
  | some v => [v.instr]
  | none => [.trap]

/-- `ref.is_null` on a reference. -/
def Ref.isNull : Ref → Bool
  | .null _ => true
  | _ => false

/-- The bits of a value of number type `t` (`none` for any other value). -/
def Val.numBits : Val → NumType → Option Nat
  | .i32 v, .i32 | .f32 v, .f32 => some v.toNat
  | .i64 v, .i64 | .f64 v, .f64 => some v.toNat
  | _, _ => none

/-- The value of number type `t` with the given bits. -/
def _root_.FVA.Wasm.NumType.val : NumType → Nat → Val
  | .i32, c => .i32 (BitVec.ofNat 32 c)
  | .i64, c => .i64 (BitVec.ofNat 64 c)
  | .f32, c => .f32 (BitVec.ofNat 32 c)
  | .f64, c => .f64 (BitVec.ofNat 64 c)

/-- `|t|/8`: the byte width of a number type. -/
def _root_.FVA.Wasm.NumType.bytes : NumType → Nat
  | .i32 | .f32 => 4
  | .i64 | .f64 => 8

/-- `N` of a packed access. -/
def _root_.FVA.Wasm.PackSize.bits : PackSize → Nat
  | .p8 => 8
  | .p16 => 16
  | .p32 => 32

/-- `extend^sx_{N,|t|}(n)` of an `N`-bit packed load into an integer of width `w`. -/
def packedVal (w : Width) (N : Nat) (sx : Sx) (n : Nat) : Val :=
  match w, sx with
  | .w32, .u => .i32 (BitVec.ofNat 32 n)
  | .w32, .s => .i32 (Num.iextendS N (BitVec.ofNat 32 n))
  | .w64, .u => .i64 (BitVec.ofNat 64 n)
  | .w64, .s => .i64 (Num.iextendS N (BitVec.ofNat 64 n))

/-- The bits of an integer value of width `w`. -/
def Val.intBits : Val → Width → Option Nat
  | .i32 v, .w32 => some v.toNat
  | .i64 v, .w64 => some v.toNat
  | _, _ => none

/-- An `i32` value from a natural number (mod 2^32). -/
abbrev vi32 (n : Nat) : AInstr := (Val.i32 (BitVec.ofNat 32 n)).instr

/-- `call_indirect x y` on index `i` finds function address `a` of the expected type
(§4.4.8.7). -/
def CallTarget (s : Store) (f : Frame) (x y : Nat) (i : BitVec 32) (a : Nat) : Prop :=
  ∃ ta t fi ft, f.inst.tables[x]? = some ta ∧ s.tables[ta]? = some t ∧
    t.elem[i.toNat]? = some (.func a) ∧ s.funcs[a]? = some fi ∧ f.inst.types[y]? = some ft ∧
    fi.type = ft

/-- The store with table `ta` replaced. -/
def Store.setTable (s : Store) (ta : Nat) (t : TableInst) : Store :=
  { s with tables := s.tables.set ta t }
/-- The store with memory `ma` replaced. -/
def Store.setMem (s : Store) (ma : Nat) (m : MemInst) : Store := { s with mems := s.mems.set ma m }

/-- One reduction step. -/
inductive Step (H : HostSem) : Config → Config → Prop where
  -- numeric (§4.4.1): every allowed result
  | num {s f i args r} :
      r ∈ numResults i args →
      Step H ⟨s, f, vals args ++ [.plain i]⟩ ⟨s, f, numOut r⟩
  -- reference (§4.4.2)
  | refIsNull {s f} {r : Ref} :
      Step H ⟨s, f, [(Val.ref r).instr, .plain .refIsNull]⟩
        ⟨s, f, [vi32 (if r.isNull then 1 else 0)]⟩
  | refFunc {s f x a} :
      f.inst.funcs[x]? = some a →
      Step H ⟨s, f, [.plain (.refFunc x)]⟩ ⟨s, f, [.refFuncAddr a]⟩
  -- parametric (§4.4.4)
  | drop {s f} {v : Val} :
      Step H ⟨s, f, [v.instr, .plain .drop]⟩ ⟨s, f, []⟩
  | select {s f ts} {v₁ v₂ : Val} {c : BitVec 32} :
      Step H ⟨s, f, [v₁.instr, v₂.instr, (Val.i32 c).instr, .plain (.select ts)]⟩
        ⟨s, f, [(if c ≠ 0 then v₁ else v₂).instr]⟩
  -- variable (§4.4.5)
  | localGet {s f x} {v : Val} :
      f.locals[x]? = some v →
      Step H ⟨s, f, [.plain (.localGet x)]⟩ ⟨s, f, [v.instr]⟩
  | localSet {s f x} {v : Val} :
      x < f.locals.length →
      Step H ⟨s, f, [v.instr, .plain (.localSet x)]⟩
        ⟨s, { f with locals := f.locals.set x v }, []⟩
  | localTee {s f x} {v : Val} :
      Step H ⟨s, f, [v.instr, .plain (.localTee x)]⟩
        ⟨s, f, [v.instr, v.instr, .plain (.localSet x)]⟩
  | globalGet {s f x a g} :
      f.inst.globals[x]? = some a → s.globals[a]? = some g →
      Step H ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.instr]⟩
  | globalSet {s f x a g} {v : Val} :
      f.inst.globals[x]? = some a → s.globals[a]? = some g →
      Step H ⟨s, f, [v.instr, .plain (.globalSet x)]⟩
        ⟨{ s with globals := s.globals.set a { g with value := v } }, f, []⟩
  -- table (§4.4.6)
  | tableGet {s f x ta t} {i : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
      t.elem[i.toNat]? = some r →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.tableGet x)]⟩ ⟨s, f, [(Val.ref r).instr]⟩
  | tableGetTrap {s f x ta t} {i : BitVec 32} :
      f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
      t.elem.length ≤ i.toNat →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.tableGet x)]⟩ ⟨s, f, [.trap]⟩
  | tableSet {s f x ta t} {i : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
      i.toNat < t.elem.length →
      Step H ⟨s, f, [(Val.i32 i).instr, (Val.ref r).instr, .plain (.tableSet x)]⟩
        ⟨s.setTable ta { t with elem := t.elem.set i.toNat r }, f, []⟩
  | tableSetTrap {s f x ta t} {i : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
      t.elem.length ≤ i.toNat →
      Step H ⟨s, f, [(Val.i32 i).instr, (Val.ref r).instr, .plain (.tableSet x)]⟩
        ⟨s, f, [.trap]⟩
  | tableSize {s f x ta t} :
      f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
      Step H ⟨s, f, [.plain (.tableSize x)]⟩ ⟨s, f, [vi32 t.elem.length]⟩
  | tableGrow {s f x ta t t'} {r : Ref} {n : BitVec 32} :
      f.inst.tables[x]? = some ta → s.tables[ta]? = some t →
      t.grow n.toNat r = some t' →
      Step H ⟨s, f, [(Val.ref r).instr, (Val.i32 n).instr, .plain (.tableGrow x)]⟩
        ⟨s.setTable ta t', f, [vi32 t.elem.length]⟩
  | tableGrowFail {s f x} {r : Ref} {n : BitVec 32} :
      Step H ⟨s, f, [(Val.ref r).instr, (Val.i32 n).instr, .plain (.tableGrow x)]⟩
        ⟨s, f, [(Val.i32 (BitVec.ofInt 32 (-1))).instr]⟩
  | tableFillTrap {s f x ta t} {i n : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some ta →
      s.tables[ta]? = some t → t.elem.length < i.toNat + n.toNat →
      Step H ⟨s, f, [(Val.i32 i).instr, (Val.ref r).instr, (Val.i32 n).instr,
        .plain (.tableFill x)]⟩ ⟨s, f, [.trap]⟩
  | tableFillZero {s f x ta t} {i : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some ta →
      s.tables[ta]? = some t → i.toNat ≤ t.elem.length →
      Step H ⟨s, f, [(Val.i32 i).instr, (Val.ref r).instr, (Val.i32 0).instr,
        .plain (.tableFill x)]⟩ ⟨s, f, []⟩
  | tableFill {s f x ta t} {i n : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some ta →
      s.tables[ta]? = some t → 0 < n.toNat → i.toNat + n.toNat ≤ t.elem.length →
      Step H ⟨s, f, [(Val.i32 i).instr, (Val.ref r).instr, (Val.i32 n).instr,
        .plain (.tableFill x)]⟩
        ⟨s, f, [(Val.i32 i).instr, (Val.ref r).instr, .plain (.tableSet x),
          vi32 (i.toNat + 1), (Val.ref r).instr, vi32 (n.toNat - 1), .plain (.tableFill x)]⟩
  | tableCopyTrap {s f x y tx ty} {d s' n : BitVec 32} :
      f.inst.tables[x]? = some tx →
      f.inst.tables[y]? = some ty →
      (∃ t, s.tables[ty]? = some t ∧ t.elem.length < s'.toNat + n.toNat) ∨
        (∃ t, s.tables[tx]? = some t ∧ t.elem.length < d.toNat + n.toNat) →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.tableCopy x y)]⟩ ⟨s, f, [.trap]⟩
  | tableCopyZero {s f x y tx ty Tx Ty} {d s' : BitVec 32} :
      f.inst.tables[x]? = some tx →
      f.inst.tables[y]? = some ty → s.tables[tx]? = some Tx → s.tables[ty]? = some Ty →
      s'.toNat ≤ Ty.elem.length → d.toNat ≤ Tx.elem.length →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 0).instr,
        .plain (.tableCopy x y)]⟩ ⟨s, f, []⟩
  | tableCopyUp {s f x y tx ty Tx Ty} {d s' n : BitVec 32} :
      f.inst.tables[x]? = some tx →
      f.inst.tables[y]? = some ty → s.tables[tx]? = some Tx → s.tables[ty]? = some Ty →
      0 < n.toNat → s'.toNat + n.toNat ≤ Ty.elem.length → d.toNat + n.toNat ≤ Tx.elem.length →
      d.toNat ≤ s'.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.tableCopy x y)]⟩
        ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, .plain (.tableGet y),
          .plain (.tableSet x), vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1),
          .plain (.tableCopy x y)]⟩
  | tableCopyDown {s f x y tx ty Tx Ty} {d s' n : BitVec 32} :
      f.inst.tables[x]? = some tx →
      f.inst.tables[y]? = some ty → s.tables[tx]? = some Tx → s.tables[ty]? = some Ty →
      0 < n.toNat → s'.toNat + n.toNat ≤ Ty.elem.length → d.toNat + n.toNat ≤ Tx.elem.length →
      s'.toNat < d.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.tableCopy x y)]⟩
        ⟨s, f, [vi32 (d.toNat + n.toNat - 1), vi32 (s'.toNat + n.toNat - 1),
          .plain (.tableGet y), .plain (.tableSet x), (Val.i32 d).instr, (Val.i32 s').instr,
          vi32 (n.toNat - 1), .plain (.tableCopy x y)]⟩
  | tableInitTrap {s f x y tx ey} {d s' n : BitVec 32} :
      f.inst.tables[x]? = some tx →
      f.inst.elems[y]? = some ey →
      (∃ e, s.elems[ey]? = some e ∧ e.elem.length < s'.toNat + n.toNat) ∨
        (∃ t, s.tables[tx]? = some t ∧ t.elem.length < d.toNat + n.toNat) →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.tableInit x y)]⟩ ⟨s, f, [.trap]⟩
  | tableInitZero {s f x y tx ey T E} {d s' : BitVec 32} :
      f.inst.tables[x]? = some tx →
      f.inst.elems[y]? = some ey → s.tables[tx]? = some T → s.elems[ey]? = some E →
      s'.toNat ≤ E.elem.length → d.toNat ≤ T.elem.length →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 0).instr,
        .plain (.tableInit x y)]⟩ ⟨s, f, []⟩
  | tableInit {s f x y tx ey T E} {d s' n : BitVec 32} {r : Ref} :
      f.inst.tables[x]? = some tx →
      f.inst.elems[y]? = some ey → s.tables[tx]? = some T → s.elems[ey]? = some E →
      0 < n.toNat → s'.toNat + n.toNat ≤ E.elem.length → d.toNat + n.toNat ≤ T.elem.length →
      E.elem[s'.toNat]? = some r →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.tableInit x y)]⟩
        ⟨s, f, [(Val.i32 d).instr, (Val.ref r).instr, .plain (.tableSet x),
          vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1),
          .plain (.tableInit x y)]⟩
  | elemDrop {s f x a e} :
      f.inst.elems[x]? = some a → s.elems[a]? = some e →
      Step H ⟨s, f, [.plain (.elemDrop x)]⟩
        ⟨{ s with elems := s.elems.set a { e with elem := [] } }, f, []⟩
  -- memory (§4.4.7); `ea` is computed in ℕ, never wrapped
  | load {s f t m a mem} {i : BitVec 32} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      i.toNat + m.offset + t.bytes ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.load t m)]⟩
        ⟨s, f, [(t.val (mem.read (i.toNat + m.offset) t.bytes)).instr]⟩
  | loadTrap {s f t m a mem} {i : BitVec 32} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      mem.size < i.toNat + m.offset + t.bytes →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.load t m)]⟩ ⟨s, f, [.trap]⟩
  | loadPacked {s f w p sx m a mem} {i : BitVec 32} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      i.toNat + m.offset + p.bits / 8 ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.loadPacked w p sx m)]⟩
        ⟨s, f, [(packedVal w p.bits sx (mem.read (i.toNat + m.offset) (p.bits / 8))).instr]⟩
  | loadPackedTrap {s f w p sx m a mem} {i : BitVec 32} :
      f.inst.mems[0]? = some a →
      s.mems[a]? = some mem → mem.size < i.toNat + m.offset + p.bits / 8 →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.loadPacked w p sx m)]⟩ ⟨s, f, [.trap]⟩
  | store {s f t m a mem} {i : BitVec 32} {v : Val} {c : Nat} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      v.numBits t = some c → i.toNat + m.offset + t.bytes ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 i).instr, v.instr, .plain (.store t m)]⟩
        ⟨s.setMem a (mem.write (i.toNat + m.offset) t.bytes c), f, []⟩
  | storeTrap {s f t m a mem} {i : BitVec 32} {v : Val} {c : Nat} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      v.numBits t = some c → mem.size < i.toNat + m.offset + t.bytes →
      Step H ⟨s, f, [(Val.i32 i).instr, v.instr, .plain (.store t m)]⟩ ⟨s, f, [.trap]⟩
  | storePacked {s f w p m a mem} {i : BitVec 32} {v : Val} {c : Nat} :
      f.inst.mems[0]? = some a →
      s.mems[a]? = some mem → v.intBits w = some c →
      i.toNat + m.offset + p.bits / 8 ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 i).instr, v.instr, .plain (.storePacked w p m)]⟩
        ⟨s.setMem a (mem.write (i.toNat + m.offset) (p.bits / 8) c), f, []⟩
  | storePackedTrap {s f w p m a mem} {i : BitVec 32} {v : Val} {c : Nat} :
      f.inst.mems[0]? = some a →
      s.mems[a]? = some mem → v.intBits w = some c →
      mem.size < i.toNat + m.offset + p.bits / 8 →
      Step H ⟨s, f, [(Val.i32 i).instr, v.instr, .plain (.storePacked w p m)]⟩
        ⟨s, f, [.trap]⟩
  | memorySize {s f a mem} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      Step H ⟨s, f, [.plain .memorySize]⟩ ⟨s, f, [vi32 mem.pages]⟩
  | memoryGrow {s f a mem mem'} {n : BitVec 32} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      mem.grow n.toNat = some mem' →
      Step H ⟨s, f, [(Val.i32 n).instr, .plain .memoryGrow]⟩
        ⟨s.setMem a mem', f, [vi32 mem.pages]⟩
  | memoryGrowFail {s f} {n : BitVec 32} :
      Step H ⟨s, f, [(Val.i32 n).instr, .plain .memoryGrow]⟩
        ⟨s, f, [(Val.i32 (BitVec.ofInt 32 (-1))).instr]⟩
  | memoryFillTrap {s f a mem} {d n : BitVec 32} {v : Val} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      mem.size < d.toNat + n.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, v.instr, (Val.i32 n).instr, .plain .memoryFill]⟩
        ⟨s, f, [.trap]⟩
  | memoryFillZero {s f a mem} {d : BitVec 32} {v : Val} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      d.toNat ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 d).instr, v.instr, (Val.i32 0).instr, .plain .memoryFill]⟩
        ⟨s, f, []⟩
  | memoryFill {s f a mem} {d n : BitVec 32} {v : Val} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      0 < n.toNat → d.toNat + n.toNat ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 d).instr, v.instr, (Val.i32 n).instr, .plain .memoryFill]⟩
        ⟨s, f, [(Val.i32 d).instr, v.instr, .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
          vi32 (d.toNat + 1), v.instr, vi32 (n.toNat - 1), .plain .memoryFill]⟩
  | memoryCopyTrap {s f a mem} {d s' n : BitVec 32} :
      f.inst.mems[0]? = some a →
      s.mems[a]? = some mem →
      mem.size < s'.toNat + n.toNat ∨ mem.size < d.toNat + n.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain .memoryCopy]⟩ ⟨s, f, [.trap]⟩
  | memoryCopyZero {s f a mem} {d s' : BitVec 32} :
      f.inst.mems[0]? = some a → s.mems[a]? = some mem →
      s'.toNat ≤ mem.size → d.toNat ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 0).instr,
        .plain .memoryCopy]⟩ ⟨s, f, []⟩
  | memoryCopyUp {s f a mem} {d s' n : BitVec 32} :
      f.inst.mems[0]? = some a →
      s.mems[a]? = some mem →
      0 < n.toNat → s'.toNat + n.toNat ≤ mem.size → d.toNat + n.toNat ≤ mem.size →
      d.toNat ≤ s'.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain .memoryCopy]⟩
        ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr,
          .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
          vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1), .plain .memoryCopy]⟩
  | memoryCopyDown {s f a mem} {d s' n : BitVec 32} :
      f.inst.mems[0]? = some a →
      s.mems[a]? = some mem →
      0 < n.toNat → s'.toNat + n.toNat ≤ mem.size → d.toNat + n.toNat ≤ mem.size →
      s'.toNat < d.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain .memoryCopy]⟩
        ⟨s, f, [vi32 (d.toNat + n.toNat - 1), vi32 (s'.toNat + n.toNat - 1),
          .plain (.loadPacked .w32 .p8 .u ⟨0, 0⟩), .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
          (Val.i32 d).instr, (Val.i32 s').instr, vi32 (n.toNat - 1), .plain .memoryCopy]⟩
  | memoryInitTrap {s f x a da mem} {d s' n : BitVec 32} :
      f.inst.mems[0]? = some a →
      f.inst.datas[x]? = some da → s.mems[a]? = some mem →
      (∃ di, s.datas[da]? = some di ∧ di.data.length < s'.toNat + n.toNat) ∨
        mem.size < d.toNat + n.toNat →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.memoryInit x)]⟩ ⟨s, f, [.trap]⟩
  | memoryInitZero {s f x a da mem di} {d s' : BitVec 32} :
      f.inst.mems[0]? = some a →
      f.inst.datas[x]? = some da → s.mems[a]? = some mem → s.datas[da]? = some di →
      s'.toNat ≤ di.data.length → d.toNat ≤ mem.size →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 0).instr,
        .plain (.memoryInit x)]⟩ ⟨s, f, []⟩
  | memoryInit {s f x a da mem di b} {d s' n : BitVec 32} :
      f.inst.mems[0]? = some a →
      f.inst.datas[x]? = some da → s.mems[a]? = some mem → s.datas[da]? = some di →
      0 < n.toNat → s'.toNat + n.toNat ≤ di.data.length → d.toNat + n.toNat ≤ mem.size →
      di.data[s'.toNat]? = some b →
      Step H ⟨s, f, [(Val.i32 d).instr, (Val.i32 s').instr, (Val.i32 n).instr,
        .plain (.memoryInit x)]⟩
        ⟨s, f, [(Val.i32 d).instr, vi32 b.toNat, .plain (.storePacked .w32 .p8 ⟨0, 0⟩),
          vi32 (d.toNat + 1), vi32 (s'.toNat + 1), vi32 (n.toNat - 1),
          .plain (.memoryInit x)]⟩
  | dataDrop {s f x a di} :
      f.inst.datas[x]? = some a → s.datas[a]? = some di →
      Step H ⟨s, f, [.plain (.dataDrop x)]⟩
        ⟨{ s with datas := s.datas.set a { data := [] } }, f, []⟩
  -- control (§4.4.8)
  | nop {s f} :
      Step H ⟨s, f, [.plain .nop]⟩ ⟨s, f, []⟩
  | unreachable {s f} :
      Step H ⟨s, f, [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩
  | block {s f bt body ft vs} :
      bt.expand f = some ft → vs.length = ft.params.length →
      Step H ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
        ⟨s, f, [.label ft.results.length [] (vals vs ++ body.map .plain)]⟩
  | loop {s f bt body ft vs} :
      bt.expand f = some ft → vs.length = ft.params.length →
      Step H ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
        ⟨s, f, [.label ft.params.length [.loop bt body] (vals vs ++ body.map .plain)]⟩
  | ifTrue {s f bt thn els} {c : BitVec 32} :
      c ≠ 0 →
      Step H ⟨s, f, [(Val.i32 c).instr, .plain (.if_ bt thn els)]⟩
        ⟨s, f, [.plain (.block bt thn)]⟩
  | ifFalse {s f bt thn els} :
      Step H ⟨s, f, [(Val.i32 0).instr, .plain (.if_ bt thn els)]⟩
        ⟨s, f, [.plain (.block bt els)]⟩
  | labelExit {s f n cont vs} :
      Step H ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩
  | br {s f n cont l vs} (L : BlockCtx l) :
      vs.length = n →
      Step H ⟨s, f, [.label n cont (L.fill (vals vs ++ [.plain (.br l)]))]⟩
        ⟨s, f, vals vs ++ cont.map .plain⟩
  | brIfTrue {s f l} {c : BitVec 32} :
      c ≠ 0 →
      Step H ⟨s, f, [(Val.i32 c).instr, .plain (.brIf l)]⟩ ⟨s, f, [.plain (.br l)]⟩
  | brIfFalse {s f l} :
      Step H ⟨s, f, [(Val.i32 0).instr, .plain (.brIf l)]⟩ ⟨s, f, []⟩
  | brTable {s f ls l} {i : BitVec 32} :
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.brTable ls l)]⟩
        ⟨s, f, [.plain (.br (ls[i.toNat]?.getD l))]⟩
  | return_ {s f n f' k vs} (L : BlockCtx k) :
      vs.length = n →
      Step H ⟨s, f, [.frame n f' (L.fill (vals vs ++ [.plain .return_]))]⟩ ⟨s, f, vals vs⟩
  | call {s f x a} :
      f.inst.funcs[x]? = some a →
      Step H ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.invoke a]⟩
  | callIndirect {s f x y a} {i : BitVec 32} :
      CallTarget s f x y i a →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.callIndirect x y)]⟩ ⟨s, f, [.invoke a]⟩
  | callIndirectTrap {s f x y} {i : BitVec 32} :
      (∀ a, ¬ CallTarget s f x y i a) →
      Step H ⟨s, f, [(Val.i32 i).instr, .plain (.callIndirect x y)]⟩ ⟨s, f, [.trap]⟩
  -- function calls (§4.4.10)
  | invoke {s f a ft inst code vs} :
      s.funcs[a]? = some (.wasm ft inst code) →
      vs.length = ft.params.length →
      Step H ⟨s, f, vals vs ++ [.invoke a]⟩
        ⟨s, f, [.frame ft.results.length ⟨vs ++ code.localDefaults, inst⟩
          [.label ft.results.length [] (code.body.map .plain)]]⟩
  | frameExit {s f n f' vs} :
      vs.length = n →
      Step H ⟨s, f, [.frame n f' (vals vs)]⟩ ⟨s, f, vals vs⟩
  | invokeHost {s s' f a ft id vs res} :
      s.funcs[a]? = some (.host ft id) →
      vs.length = ft.params.length → H id s vs (.returned s' res) →
      Step H ⟨s, f, vals vs ++ [.invoke a]⟩ ⟨s', f, vals res⟩
  | invokeHostTrap {s s' f a ft id vs} :
      s.funcs[a]? = some (.host ft id) →
      vs.length = ft.params.length → H id s vs (.trapped s') →
      Step H ⟨s, f, vals vs ++ [.invoke a]⟩ ⟨s', f, [.trap]⟩
  | invokeHostDiverge {s f a ft id vs} :
      s.funcs[a]? = some (.host ft id) →
      vs.length = ft.params.length → H id s vs .diverged →
      Step H ⟨s, f, vals vs ++ [.invoke a]⟩ ⟨s, f, vals vs ++ [.invoke a]⟩
  -- contexts (§4.2.13); `seq` + `label` together give `E[es] ↪ E[es']` for every evaluation
  -- context `E`; `trap` collapses any non-trivial context in one step
  | seq {s f s' f' es es' vs rest} :
      Step H ⟨s, f, es⟩ ⟨s', f', es'⟩ →
      Step H ⟨s, f, vals vs ++ es ++ rest⟩ ⟨s', f', vals vs ++ es' ++ rest⟩
  | label {s f s' f' n cont es es'} :
      Step H ⟨s, f, es⟩ ⟨s', f', es'⟩ →
      Step H ⟨s, f, [.label n cont es]⟩ ⟨s', f', [.label n cont es']⟩
  | frame {s f s' n fi fi' es es'} :
      Step H ⟨s, fi, es⟩ ⟨s', fi', es'⟩ →
      Step H ⟨s, f, [.frame n fi es]⟩ ⟨s', f, [.frame n fi' es']⟩
  | trap {s f} (E : EvalCtx) : E.fill [.trap] ≠ [.trap] →
      Step H ⟨s, f, E.fill [.trap]⟩ ⟨s, f, [.trap]⟩
  | trapFrame {s f n fi} :
      Step H ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩

/-- Zero or more steps. -/
abbrev Steps (H : HostSem) : Config → Config → Prop := Relation.ReflTransGen (Step H)

end FVA.Wasm.Exec
