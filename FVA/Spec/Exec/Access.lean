import FVA.Spec.Exec.Step

/-!
# Memory accesses of a step (reviewed spec)

`Reads c ma a` / `Writes c ma a`: the step `Step` takes from `c` is an in-bounds load / store of
the memory at store address `ma` that reads / writes byte `a`. The base cases are the redexes of
the `load`, `loadPacked`, `store` and `storePacked` rules with their premises; the context cases
are `Step`'s `seq`, `label` and `frame` rules, so a relation holds at the redex the next step
reduces and nowhere else. Bulk instructions (`memory.copy`, `memory.fill`, `memory.init`) access
memory only through the packed loads and stores their rules expand into. A trapping access
(`loadTrap`, …) accesses nothing. A host call's effect on the store is the host relation's and is
no access here: footprint claims concern import-free modules, whose fresh instances call no host.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- The next step of `c` reads byte `a` of the memory at store address `ma`. -/
inductive Reads : Config → Nat → Nat → Prop where
  | load {s f t m ma mem a} {i : BitVec 32} :
      f.inst.mems[0]? = some ma → s.mems[ma]? = some mem →
      i.toNat + m.offset + t.bytes ≤ mem.size →
      i.toNat + m.offset ≤ a → a < i.toNat + m.offset + t.bytes →
      Reads ⟨s, f, [(Val.i32 i).instr, .plain (.load t m)]⟩ ma a
  | loadPacked {s f w p sx m ma mem a} {i : BitVec 32} :
      f.inst.mems[0]? = some ma → s.mems[ma]? = some mem →
      i.toNat + m.offset + p.bits / 8 ≤ mem.size →
      i.toNat + m.offset ≤ a → a < i.toNat + m.offset + p.bits / 8 →
      Reads ⟨s, f, [(Val.i32 i).instr, .plain (.loadPacked w p sx m)]⟩ ma a
  | seq {s f es vs rest ma a} :
      Reads ⟨s, f, es⟩ ma a → Reads ⟨s, f, vals vs ++ es ++ rest⟩ ma a
  | label {s f n cont es ma a} :
      Reads ⟨s, f, es⟩ ma a → Reads ⟨s, f, [.label n cont es]⟩ ma a
  | frame {s f n fi es ma a} :
      Reads ⟨s, fi, es⟩ ma a → Reads ⟨s, f, [.frame n fi es]⟩ ma a

/-- The next step of `c` writes byte `a` of the memory at store address `ma`. -/
inductive Writes : Config → Nat → Nat → Prop where
  | store {s f t m ma mem a c} {i : BitVec 32} {v : Val} :
      f.inst.mems[0]? = some ma → s.mems[ma]? = some mem →
      v.numBits t = some c → i.toNat + m.offset + t.bytes ≤ mem.size →
      i.toNat + m.offset ≤ a → a < i.toNat + m.offset + t.bytes →
      Writes ⟨s, f, [(Val.i32 i).instr, v.instr, .plain (.store t m)]⟩ ma a
  | storePacked {s f w p m ma mem a c} {i : BitVec 32} {v : Val} :
      f.inst.mems[0]? = some ma → s.mems[ma]? = some mem →
      v.intBits w = some c → i.toNat + m.offset + p.bits / 8 ≤ mem.size →
      i.toNat + m.offset ≤ a → a < i.toNat + m.offset + p.bits / 8 →
      Writes ⟨s, f, [(Val.i32 i).instr, v.instr, .plain (.storePacked w p m)]⟩ ma a
  | seq {s f es vs rest ma a} :
      Writes ⟨s, f, es⟩ ma a → Writes ⟨s, f, vals vs ++ es ++ rest⟩ ma a
  | label {s f n cont es ma a} :
      Writes ⟨s, f, es⟩ ma a → Writes ⟨s, f, [.label n cont es]⟩ ma a
  | frame {s f n fi es ma a} :
      Writes ⟨s, fi, es⟩ ma a → Writes ⟨s, f, [.frame n fi es]⟩ ma a

/-- The next step of `c` reads only bytes `a` of memories `ma` with `R ma a`, and writes only those
with `W ma a`. -/
def Within (R W : Nat → Nat → Prop) (c : Config) : Prop :=
  (∀ ma a, Reads c ma a → R ma a) ∧ (∀ ma a, Writes c ma a → W ma a)

/-- Every configuration reachable from `c` (including `c`) satisfies `P`. -/
def Throughout (H : HostSem) (P : Config → Prop) (c : Config) : Prop :=
  ∀ c', Steps H c c' → P c'

end FVA.Wasm.Exec
