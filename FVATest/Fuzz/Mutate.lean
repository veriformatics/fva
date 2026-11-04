import FVA.Tool.Encode
import FVA.Tool.Pack
import FVATest.Props

/-!
# Structure-aware mutation for the `lift` target (D76)

libFuzzer's byte mutations rarely keep a module decodable (a length change breaks a section
size), so code after a successful decode got little of a campaign. `FVATest/Fuzz/shim.c`'s
custom mutator calls these: a module's leaves (data segment bytes, import + export names) go to
libFuzzer's own mutator one at a time and come back spliced into a re-encoded module; or a
function body is replaced by a generated instruction sequence (`FVATest.Props`). An input that
does not decode gets byte mutation alone.
-/

namespace FVA.Test.Fuzz.Mutate

open FVA.Wasm FVA.Tool.Wast

/-- The decoded module of `bs`, if it decodes. -/
def decoded (bs : ByteArray) : Option Module :=
  (FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size).toOption

/-- A module's leaves: data segment bytes, then import module/field names, then export names. -/
def leaves (m : Module) : Array ByteArray :=
  (m.datas.map fun d => ByteArray.mk d.init.toArray).toArray ++
    (m.imports.flatMap fun im => [im.module.toUTF8, im.name.toUTF8]).toArray ++
    (m.exports.map (·.name.toUTF8)).toArray

/-- `m` with leaf `i` replaced by `b` (`none`: no such leaf, or a name that is not UTF-8). -/
def splice (m : Module) (i : Nat) (b : ByteArray) : Option Module := do
  let nd := m.datas.length
  if i < nd then
    return { m with datas := m.datas.modify i fun d => { d with init := b.toList } }
  let j := i - nd
  if j < 2 * m.imports.length then
    let s ← String.fromUTF8? b
    return { m with imports := m.imports.modify (j / 2) fun im =>
      if j % 2 = 0 then { im with module := s } else { im with name := s } }
  let k := j - 2 * m.imports.length
  if k < m.exports.length then
    let s ← String.fromUTF8? b
    return { m with exports := m.exports.modify k fun ex => { ex with name := s } }
  none

/-- The bytes of a module. -/
def encode (m : Module) : ByteArray := ⟨(FVA.Tool.Encode.module m).toArray⟩

/-- The decoded module of `bs`; the C mutator keeps it for the calls below (one decode each). -/
@[export fva_fuzz_decode]
def decodeOpt (bs : ByteArray) : Option Module := decoded bs

/-- The number of leaves (0 when the input did not decode). -/
@[export fva_fuzz_leaves]
def leafCount (om : Option Module) : UInt32 := (om.map fun m => (leaves m).size).getD 0 |>.toUInt32

/-- Leaf `i` (empty when there is none). -/
@[export fva_fuzz_leaf]
def leaf (om : Option Module) (i : UInt32) : ByteArray :=
  (om.bind fun m => (leaves m)[i.toNat]?).getD .empty

/-- The module re-encoded with leaf `i` replaced by `b` (empty when that fails). -/
@[export fva_fuzz_splice]
def spliceBytes (om : Option Module) (i : UInt32) (b : ByteArray) : ByteArray :=
  (om.bind fun m => (splice m i.toNat b).map encode).getD .empty

/-- The module re-encoded with one function body (or, without functions, a new data segment)
generated; empty when the input did not decode. -/
@[export fva_fuzz_regen]
def regen (om : Option Module) (seed : UInt64) : ByteArray := Id.run do
  let some m := om | return .empty
  let gen : Gen Module := do
    if m.funcs.isEmpty then
      let init ← FVA.Test.Props.listOf 8 (do return (← below 256).toUInt8)
      return { m with datas := m.datas ++ [⟨init, .passive⟩] }
    let i ← below m.funcs.length
    let body ← FVA.Test.Props.seq 4 2
    return { m with funcs := m.funcs.modify i fun f => { f with body } }
  return encode (gen.run' seed)

end FVA.Test.Fuzz.Mutate
