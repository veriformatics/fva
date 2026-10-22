import FVA.Impl.Decode
import FVA.Tool.Pack

/-! `fva decode`: decode a `.wasm` file with the verified decoder and summarize the result. -/

namespace FVA.Tool

open FVA.Wasm FVA.Wasm.Decode

mutual
/-- Number of instructions in an instruction, counting nested bodies. -/
def instrCount1 : Instr → Nat
  | .block _ b | .loop _ b => 1 + instrCount b
  | .if_ _ t e => 1 + instrCount t + instrCount e
  | _ => 1
/-- Number of instructions in a sequence, counting nested bodies. -/
def instrCount : List Instr → Nat
  | [] => 0
  | i :: is => instrCount1 i + instrCount is
end

/-- A decoding error in words. -/
def decodeError : DecodeError → String
  | .malformed p msg => s!"malformed at byte {p}: {msg}"
  | .unsupported p msg => s!"unsupported at byte {p}: {msg}"

/-- One-line result: `ok …` with section counts, `malformed …` or `unsupported …`. -/
def decodeSummary (bs : ByteArray) : String :=
  match decode (packBytes bs) bs.size with
  | .ok m =>
    s!"ok types={m.types.length} imports={m.imports.length} funcs={m.funcs.length} " ++
    s!"tables={m.tables.length} mems={m.mems.length} globals={m.globals.length} " ++
    s!"exports={m.exports.length} elems={m.elems.length} datas={m.datas.length} " ++
    s!"instrs={(m.funcs.map fun f => instrCount f.body).sum}"
  | .error e => decodeError e

end FVA.Tool
