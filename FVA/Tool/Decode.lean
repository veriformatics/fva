import FVA.Impl.Decode

/-! `fva decode`: decode a `.wasm` file with the verified decoder and summarize the result. -/

namespace FVA.Tool

open FVA.Wasm FVA.Wasm.Decode

/-- Little-endian packing of file bytes, the representation `decode` reads. -/
def packBytes (bs : ByteArray) : Nat :=
  bs.toList.foldr (fun b acc => acc * 256 + b.toNat) 0

mutual
/-- Number of instructions in an instruction, counting nested bodies. -/
def instrCount1 : Instr → Nat
  | .block _ b | .loop _ b => 1 + instrCount b
  | .if_ _ t e => 1 + instrCount t + instrCount e
  | _ => 1
/-- Number of instructions in a sequence, counting nested bodies. -/
def instrCount : Instrs → Nat
  | .nil => 0
  | .cons i is => instrCount1 i + instrCount is
end

/-- One-line result: `ok …` with section counts, `malformed …` or `unsupported …`. -/
def decodeSummary (bs : ByteArray) : String :=
  match decode (packBytes bs) bs.size with
  | .ok m =>
    s!"ok types={m.types.length} imports={m.imports.length} funcs={m.funcs.length} " ++
    s!"tables={m.tables.length} mems={m.mems.length} globals={m.globals.length} " ++
    s!"exports={m.exports.length} elems={m.elems.length} datas={m.datas.length} " ++
    s!"instrs={(m.funcs.map fun f => instrCount f.body).sum}"
  | .error (.malformed p msg) => s!"malformed @{p}: {msg}"
  | .error (.unsupported p msg) => s!"unsupported @{p}: {msg}"

end FVA.Tool
