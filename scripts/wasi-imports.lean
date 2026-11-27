import FVA.Spec.Wasi.Call

/-!
U29b1: the reviewed model's preview1 imports as one WAT module (`Call.all`, each by its WITX name
`Call.info` at its raw signature `Call.sig`) with an empty `_start`; `scripts/test-wasi` links it
on the pinned wasmtime, whose linker rejects an unknown name or a mismatched signature (the
vectors call through the model's own signatures, so they never see one). Run by
`lake env lean --run scripts/wasi-imports.lean`; lives outside `FVATest/` like
`scripts/wasi-vectors.lean`.
-/

open FVA.Wasm FVA.Wasi

def valType : ValType → String
  | .num .i32 => "i32"
  | .num .i64 => "i64"
  | .num .f32 => "f32"
  | .num .f64 => "f64"
  | .ref _ => "externref"

def main : IO Unit := do
  IO.println "(module"
  for c in Call.all do
    let ps := " ".intercalate (c.sig.params.map valType)
    let rs := " ".intercalate (c.sig.results.map valType)
    let func := s!"(func (param {ps}) (result {rs}))"
    IO.println s!"  (import \"wasi_snapshot_preview1\" \"{c.info.1}\" {func})"
  IO.println "  (memory (export \"memory\") 1)"
  IO.println "  (func (export \"_start\")))"
