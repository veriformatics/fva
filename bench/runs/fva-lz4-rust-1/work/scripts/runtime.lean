import Proofs.Spec

open Proofs

def hexByte (b : UInt8) : String :=
  let ds := Nat.toDigits 16 b.toNat
  "\\" ++ (if ds.length = 1 then "0" else "") ++ String.ofList ds

def quotedBytes (bs : List UInt8) : String :=
  "\"" ++ String.join (bs.map hexByte) ++ "\""

def makeCase (wasm : List UInt8) (e : Example) (i : Nat) : String := Id.run do
  let artifact := s!"artifact{i}"
  let harness := s!"harness{i}"
  let mut text := s!"(module ${artifact} binary {quotedBytes wasm})\n" ++
    s!"(register \"lz4_{i}\" ${artifact})\n" ++
    s!"(module ${harness}\n" ++
    s!"  (import \"lz4_{i}\" \"memory\" (memory 32 32))\n" ++
    s!"  (import \"lz4_{i}\" \"lz4_decompress\" (func $decode (param i32 i32 i32 i32) (result i32)))\n" ++
    s!"  (data $input {quotedBytes e.input})\n" ++
    "  (func (export \"run\") (result i32)\n" ++
    "    i32.const 131072 i32.const 165 i32.const 1966080 memory.fill\n" ++
    s!"    i32.const 131072 i32.const 0 i32.const {e.input.length} memory.init $input\n" ++
    s!"    i32.const 131072 i32.const 262144 i32.const {e.input.length} i32.const {e.cap} call $decode)\n" ++
    "  (func (export \"byte\") (param i32) (result i32) local.get 0 i32.load8_u)\n" ++
    "  (func (export \"outside\") (result i32) (local $p i32)\n" ++
    "    i32.const 131072 local.set $p\n" ++
    "    loop $scan\n" ++
    "      local.get $p i32.const 2097152 i32.eq if i32.const 1 return end\n" ++
    s!"      local.get $p i32.const {131072 + e.input.length} i32.ge_u\n" ++
    "      local.get $p i32.const 262144 i32.lt_u\n" ++
    s!"      local.get $p i32.const {262144 + e.cap} i32.ge_u i32.or i32.and\n" ++
    "      if local.get $p i32.load8_u i32.const 165 i32.ne if i32.const 0 return end end\n" ++
    "      local.get $p i32.const 1 i32.add local.set $p br $scan\n" ++
    "    end unreachable))\n" ++
    s!"(assert_return (invoke ${harness} \"run\") (i32.const {e.result.toNat}))\n" ++
    s!"(assert_return (invoke ${harness} \"outside\") (i32.const 1))\n"
  for (b, j) in e.input.zipIdx do
    text := text ++ s!"(assert_return (invoke ${harness} \"byte\" (i32.const {131072+j})) (i32.const {b.toNat}))\n"
  for (b, j) in e.output.zipIdx do
    text := text ++ s!"(assert_return (invoke ${harness} \"byte\" (i32.const {262144+j})) (i32.const {b.toNat}))\n"
  return text

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: lake env lean --run scripts/runtime.lean OUTPUT.wast")
  let wasm ← IO.FS.readBinFile "lz4-flex.wasm"
  let text := String.join (examples.zipIdx.map fun (e, i) => makeCase wasm.data.toList e i)
  IO.FS.writeFile out text
  IO.println s!"Wrote {examples.length} cases to {out} (shipped Wasm embedded verbatim)."
