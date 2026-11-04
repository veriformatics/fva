import Lean

/-! Native model outputs → WAST: exact return + byte equality, no model-derived artifact prediction.
T2 compares the whole caller region; T3 compares the successful returned prefix. -/

def unhex (s : String) : Except String ByteArray := do
  if s == "-" then return .empty
  let a := s.toList.toArray
  if a.size % 2 != 0 then throw "odd hex length"
  let digit (c : Char) : Except String Nat :=
    if c >= '0' && c <= '9' then pure (c.toNat - '0'.toNat)
    else if c >= 'a' && c <= 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw "invalid hex digit"
  let mut out := ByteArray.empty
  for i in [:a.size / 2] do
    out := out.push (UInt8.ofNat ((← digit a[i * 2]!) * 16 + (← digit a[i * 2 + 1]!)))
  return out

def quotedBytes (a : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := "\""
  for b in a do
    out := out.push '\\' |>.push digits[b.toNat / 16]! |>.push digits[b.toNat % 16]!
  return out ++ "\""

def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid integer: {s}"

def bytes (s : String) : IO ByteArray :=
  match unhex s with
  | .ok b => pure b
  | .error e => throw <| IO.userError e

def main (args : List String) : IO UInt32 := do
  let [task, wasm, cases, results, out] := args | do
    IO.eprintln ("Usage: lake env lean --run Fidelity.lean " ++
      "lz4-c|lz4-rust WASM CASES MODEL_OUTPUT OUT.wast")
    return 2
  unless task == "lz4-c" || task == "lz4-rust" do return 2
  let inputs := ((← IO.FS.readFile cases).splitOn "\n").filter (!·.isEmpty)
  let outputs := ((← IO.FS.readFile results).splitOn "\n").filter (!·.isEmpty)
  unless inputs.length == outputs.length && inputs.length == 2000 do
    IO.eprintln s!"fidelity: expected 2000 cases/results, got {inputs.length}/{outputs.length}"
    return 2
  let fn := if task == "lz4-c" then "LZ4_decompress_safe" else "lz4_decompress"
  let artifact := s!"(module $artifact binary {quotedBytes (← IO.FS.readBinFile wasm)})"
  let register := "(register \"artifact\" $artifact)"
  let mut lines := if task == "lz4-c" then #[artifact, register] else #[]
  for (input, output) in inputs.zip outputs do
    -- T2 reuses one instance; T3's reference creates a fresh instance for each case.
    if task == "lz4-rust" then lines := lines.push artifact |>.push register
    let ins := (input.splitOn " ").filter (!·.isEmpty)
    let outs := (output.splitOn " ").filter (!·.isEmpty)
    let (src, dst, size, cap, data) ← if task == "lz4-c" then do
      let [_, s, d, n, c, h] := ins | throw <| IO.userError "invalid T2 case"
      pure (← number s, ← number d, ← number n, ← number c, ← bytes h)
    else do
      let [c, h] := ins | throw <| IO.userError "invalid T3 case"
      let b ← bytes h
      pure (131072, 1150000, b.size, ← number c, b)
    unless data.size == size && src >= 131072 && src + size <= 2097152 &&
        dst >= 131072 && dst + cap <= 2097152 do
      throw <| IO.userError "case outside the caller-memory domain"
    let ret := outs.headD ""
    let r ← match ret.toInt? with
      | some n => pure n
      | none => throw <| IO.userError s!"invalid model result: {output}"
    let (lo, expected) ← if task == "lz4-c" then do
      match outs with
      | [_, "none"] => pure (0, ByteArray.empty)
      | [_, a, _, h] => pure (← number a, ← bytes h)
      | _ => throw <| IO.userError "invalid T2 model result"
    else pure (0, ← bytes (outs[1]?.getD "-"))
    if task == "lz4-rust" && r >= 0 then
      unless expected.size == r.toNat && r.toNat <= cap do
        throw <| IO.userError "model length/content mismatch"
    if task == "lz4-c" && !expected.isEmpty then
      unless lo >= 131072 && lo + expected.size <= 2097152 do
        throw <| IO.userError "model write outside the caller-memory domain"
    let begin := if task == "lz4-c" then 131072 else dst
    let count := if task == "lz4-c" then 2097152 - 131072 else r.toNat
    let expectedBase := if task == "lz4-c" then begin else 0
    let initExpected := if task == "lz4-c" then
      s!"(memory.fill $expected (i32.const 131072) (i32.const 165) (i32.const 1966080))
      (memory.init $expected $input (i32.const {src}) (i32.const 0) (i32.const {size}))" else ""
    let initActual := if task == "lz4-c" then
      "(memory.fill $actual (i32.const 131072) (i32.const 165) (i32.const 1966080))"
    else
      "(block $filled (loop $fill
        (br_if $filled (i32.ge_u (local.get $k) (i32.const 1966080)))
        (i32.store8 $actual (i32.add (i32.const 131072) (local.get $k))
          (i32.add (i32.mul (local.get $k) (i32.const 37)) (i32.const 11)))
        (local.set $k (i32.add (local.get $k) (i32.const 1))) (br $fill)))"
    lines := lines.push s!"(module $case
      (import \"artifact\" \"memory\" (memory $actual 0))
      (import \"artifact\" \"{fn}\" (func $decode (param i32 i32 i32 i32) (result i32)))
      (memory $expected 32)
      (data $input {quotedBytes data})
      (data $output {quotedBytes expected})
      (func (export \"run\") (result i32) (local $k i32)
        {initActual}
        (memory.init $actual $input (i32.const {src}) (i32.const 0) (i32.const {size}))
        {initExpected}
        (memory.init $expected $output (i32.const {lo}) (i32.const 0) (i32.const {expected.size}))
        (call $decode (i32.const {src}) (i32.const {dst}) (i32.const {size}) (i32.const {cap})))
      (func (export \"equal\") (result i32) (local $i i32)
        (block $done (loop $next
          (br_if $done (i32.ge_u (local.get $i) (i32.const {count})))
          (if (i32.ne
            (i32.load8_u $actual (i32.add (i32.const {begin}) (local.get $i)))
            (i32.load8_u $expected (i32.add (i32.const {expectedBase}) (local.get $i))))
            (then (return (i32.const 0))))
          (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $next))) (i32.const 1)))"
    lines := lines.push s!"(assert_return (invoke $case \"run\") (i32.const {r}))"
    if task == "lz4-c" || r >= 0 then
      lines := lines.push "(assert_return (invoke $case \"equal\") (i32.const 1))"
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"fidelity: {inputs.length} cases → {out}"
  return 0
