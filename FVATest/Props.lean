import FVA.Tool.Encode
import FVA.Tool.Lift
import FVA.Tool.Pack
import FVA.Tool.Wast
import FVA.Tool.Explain
import FVA.Trust.Lines
import FVA.Trust.Olean

/-!
# Fixed-seed property tests (D69)

Contract predicates of unproven code over generated inputs (splitmix64, `FVA.Tool.Wast.Gen`),
case sizes ascending so the first counterexample is a small one. Proven predicates need none
(`.claude/rules/fva-gate.md`); the compiled code's agreement with proven definitions stays with
the official-suite + difftest runs.

- encoder: `decode (encode m) = m` on generated modules of the decoder's profile (compared by
  `fva lift`'s rendering, which the kernel's `decode_eq` check holds to the module exactly);
- explain renamer: `restore (apply src) = src`;
- `codeLines`: unchanged by inserted blank and comment lines, + 1 per inserted code line;
- `.olean` pin digest: `FVA.Trust.oleanDigests` = `scripts/make-olean-pins --digest` on
  generated part triples (absent parts included).

`FVA_PROPS_SEED` / `FVA_PROPS_SCALE` (case-count multiplier) explore beyond the gate's fixed run.
-/

namespace FVA.Test.Props

open FVA.Wasm FVA.Wasm.Binary FVA.Tool.Wast

/-- An element of `xs` (`d` when empty). -/
def pick {α : Type} (xs : List α) (d : α) : Gen α := do
  return xs[← below xs.length]?.getD d

/-- Up to `n` draws of `g`. -/
def listOf {α : Type} (n : Nat) (g : Gen α) : Gen (List α) := do
  let k ← below (n + 1)
  let mut out := []
  for _ in [0:k] do out := (← g) :: out
  return out.reverse

/-! ## Encoder round trip -/

/-- A `u32`, biased to LEB length boundaries. -/
def u32 : Gen Nat := do
  match ← below 4 with
  | 0 => pick [0, 1, 63, 64, 127, 128, 16383, 16384, 2 ^ 21 - 1, 2 ^ 21, 2 ^ 28 - 1, 2 ^ 28,
      2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1] 0
  | 1 => below (2 ^ 32)
  | _ => below 200

/-- Constant bits of width `w`, biased to sign and LEB boundaries. -/
def bits (w : Width) : Gen Nat := do
  let n := match w with | .w32 => 32 | .w64 => 64
  if (← below 3) = 0 then
    pick [0, 1, 63, 64, 2 ^ (n - 1) - 1, 2 ^ (n - 1), 2 ^ n - 1, 2 ^ n - 64, 2 ^ n - 65] 0
  else below (2 ^ n)

def width : Gen Width := pick [.w32, .w64] .w32
def refType : Gen RefType := pick [.funcref, .externref] .funcref
def valType : Gen ValType :=
  pick [.num .i32, .num .i64, .num .f32, .num .f64, .ref .funcref, .ref .externref] (.num .i32)
def limits : Gen Limits := do
  return ⟨← u32, ← if (← below 2) = 0 then pure none else some <$> u32⟩
def blockType : Gen BlockType := do
  match ← below 3 with
  | 0 => return .empty
  | 1 => return .val (← valType)
  | _ => return .idx (← u32)

private instance : Inhabited Instr := ⟨.nop⟩

mutual
/-- An instruction: every opcode table of the binary spec, structured ones to depth `d`. -/
partial def instr (s d : Nat) : Gen Instr := do
  match ← below 13 with
  | 0 | 1 => pick (plainOps.map (·.2)) .nop
  | 2 => pick (fcPlainOps.map (·.2)) .nop
  | 3 => return (← pick (memOps.map (·.2)) fun (_ : MemArg) => Instr.nop) ⟨← u32, ← u32⟩
  | 4 => return (← pick (idxOps.map (·.2)) fun (_ : Nat) => Instr.nop) (← u32)
  | 5 => return (← pick (fcIdxOps.map (·.2)) fun (_ : Nat) => Instr.nop) (← u32)
  | 6 => let w ← width; return .iconst w (← bits w)
  | 7 => let w ← width; return .fconst w (← bits w)
  | 8 => return .brTable (← listOf s u32) (← u32)
  | 9 => pick [.memorySize, .memoryGrow, .memoryFill, .memoryCopy] .nop
  | 10 => match ← below 6 with
    | 0 => return .memoryInit (← u32)
    | 1 => return .tableInit (← u32) (← u32)
    | 2 => return .tableCopy (← u32) (← u32)
    | 3 => return .callIndirect (← u32) (← u32)
    | 4 => return .select (some [← valType])
    | _ => return .refNull (← refType)
  | _ =>
    if d = 0 then return .nop
    let bt ← blockType
    match ← below 3 with
    | 0 => return .block bt (← seq s (d - 1))
    | 1 => return .loop bt (← seq s (d - 1))
    | _ => return .if_ bt (← seq s (d - 1)) (← seq s (d - 1))
/-- An instruction sequence. -/
partial def seq (s d : Nat) : Gen (List Instr) := listOf s (instr s d)
end

/-- A name: ASCII, multi-byte UTF-8 and NUL. -/
def name : Gen String := do
  let cs ← listOf 6 (pick ['a', 'Z', '_', '0', ' ', 'é', 'Ω', '中', '😀', '\x00'] 'a')
  return String.ofList cs

/-- A constant expression (the decoder accepts any instruction sequence). -/
def constExpr : Gen Expr := do
  match ← below 3 with
  | 0 => return [.refFunc (← u32)]
  | 1 => return [.refNull (← refType)]
  | _ => return [.globalGet (← u32)]

/-- A module of size `s` (list lengths ≤ `s`). -/
def module (s : Nat) : Gen Module := do
  let types ← listOf s do return ⟨← listOf 4 valType, ← listOf 2 valType⟩
  let imports ← listOf s do
    let desc ← match ← below 4 with
      | 0 => pure (ImportDesc.func (← u32))
      | 1 => pure (.table ⟨← limits, ← refType⟩)
      | 2 => pure (.mem (← limits))
      | _ => pure (.global ⟨← pick [.const, .var] .const, ← valType⟩)
    return ⟨← name, ← name, desc⟩
  let funcs ← listOf s do
    return { type := ← u32, locals := ← listOf 3 (do return (← below 70, ← valType)),
             body := ← seq s 2 }
  let tables ← listOf s do return ⟨← limits, ← refType⟩
  let mems ← listOf 2 limits
  let globals ← listOf s do
    return ⟨⟨← pick [.const, .var] .const, ← valType⟩, ← seq 2 0⟩
  let exports ← listOf s do
    let desc ← match ← below 4 with
      | 0 => pure (ExportDesc.func (← u32)) | 1 => pure (.table (← u32))
      | 2 => pure (.mem (← u32)) | _ => pure (.global (← u32))
    return ⟨← name, desc⟩
  let start ← if (← below 2) = 0 then pure none else some <$> u32
  let elems ← listOf s do
    let mode ← match ← below 3 with
      | 0 => pure ElemMode.passive
      | 1 => pure (.active (← pick [0, 0, 1, ← u32] 0) (← seq 2 0))
      | _ => pure .declarative
    return ⟨← refType, ← listOf s constExpr, mode⟩
  let datas ← listOf s do
    let mode ← if (← below 2) = 0 then pure DataMode.passive
      else pure (.active (← pick [0, 0, ← u32] 0) (← seq 2 0))
    return ⟨← listOf (4 * s) (do return (← below 256).toUInt8), mode⟩
  return { types, imports, funcs, tables, mems, globals, exports, start, elems, datas }

/-- The module as `fva lift` renders it. -/
def render (m : Module) : String := FVA.Tool.Lift.file "P" .empty m

/-- `decode (encode m) = m` for `n` modules, sizes 1, 1, …, ascending. -/
def encoderRoundTrip (n : Nat) (seed : UInt64) : Except String Unit := do
  let mut st := seed
  for i in [0:n] do
    let (m, st') := (module (1 + i / 25)).run st
    st := st'
    let bs : ByteArray := ⟨(FVA.Tool.Encode.module m).toArray⟩
    match FVA.Wasm.Decode.decode (FVA.Tool.packBytes bs) bs.size with
    | .ok m' =>
      unless render m' == render m do
        throw s!"case {i}: decode (encode m) ≠ m\nm = {render m}\ndecoded = {render m'}"
    | .error e => throw s!"case {i}: the encoding does not decode ({repr e})\nm = {render m}"

/-! ## Explain renamer round trip -/

open FVA.Tool.Explain in
/-- `restore (apply src) = src` for generated claims, declared names and sources (neutral-name
words, strings, `«…»` names, projections and primed identifiers included); also the count of
cases where `apply` renamed something, so a vacuous run shows. -/
def renamerRoundTrip (n : Nat) (seed : UInt64) : Except String Nat := do
  let comps := ["clamp", "gcd", "x", "α", "get?", "f'", "helper", "Toy", "Ex", "claim_1", "name_2"]
  let nameOf : Gen Lean.Name := do
    let cs ← listOf 2 (pick comps "x")
    return (cs ++ [← pick comps "x"]).foldl Lean.Name.str .anonymous
  let mut st := seed
  let mut renamed := 0
  for i in [0:n] do
    let gen : Gen (List Lean.Name × List Lean.Name × String) := do
      let claims ← listOf 3 nameOf
      let declared ← listOf 4 nameOf
      let names := claims ++ declared
      let tok : Gen String := do
        match ← below 9 with
        | 0 | 1 =>
          let cs : List String := (← pick names `x).components.map toString
          return ".".intercalate (cs.drop (← below cs.length))
        | 2 => pick ["claim_1", "claim_2", "name_3", "name_10", "x", "h'", "y₁", "Nat.gcd"] "x"
        | 3 => return s!"x.{← pick comps "x"}"
        | 4 => return s!"\"{← pick comps "x"} claim_2 \\\" name_1\""
        | 5 => return s!"«{← pick comps "x"}»"
        | 6 => return s!"'{← pick comps "x"}'"
        | _ => pick [" ", "\n", "(", ")", " : ", ".", ", ", " → ", "∀ ", "1.5", "_"] " "
      let toks ← listOf 12 tok
      return (claims, declared, String.join toks)
    let ((claims, declared, src), st') := gen.run st
    st := st'
    let rn := Renamer.of claims declared (Renamer.words src)
    let out := rn.apply src
    if out != src then renamed := renamed + 1
    unless rn.restore out == src do
      throw s!"case {i}: restore (apply src) ≠ src\nclaims = {claims}, declared = {declared}\n\
        src = {repr src}\napply = {repr out}\nrestore = {repr (rn.restore out)}"
  return renamed

/-! ## Code lines (D11) -/

/-- Lines holding code alone (no unclosed string or comment). -/
def codePool : List String :=
  ["def x := 1", "theorem t : True := trivial", "  simp", "#check Nat", "x",
   "def s := \"--x\"", "def c := '\"' -- quote char", "def «a--b» := 1", "/- c -/ def y := 2",
   "  ∑ i ∈ s, f i ≤ 3", "def m := \"a /- b\""]

/-- Line groups holding no code. -/
def emptyPool : List String :=
  ["", "   ", "-- c", "  -- indented", "/- block -/", "/- multi\nline -/", "/-- doc -/",
   "/-! module doc\n  def notCode := 1\n-/", "/- /- nested -/ still -/"]

/-- `codeLines` unchanged by inserted blank + comment lines, + 1 per inserted code line. -/
def codeLinesMetamorphic (env : Lean.Environment) (n : Nat) (seed : UInt64) :
    Except String Unit := do
  let mut st := seed
  for i in [0:n] do
    let gen : Gen (List String × List String × Nat) := do
      let base ← listOf (2 + i / 50) (pick codePool "x")
      let mut grown := base
      let mut added := 0
      let k ← below 4
      for _ in [0:k] do
        let at_ ← below (grown.length + 1)
        let line ← if (← below 3) = 0 then pick codePool "x" else pick emptyPool ""
        if codePool.contains line then added := added + 1
        grown := grown.take at_ ++ [line] ++ grown.drop at_
      return (base, grown, added)
    let ((base, grown, added), st') := gen.run st
    st := st'
    let a := FVA.Trust.codeLines env ("\n".intercalate base)
    let b := FVA.Trust.codeLines env ("\n".intercalate grown)
    unless b == a + added do
      throw s!"case {i}: codeLines {repr ("\n".intercalate grown)} = {b}, want {a} + {added} \
        (base {repr ("\n".intercalate base)})"

/-! ## `.olean` pin digest: Lean = bash -/

/-- `oleanDigests` and `scripts/make-olean-pins --digest` agree on `n` generated part triples
(each part present with probability 3/4, the `.olean` included; random contents). -/
def digestsAgree (n : Nat) (seed : UInt64) : IO (Except String Unit) :=
  IO.FS.withTempDir fun dir => do
    let mut st := seed
    let mut list := ""
    let mut oleans := #[]
    for i in [0:n] do
      let o := dir / s!"M{i}.olean"
      oleans := oleans.push o
      list := list ++ s!"{dir}\tM{i}.olean\n"
      for p in FVA.Trust.oleanParts o do
        let ((present, bytes), st') := (do
          let present := (← below 4) != 0
          let bytes ← listOf 40 (do return (← below 256).toUInt8)
          return (present, bytes) : Gen _).run st
        st := st'
        if present then IO.FS.writeBinFile p ⟨bytes.toArray⟩
    IO.FS.writeFile (dir / "list") list
    let r ← IO.Process.output
      { cmd := "scripts/make-olean-pins", args := #["--digest", (dir / "list").toString] }
    if r.exitCode != 0 then
      return .error s!"make-olean-pins --digest rc {r.exitCode}: {r.stderr}"
    let bash : Std.HashMap String String := (r.stdout.splitOn "\n").foldl (init := {})
      fun m l => match l.splitOn "\t" with | [k, v] => m.insert k v | _ => m
    let lean ← FVA.Trust.oleanDigests oleans
    for (o, i) in oleans.zipIdx do
      let b := bash.get? s!"M{i}"
      let l := lean.get? o.toString
      unless b.isSome && b == l do
        let parts := (FVA.Trust.oleanParts o).toList.map fun p => (p.fileName.getD "", p)
        let present ← parts.filterM fun (_, p) => p.pathExists
        return .error s!"M{i} (parts present: {present.map (·.1)}): bash {b}, Lean {l}"
    return .ok ()

/-- Every property at the fixed seed; rc 1 on the first counterexample of each. -/
def run : IO UInt32 := do
  let seed := ((← IO.getEnv "FVA_PROPS_SEED").bind String.toNat?).getD 20261104 |>.toUInt64
  let scale := ((← IO.getEnv "FVA_PROPS_SCALE").bind String.toNat?).getD 1
  let env ← Lean.mkEmptyEnvironment
  let mut bad := false
  let report (label : String) (r : Except String String) : IO Bool := do
    match r with
    | .ok msg => IO.println s!"props: {label} {msg}"; return false
    | .error e => IO.eprintln s!"props: {label} FAILED (seed {seed})\n{e}"; return true
  bad := bad || (← report "encoder round trip"
    ((encoderRoundTrip (300 * scale) seed).map fun _ => s!"{300 * scale} modules ok"))
  bad := bad || (← report "renamer round trip"
    ((renamerRoundTrip (500 * scale) seed).map fun k => s!"{500 * scale} sources ok ({k} renamed)"))
  bad := bad || (← report "codeLines metamorphic"
    ((codeLinesMetamorphic env (300 * scale) seed).map fun _ => s!"{300 * scale} sources ok"))
  bad := bad || (← report "olean digest Lean = bash"
    ((← digestsAgree (60 * scale) seed).map fun _ => s!"{60 * scale} triples ok"))
  return if bad then 1 else 0

end FVA.Test.Props
