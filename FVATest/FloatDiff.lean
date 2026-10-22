import FVATest.Numeric

/-!
# Float differential test (U3 evidence E3)

Writes WAST scripts whose expected results are the verified float implementation's, on
fixed-seed operands biased to boundaries (zeros, infinities, NaNs, subnormals, the normal range
edges, values near 1, operands sharing an exponent for cancellation and rounding ties);
`wasmtime wast` checks them. A NaN result is expected as its spec class: `nan:canonical` when
every NaN operand is canonical, else `nan:arithmetic`.
-/

namespace FVA.Test.FloatDiff

open FVA.Wasm FVA.Wasm.Num FVA.Test.Numeric

/-- splitmix64 state. -/
abbrev Gen := StateM UInt64

/-- The next 64 random bits. -/
def next : Gen UInt64 := do
  let s := (← get) + 0x9E3779B97F4A7C15
  set s
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  return z ^^^ (z >>> 31)

/-- Run a generator step inside the script writer. -/
def lift {α : Type} (g : Gen α) : StateT UInt64 IO α := fun s => pure (g.run s)

/-- A random natural below `n` (`n > 0`). -/
def below (n : Nat) : Gen Nat := do
  let a ← next
  let b ← next
  return (a.toNat * 2 ^ 64 + b.toNat) % n

/-- Format facts of a width: the format, its bit width, a WAST type name. -/
def fmt : Width → FloatFormat × Nat × String
  | .w32 => (f32fmt, 32, "f32")
  | .w64 => (f64fmt, 64, "f64")

/-- Boundary bit patterns of a format, positive and negative. -/
def specials (F : FloatFormat) : List Nat :=
  let bias := 2 ^ (F.E - 1) - 1
  let inf := (2 ^ F.E - 1) * 2 ^ F.M
  let pos := [0, 1, 2, 2 ^ F.M - 1, 2 ^ F.M, 2 ^ F.M + 1, inf - 1, inf - 2, inf, inf + F.canon,
    inf + F.canon + 1, inf + 1, inf + 2 ^ F.M - 1, bias * 2 ^ F.M, bias * 2 ^ F.M + 1,
    bias * 2 ^ F.M - 1, (bias + 1) * 2 ^ F.M, (bias - 1) * 2 ^ F.M,
    (bias - 1) * 2 ^ F.M + 2 ^ (F.M - 1),
    (bias + F.M) * 2 ^ F.M, (bias + F.M + 1) * 2 ^ F.M - 1]
  pos ++ pos.map (· + 2 ^ (F.E + F.M))

/-- A boundary-biased operand; `near` = another operand whose exponent it may share. -/
def operand (F : FloatFormat) (near : Option Nat) : Gen Nat := do
  let sign := (← below 2) * 2 ^ (F.E + F.M)
  let bias := 2 ^ (F.E - 1) - 1
  match ← below 10 with
  | 0 | 1 => let s := specials F; return s[← below s.length]!
  | 2 | 3 => return sign + (← below (2 ^ F.M))
  | 4 | 5 => return ← below (2 ^ (1 + F.E + F.M))
  | 6 | 7 => return sign + (bias - 30 + (← below 61)) * 2 ^ F.M + (← below (2 ^ F.M))
  | _ => match near with
    | some b =>
      -- a quarter of these are ±b exactly (cancellation, equality)
      if (← below 4) = 0 then return b % 2 ^ (F.E + F.M) + sign
      let e := b / 2 ^ F.M % 2 ^ F.E
      let up ← below 2
      let k ← below (F.M + 4)
      let e' := if up = 0 then min (2 ^ F.E - 2) (e + k) else e - min e k
      let low := ← below (2 ^ (← below (F.M + 1)))
      return sign + e' * 2 ^ F.M + (b % 2 ^ F.M ^^^ low)
    | none => return ← below (2 ^ (1 + F.E + F.M))

/-- `n` as exactly `w` hex digits. -/
def hex (n w : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- An exact WAST float literal of a bit pattern. -/
def lit (F : FloatFormat) (b : Nat) : String :=
  let sg := if b / 2 ^ (F.E + F.M) % 2 = 1 then "-" else ""
  let e := b / 2 ^ F.M % 2 ^ F.E
  let m := b % 2 ^ F.M
  let bias := 2 ^ (F.E - 1) - 1
  -- hex digits hold the significand left-aligned: 23 bits → 6 digits, 52 bits → 13 digits
  let digits := (F.M + 3) / 4
  let frac := hex (m * 2 ^ (4 * digits - F.M)) digits
  if e = 2 ^ F.E - 1 then
    if m = 0 then sg ++ "inf" else sg ++ "nan:0x" ++ hex m 1
  else if e = 0 then s!"{sg}0x0.{frac}p-{bias - 1}"
  else if e ≥ bias then s!"{sg}0x1.{frac}p+{e - bias}"
  else s!"{sg}0x1.{frac}p-{bias - e}"

/-- A NaN payload of a bit pattern (`none` for other values). -/
def payload (F : FloatFormat) (b : Nat) : Option Nat :=
  if b / 2 ^ F.M % 2 ^ F.E = 2 ^ F.E - 1 ∧ b % 2 ^ F.M ≠ 0 then some (b % 2 ^ F.M) else none

/-- The expected-result form of a float result: exact, or the spec's NaN class given the NaN
operands `ins` (with their formats). `signOnly` = a sign-bit operator (`abs`, `neg`,
`copysign`), whose NaN results keep their payload exactly. -/
def expect (F : FloatFormat) (ty : String) (r : Nat) (ins : List (FloatFormat × Nat))
    (signOnly := false) : String :=
  match payload F r with
  | none => s!"({ty}.const {lit F r})"
  | some _ =>
    if signOnly then s!"({ty}.const {lit F r})" else
    let canon := ins.all fun (G, b) => match payload G b with
      | some p => p == G.canon
      | none => true
    if canon then s!"({ty}.const nan:canonical)" else s!"({ty}.const nan:arithmetic)"

/-- A module function exporting one instruction over its parameters. -/
def func (name params result body : String) : String :=
  s!"  (func (export \"{name}\") (param {params}) (result {result}) ({body}))"

/-- An `assert_return` of an invocation. -/
def ret (name args expected : String) : String :=
  s!"(assert_return (invoke \"{name}\" {args}) {expected})"

/-- Float unary ops by name. -/
def unops : List (String × FUnOp) :=
  [("abs", .abs), ("neg", .neg), ("sqrt", .sqrt), ("ceil", .ceil), ("floor", .floor),
    ("trunc", .trunc), ("nearest", .nearest)]

/-- Float binary ops by name. -/
def binops : List (String × FBinOp) :=
  [("add", .add), ("sub", .sub), ("mul", .mul), ("div", .div), ("min", .min), ("max", .max),
    ("copysign", .copysign)]

/-- Float comparisons by name. -/
def relops : List (String × FRelOp) :=
  [("eq", .eq), ("ne", .ne), ("lt", .lt), ("gt", .gt), ("le", .le), ("ge", .ge)]

/-- Integer operands for conversions: boundary values, then random bits. -/
def intOperand (N : Nat) : Gen Nat := do
  if (← below 4) = 0 then
    let s := [0, 1, 2, 2 ^ (N - 1) - 1, 2 ^ (N - 1), 2 ^ (N - 1) + 1, 2 ^ N - 1, 2 ^ N - 2,
      2 ^ 24 - 1, 2 ^ 24 + 1, 2 ^ 53 - 1, 2 ^ 53 + 1, 2 ^ 63 - 1].map (· % 2 ^ N)
    return s[← below s.length]!
  else
    let k ← below (N + 1)
    return ← below (2 ^ k)

/-- Case-matrix representatives: one operand per class a spec bullet distinguishes (zeros,
subnormals, the normal-range edges, 1/4, 1/2, 3/4, 1, 1 + ulp, 3/2, 5/2, 3, half an ulp of 1
(a tie with 1), the integer-conversion limits 2^31, 2^32, 2^63, 2^64, the largest finite,
infinity, canonical/arithmetic/signaling NaNs), both signs. -/
def reps (F : FloatFormat) : List Nat :=
  let bias := 2 ^ (F.E - 1) - 1
  let p2 (k : Nat) := (bias + k) * 2 ^ F.M
  let inf := (2 ^ F.E - 1) * 2 ^ F.M
  let pos := [0, 1, 2 ^ F.M - 1, 2 ^ F.M, (bias - 2) * 2 ^ F.M, (bias - 1) * 2 ^ F.M,
    (bias - 1) * 2 ^ F.M + 2 ^ (F.M - 1), p2 0, p2 0 + 1, p2 0 + 2 ^ (F.M - 1),
    p2 1 + 2 ^ (F.M - 2), p2 1 + 2 ^ (F.M - 1), (bias - F.M - 1) * 2 ^ F.M, p2 31, p2 32, p2 63,
    p2 64, inf - 1, inf, inf + F.canon, inf + F.canon + 1, inf + 1]
  pos ++ pos.map (· + 2 ^ (F.E + F.M))

/-- Integer case-matrix representatives of width `N`. -/
def intReps (N : Nat) : List Nat :=
  [0, 1, 2, 2 ^ (N - 1) - 1, 2 ^ (N - 1), 2 ^ (N - 1) + 1, 2 ^ N - 1, 2 ^ N - 2, 2 ^ 24 + 1,
    2 ^ 53 + 1, 2 ^ 63 - 1].map (· % 2 ^ N)

/-- Assertions for float width `w`, written to `h`. -/
structure Emit where
  /-- The width's format, WAST type, the other width's format + type, the promote/demote name. -/
  F : FloatFormat
  ty : String
  G : FloatFormat
  ty2 : String
  cvt : String
  /-- Output. -/
  h : IO.FS.Handle

namespace Emit

/-- A float operand of the width. -/
def toF (x : Emit) (b : Nat) : FVal := ofBits x.F (BitVec.ofNat x.F.N b)
/-- A float result's bits. -/
def bitsF (x : Emit) (z : FVal) : Nat := (fbits x.F z).toNat
/-- A float literal argument. -/
def arg (x : Emit) (b : Nat) : String := s!"({x.ty}.const {lit x.F b})"

/-- One binary-op case. -/
def bin (x : Emit) (n : String) (op : FBinOp) (a b : Nat) : IO Unit := do
  let r := x.bitsF (fun2 x.F op (x.toF a) (x.toF b))
  let e := expect x.F x.ty r [(x.F, a), (x.F, b)] (signOnly := n == "copysign")
  x.h.putStrLn (ret n s!"{x.arg a} {x.arg b}" e)

/-- One unary-op case. -/
def un (x : Emit) (n : String) (op : FUnOp) (a : Nat) : IO Unit := do
  let r := x.bitsF (fun1 x.F op (x.toF a))
  let e := expect x.F x.ty r [(x.F, a)] (signOnly := n == "abs" || n == "neg")
  x.h.putStrLn (ret n (x.arg a) e)

/-- One comparison case. -/
def rel (x : Emit) (n : String) (op : FRelOp) (a b : Nat) : IO Unit :=
  let r := (frel x.F op (x.toF a) (x.toF b)).toNat
  x.h.putStrLn (ret n s!"{x.arg a} {x.arg b}" s!"(i32.const {r})")

/-- One `trunc` and one `trunc_sat` case into integer type `it` of width `M`. -/
def trunc (x : Emit) (it : String) (M : Nat) (sx : String) (sxv : Sx) (a : Nat) : IO Unit := do
  let call := s!"(invoke \"{it}.trunc_{x.ty}_{sx}\" {x.arg a})"
  match ftruncSx x.F M sxv (x.toF a) with
  | some v => x.h.putStrLn s!"(assert_return {call} ({it}.const {v.toNat}))"
  | none =>
    let msg :=
      if (payload x.F a).isSome then "invalid conversion to integer" else "integer overflow"
    x.h.putStrLn s!"(assert_trap {call} \"{msg}\")"
  let v := ftruncSatSx x.F M sxv (x.toF a)
  x.h.putStrLn (ret s!"{it}.trunc_sat_{x.ty}_{sx}" (x.arg a) s!"({it}.const {v.toNat})")

/-- One `convert` case from integer type `it` of width `M`. -/
def convert (x : Emit) (it : String) (M : Nat) (sx : String) (sxv : Sx) (i : Nat) : IO Unit := do
  let r := x.bitsF (fconvertSx x.F sxv (BitVec.ofNat M i))
  x.h.putStrLn (ret s!"{x.ty}.convert_{it}_{sx}" s!"({it}.const {i})" (expect x.F x.ty r []))

/-- One promote (f32) or demote (f64) case. -/
def cvtCase (x : Emit) (a : Nat) : IO Unit := do
  let r := if x.ty == "f32" then (fbits f64fmt (Impl.fpromote (x.toF a))).toNat
    else (fbits f32fmt (Impl.fdemote (x.toF a))).toNat
  x.h.putStrLn (ret x.cvt (x.arg a) (expect x.G x.ty2 r [(x.F, a)]))

end Emit

/-- Write the module + assertions of one float width to `h`: the case matrix (every op on every
pair of representatives), then `nBin` random cases per binary op and `nOther` per other op. -/
def script (w : Width) (nBin nOther : Nat) (h : IO.FS.Handle) : StateT UInt64 IO Unit := do
  let (F, _, ty) := fmt w
  let (G, _, ty2) := fmt (match w with | .w32 => .w64 | .w64 => .w32)
  let cvt := if w == .w32 then s!"{ty2}.promote_{ty}" else s!"{ty2}.demote_{ty}"
  let x : Emit := { F, ty, G, ty2, cvt, h }
  -- module: every op over parameters, exported under its instruction name
  h.putStrLn "(module"
  for (n, _) in unops do
    h.putStrLn (func n ty ty s!"{ty}.{n} (local.get 0)")
  for (n, _) in binops do
    h.putStrLn (func n s!"{ty} {ty}" ty s!"{ty}.{n} (local.get 0) (local.get 1)")
  for (n, _) in relops do
    h.putStrLn (func n s!"{ty} {ty}" "i32" s!"{ty}.{n} (local.get 0) (local.get 1)")
  for it in ["i32", "i64"] do
    for sx in ["s", "u"] do
      for i in [s!"{it}.trunc_{ty}_{sx}", s!"{it}.trunc_sat_{ty}_{sx}"] do
        h.putStrLn (func i ty it s!"{i} (local.get 0)")
      let c := s!"{ty}.convert_{it}_{sx}"
      h.putStrLn (func c it ty s!"{c} (local.get 0)")
  h.putStrLn (func cvt ty ty2 s!"{cvt} (local.get 0)" ++ ")")
  let ints := [("i32", 32), ("i64", 64)]
  let sxs := [("s", Sx.s), ("u", Sx.u)]
  -- case matrix
  for (n, op) in binops do
    for a in reps F do
      for b in reps F do x.bin n op a b
  for (n, op) in unops do
    for a in reps F do x.un n op a
  for (n, op) in relops do
    for a in reps F do
      for b in reps F do x.rel n op a b
  for (it, M) in ints do
    for (sx, sxv) in sxs do
      for a in reps F do x.trunc it M sx sxv a
      for i in intReps M do x.convert it M sx sxv i
  for a in reps F do x.cvtCase a
  -- random cases
  for (n, op) in binops do
    for _ in [0:nBin] do
      let a ← lift (operand F none)
      let b ← lift (operand F (some a))
      x.bin n op a b
  for (n, op) in unops do
    for _ in [0:nOther] do x.un n op (← lift (operand F none))
  for (n, op) in relops do
    for _ in [0:nOther] do
      let a ← lift (operand F none)
      let b ← lift (operand F (some a))
      x.rel n op a b
  for (it, M) in ints do
    for (sx, sxv) in sxs do
      for _ in [0:nOther] do
        x.trunc it M sx sxv (← lift (operand F none))
        x.convert it M sx sxv (← lift (intOperand M))
  for _ in [0:nOther] do x.cvtCase (← lift (operand F none))

/-- Write `f32.wast` and `f64.wast` into `dir` from `seed`. -/
def run (dir : System.FilePath) (seed : UInt64) (nBin nOther : Nat) : IO Unit := do
  let mut st := seed
  for w in [Width.w32, Width.w64] do
    let (_, _, ty) := fmt w
    let h ← IO.FS.Handle.mk (dir / s!"{ty}.wast") .write
    let ((), st') ← (script w nBin nOther h).run st
    st := st'

end FVA.Test.FloatDiff
