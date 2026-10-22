import FVA.Spec.Exec.Runtime
import FVA.Spec.Numerics.Float

/-!
# Numeric instructions on values (reviewed spec)

The results of each numeric instruction of §4.4.1 on its operand values, taken from the reviewed
operators of `FVA.Spec.Numerics`: `some v` = the value pushed, `none` = a trap. Integer operators
have one result; float operators may have several (NaN results are sets). An instruction applied
to operands of the wrong number or type has no result (the configuration is stuck; validation
excludes it).
-/

namespace FVA.Wasm.Exec

open FVA.Wasm FVA.Wasm.Num

/-- Integer unary operators. -/
def iunop {N : Nat} : IUnOp → BitVec N → BitVec N
  | .clz, a => iclz a
  | .ctz, a => ictz a
  | .popcnt, a => ipopcnt a
  | .extend8s, a => iextendS 8 a
  | .extend16s, a => iextendS 16 a
  | .extend32s, a => iextendS 32 a

/-- Integer binary operators; `none` = trap. -/
def ibinop {N : Nat} : IBinOp → BitVec N → BitVec N → Option (BitVec N)
  | .add, a, b => some (iadd a b)
  | .sub, a, b => some (isub a b)
  | .mul, a, b => some (imul a b)
  | .div .u, a, b => idivU a b
  | .div .s, a, b => idivS a b
  | .rem .u, a, b => iremU a b
  | .rem .s, a, b => iremS a b
  | .and, a, b => some (iand a b)
  | .or, a, b => some (ior a b)
  | .xor, a, b => some (ixor a b)
  | .shl, a, b => some (ishl a b)
  | .shr .u, a, b => some (ishrU a b)
  | .shr .s, a, b => some (ishrS a b)
  | .rotl, a, b => some (irotl a b)
  | .rotr, a, b => some (irotr a b)

/-- Integer comparisons. -/
def irelop {N : Nat} : IRelOp → BitVec N → BitVec N → BitVec 32
  | .eq, a, b => ieq a b
  | .ne, a, b => ine a b
  | .lt .u, a, b => iltU a b
  | .lt .s, a, b => iltS a b
  | .gt .u, a, b => igtU a b
  | .gt .s, a, b => igtS a b
  | .le .u, a, b => ileU a b
  | .le .s, a, b => ileS a b
  | .ge .u, a, b => igeU a b
  | .ge .s, a, b => igeS a b

/-- Float unary operators on values. -/
noncomputable def funop (F : FloatFormat) : FUnOp → FVal → Set FVal
  | .abs, z => {fabs z}
  | .neg, z => {fneg z}
  | .sqrt, z => fsqrt F z
  | .ceil, z => fceil F z
  | .floor, z => ffloor F z
  | .trunc, z => ftrunc F z
  | .nearest, z => fnearest F z

/-- Float binary operators on values. -/
noncomputable def fbinop (F : FloatFormat) : FBinOp → FVal → FVal → Set FVal
  | .add, a, b => fadd F a b
  | .sub, a, b => fsub F a b
  | .mul, a, b => fmul F a b
  | .div, a, b => fdiv F a b
  | .min, a, b => fmin F a b
  | .max, a, b => fmax F a b
  | .copysign, a, b => {fcopysign a b}

/-- Float comparisons on values. -/
noncomputable def frelop (F : FloatFormat) : FRelOp → FVal → FVal → BitVec 32
  | .eq, a, b => feq a b
  | .ne, a, b => fne a b
  | .lt, a, b => flt F a b
  | .gt, a, b => fgt F a b
  | .le, a, b => fle F a b
  | .ge, a, b => fge F a b

/-- An `f32` result value. -/
def r32 (z : FVal) : Option Val := some (.f32 (fbits f32fmt z))
/-- An `f64` result value. -/
def r64 (z : FVal) : Option Val := some (.f64 (fbits f64fmt z))

/-- An integer result of width `N` as a value (`i32` or `i64`). -/
def intVal : (N : Nat) → BitVec N → Option Val
  | 32, v => some (.i32 v)
  | 64, v => some (.i64 v)
  | _, _ => none

/-- `trunc_sx` into `N` bits: a trap (`none`) on NaN, infinity or out of range. -/
noncomputable def truncTo (F : FloatFormat) (N : Nat) (sx : Sx) (z : FVal) : Option Val :=
  match sx with
  | .u => (ftruncU F N z).bind (intVal N)
  | .s => (ftruncS F N z).bind (intVal N)

/-- `trunc_sat_sx` into `N` bits. -/
noncomputable def truncSatTo (F : FloatFormat) (N : Nat) (sx : Sx) (z : FVal) : Option Val :=
  match sx with
  | .u => intVal N (ftruncSatU F N z)
  | .s => intVal N (ftruncSatS F N z)

/-- `convert_sx` of an `M`-bit integer. -/
noncomputable def convertFrom (F : FloatFormat) {M : Nat} (sx : Sx) (i : BitVec M) : Set FVal :=
  match sx with
  | .u => fconvertU F i
  | .s => fconvertS F i

/-- The results of a numeric instruction on its operands (bottom of the stack first). -/
noncomputable def numResults : Instr → List Val → Set (Option Val)
  | .iunop .w32 op, [.i32 a] => {some (.i32 (iunop op a))}
  | .iunop .w64 op, [.i64 a] => {some (.i64 (iunop op a))}
  | .ibinop .w32 op, [.i32 a, .i32 b] => {(ibinop op a b).map .i32}
  | .ibinop .w64 op, [.i64 a, .i64 b] => {(ibinop op a b).map .i64}
  | .itestEqz .w32, [.i32 a] => {some (.i32 (ieqz a))}
  | .itestEqz .w64, [.i64 a] => {some (.i32 (ieqz a))}
  | .irelop .w32 op, [.i32 a, .i32 b] => {some (.i32 (irelop op a b))}
  | .irelop .w64 op, [.i64 a, .i64 b] => {some (.i32 (irelop op a b))}
  | .funop .w32 op, [.f32 a] => r32 '' funop f32fmt op (ofBits f32fmt a)
  | .funop .w64 op, [.f64 a] => r64 '' funop f64fmt op (ofBits f64fmt a)
  | .fbinop .w32 op, [.f32 a, .f32 b] =>
    r32 '' fbinop f32fmt op (ofBits f32fmt a) (ofBits f32fmt b)
  | .fbinop .w64 op, [.f64 a, .f64 b] =>
    r64 '' fbinop f64fmt op (ofBits f64fmt a) (ofBits f64fmt b)
  | .frelop .w32 op, [.f32 a, .f32 b] =>
    {some (.i32 (frelop f32fmt op (ofBits f32fmt a) (ofBits f32fmt b)))}
  | .frelop .w64 op, [.f64 a, .f64 b] =>
    {some (.i32 (frelop f64fmt op (ofBits f64fmt a) (ofBits f64fmt b)))}
  | .cvtop .wrap, [.i64 a] => {some (.i32 (wrap a))}
  | .cvtop (.extend .u), [.i32 a] => {some (.i64 (extendU a))}
  | .cvtop (.extend .s), [.i32 a] => {some (.i64 (extendS a))}
  | .cvtop (.trunc .w32 .w32 sx), [.f32 a] => {truncTo f32fmt 32 sx (ofBits f32fmt a)}
  | .cvtop (.trunc .w32 .w64 sx), [.f64 a] => {truncTo f64fmt 32 sx (ofBits f64fmt a)}
  | .cvtop (.trunc .w64 .w32 sx), [.f32 a] => {truncTo f32fmt 64 sx (ofBits f32fmt a)}
  | .cvtop (.trunc .w64 .w64 sx), [.f64 a] => {truncTo f64fmt 64 sx (ofBits f64fmt a)}
  | .cvtop (.truncSat .w32 .w32 sx), [.f32 a] => {truncSatTo f32fmt 32 sx (ofBits f32fmt a)}
  | .cvtop (.truncSat .w32 .w64 sx), [.f64 a] => {truncSatTo f64fmt 32 sx (ofBits f64fmt a)}
  | .cvtop (.truncSat .w64 .w32 sx), [.f32 a] => {truncSatTo f32fmt 64 sx (ofBits f32fmt a)}
  | .cvtop (.truncSat .w64 .w64 sx), [.f64 a] => {truncSatTo f64fmt 64 sx (ofBits f64fmt a)}
  | .cvtop (.convert .w32 .w32 sx), [.i32 a] => r32 '' convertFrom f32fmt sx a
  | .cvtop (.convert .w32 .w64 sx), [.i64 a] => r32 '' convertFrom f32fmt sx a
  | .cvtop (.convert .w64 .w32 sx), [.i32 a] => r64 '' convertFrom f64fmt sx a
  | .cvtop (.convert .w64 .w64 sx), [.i64 a] => r64 '' convertFrom f64fmt sx a
  | .cvtop .demote, [.f64 a] => r32 '' fdemote (ofBits f64fmt a)
  | .cvtop .promote, [.f32 a] => r64 '' fpromote (ofBits f32fmt a)
  | .cvtop (.reinterpret .w32 true), [.f32 a] => {some (.i32 a)}
  | .cvtop (.reinterpret .w64 true), [.f64 a] => {some (.i64 a)}
  | .cvtop (.reinterpret .w32 false), [.i32 a] => {some (.f32 a)}
  | .cvtop (.reinterpret .w64 false), [.i64 a] => {some (.f64 a)}
  | _, _ => ∅

end FVA.Wasm.Exec
