import FVA.Impl.Decode
import FVA.Tool.Pack
import Lean.Elab.Tactic.Basic

/-!
# Support for `Lifted.lean` files written by `fva lift`

Both elaborators are untrusted: the kernel checks `decode_eq`, and `fva trust` compares the
`bytes` numeral and `len` with the file.

* `wasm_bytes% "<hex>"`: the numeral packing these bytes little-endian (hex in file order),
  built in `O(n log n)`; a 96 KB file as a decimal literal takes 28 s to elaborate.
* `kernel_rfl`: proves `lhs = rhs` by `Eq.refl rhs`, checked by the kernel alone. The
  elaborator's `rfl` hits recursion limits on a decoder run, and `decide +kernel` evaluates
  derived `DecidableEq` matchers (lz4 C `decode_eq`: comparison 7 s vs 1.3 s).
-/

open Lean Elab Term Tactic Meta

/-- The numeral packing the given bytes (hex digits in file order) little-endian. -/
elab (name := wasmBytesTerm) "wasm_bytes% " s:str : term => do
  match FVA.Tool.ofHex s.getString with
  | some bs => return mkRawNatLit (FVA.Tool.packBytes bs)
  | none => throwErrorAt s "wasm_bytes%: expected an even number of lowercase hex digits"

/-- Prove `lhs = rhs` by kernel definitional unfolding (no elaborator `isDefEq`). -/
elab (name := kernelRflTactic) "kernel_rfl" : tactic => liftMetaFinishingTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar || t.hasFVar then throwError "kernel_rfl: goal must be closed"
  let some (α, _, rhs) := t.eq? | throwError "kernel_rfl: goal is not an equality"
  let u ← getLevel α
  let n ← mkAuxDeclName `kernel_rfl
  let v := mkApp2 (mkConst ``Eq.refl [u]) α rhs
  addDecl (.thmDecl { name := n, levelParams := [], type := t, value := v })
  g.assign (mkConst n)
