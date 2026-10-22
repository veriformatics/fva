# U3 contract — Wasm numerics: integers + IEEE-754 floats (tier: kernel)

Purpose: the value-level meaning of every numeric instruction in profile P (U2), reviewed once and shared by every subject (Decisions: Trusted base, Floats). Spec = `FVA/Spec/Numerics/{Int,Float}.lean`; verified impl = `FVA/Impl/Numerics/**` (executable ops proven equal to the spec); evidence = official numeric spec tests.

## Spec (reviewed once)
- N1 Integers (spec §4.3.2): i32/i64 values = `BitVec 32/64`; each op defined spec-shaped through `signed`/`unsigned` interpretations into ℤ/ℕ (e.g. `idiv_s` = truncating ℤ division, trap when divisor 0 or result = 2^(N−1)); partial ops return `Option` (none = trap). Ops: add sub mul div_{u,s} rem_{u,s} and or xor shl shr_{u,s} rotl rotr clz ctz popcnt eqz eq ne lt/gt/le/ge_{u,s} extend{8,16,32}_s wrap extend_{u,s}.
- N2 Float formats: binary32 (p 24, emax 127), binary64 (p 53, emax 1023) as bit vectors with a classification `bits ↔ {nan (sign, payload ≠ 0), inf sign, zero sign, finite sign e m}`; value of a finite = exact ℚ.
- N3 Rounding: `rne : ℝ → Float N` (round to nearest, ties to even; overflow to ±∞ at |x| ≥ (2 − 2^−p)·2^emax; sign of zero preserved by the op rules); operations on finite inputs = `rne` of the exact real result (add sub mul div sqrt, convert_{s,u}, demote, nearest/ceil/floor/trunc are exact-integer variants).
- N4 Special values per spec §4.3.3: ±0 and ±∞ cases, `min`/`max` (−0 < +0, NaN propagation), `copysign`/`abs`/`neg` = sign-bit ops (non-arithmetic, payload preserved), comparisons (NaN → false except `ne`).
- N5 NaN results are a set (spec "nans"): canonical NaN set when all NaN inputs are canonical, arithmetic NaN set otherwise; ops return `Set (Float N)` (or a relation); claims quantify over every allowed result; the executable impl picks one member and proves membership.
- N6 Conversions: `trunc_{s,u}` trap on NaN/out-of-range (Option); `trunc_sat_{s,u}` saturate (NaN → 0); `reinterpret` = identity on bits; `promote`/`demote` with NaN-set rules.

## Implementation
- I1 executable ops over bits (Nat/BitVec arithmetic; rounding via integer significand + guard/round/sticky or exact ℚ when cheaper), each with `theorem op_impl_mem : impl x y ∈ spec x y` (equality for non-NaN results).

## Evidence (each seen red on a planted bug first)
- E1 official tests @ testsuite 44f1503f9840: `i32.wast`, `i64.wast`, `int_exprs.wast`, `int_literals.wast`, `f32.wast`, `f64.wast`, `f32_cmp.wast`, `f64_cmp.wast`, `f32_bitwise.wast`, `f64_bitwise.wast`, `float_exprs.wast`, `float_misc.wast`, `float_literals.wast`, `conversions.wast` — every `assert_return` / `assert_trap` on single-op functions passes (NaN patterns `nan:canonical` / `nan:arithmetic` = set membership); a small numeric runner maps export → op (no interpreter needed; U5 later runs the full suite through U4).
- E2 planted bugs fire: RNE → round-toward-zero, `min(−0,+0) = +0`, `rem_s(MIN, −1)` trap.
- E3 spot difftest vs wasmtime on random bit patterns (≥ 10⁵ per binary op) for non-NaN results; NaN results checked for set membership.
