# Draft report: WebAssembly spec, `fmul` prose says "infinity" where the equations say zero

Status: draft for the user to post. Target: https://github.com/WebAssembly/spec (issue or pull request).

## Summary

Commit `fe509cad6fc90577fa60264564c6b8ebf4963a43` ("[spec] Add missing zero cases for fmul", 2026-10-22) adds the cases for a zero times a finite non-zero value to `document/core/exec/numerics.rst`. Its equations give a signed zero, but its prose gives a signed infinity:

- Prose: "Else if either z₁ or z₂ is a zero and the other a value with the same sign, then return positive infinity." and "… with opposite sign, then return negative infinity."
- Equations: `fmul_N(±0, ±q₂) = +0`, `fmul_N(±0, ∓q₂) = −0`, `fmul_N(±q₁, ±0) = +0`, `fmul_N(±q₁, ∓0) = −0`.

The equations agree with IEEE 754 (the sign of a product is the exclusive or of the operands' signs, also for zeros) and with the official test suite (for example `test/core/f32.wast`: `(f32.mul (f32.const -0x0p+0) (f32.const 0x1p+0))` returns `-0x0p+0`). The prose must say "positive zero" and "negative zero".

## Background

In the WebAssembly 2.0 specification, the equations for `fmul` cover `±0 · ±0` but not a zero times a finite non-zero value, so that case falls to the last equation, `fmul_N(z₁, z₂) = ieee_N(z₁ · z₂)`, which rounds the exact product 0 to `+0` for every sign. The commit above closes that gap in the equations.

## How this was found

FVA transcribes the WebAssembly 2.0 numerics into Lean and tests the transcription against the official test suite and against wasmtime. The `-0 · 1` tests disagreed with the 2.0 equations, so FVA follows IEEE 754 and the tests there (recorded in its numerics contract). The prose error in the new commit was found when the draft of this report was checked against the current text.
