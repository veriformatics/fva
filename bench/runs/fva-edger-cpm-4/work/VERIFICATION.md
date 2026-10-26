# Verification of the shipped edgeR files

Both README requirements, read literally over their stated domains, have counterexamples. R1 has a Lean/FVA proof about the decoded function bodies and an execution of the original module. R2 has executable counterexamples using the unchanged R filter and the original module for raw CPM. This is not a proof that either universal requirement holds.

## R1: intermediate overflow

Input: a 1 by 1 matrix with count `c = 2^1023`, library size `L = 2^1023 > 0`, and one thread. Both inputs are finite, exactly representable binary64 values (`0x7fe0000000000000`). The count does not exceed the library size.

The artifact writes `+Infinity` (`0x7ff0000000000000`). It computes `fl(fl(c * 1000000) / L)`; the multiplication overflows. The exact mathematical answer is `1000000`, and evaluating `(c / L) * 1000000` in binary64 gives that answer with **zero rounding error** for this input. Consequently, no finite absolute or relative rounding-error bound applies to the artifact over all of R1's stated domain. No universal accuracy theorem for a restricted, overflow-free domain is claimed.

The principal machine-checked theorem, in [Proofs/Proof.lean](Proofs/Proof.lean), is exactly:

```lean
theorem Proofs.r1_overflow_holds : Proofs.r1_overflow
```

Its full proposition is defined in [Proofs/Spec.lean](Proofs/Spec.lean):

```lean
def r1_overflow : Prop :=
  (∃ e ∈ Lifted.module.exports, e.name = "calc_cpm_raw" ∧ e.desc = .func 160) ∧
  Lifted.module.funcs[86]? = some Lifted.func86 ∧
  Lifted.module.funcs[133]? = some Lifted.func133 ∧
  ∀ H, CallReturns H testStore testInst "calc_cpm_raw"
    [.i32 32768, .i32 32800, .i32 32832, .i32 1] fun s vs =>
      vs = [] ∧ ∃ m, s.mems[0]? = some m ∧
        (List.range 8).map (fun k => m.byte (32832 + k)) =
          [0, 0, 0, 0, 0, 0, 240, 127]
```

`CallReturns` means every permitted execution terminates, never traps, and satisfies the final-memory condition. The eight bytes are precisely positive infinity in little-endian binary64. The proof checks the deterministic execution with FVA's verified interpreter, then uses its soundness theorem to obtain this total semantic statement; the semantic claim has no fuel parameter.

The supporting arithmetic theorem in `Proofs/Proof.lean` is:

```lean
theorem Proofs.equal_count_exact (c : ℝ) (hc : c ≠ 0) :
  c / c * 1000000 = 1000000
```

**Environment scope:** `testStore`, `testInst`, `testByte`, `testAlloc`, and `testFree` are reviewed definitions in the spec. They describe non-null matrix pointers, one memory page, the two exact artifact function bodies, and small Wasm implementations of the two allocation/free imports. The allocator returns distinct aligned zeroed regions for the two requests in this test; free has no observable effect before termination. Other function slots are unused placeholders. This is a proof of function execution in that explicit environment, not a formal proof of full module instantiation, its start function, the R runtime, or arbitrary allocator behavior. The ABI interpretation of the memory layout comes from `src/edgeR.h`.

[verification/artifact.cjs](verification/artifact.cjs) separately instantiates the **entire unchanged artifact**, including its start function, in Node's WebAssembly engine. It supplies imported memory, globals and table, an allocating/zeroing host, and checked frees. Every other function import throws if called. It verifies the artifact's hash before execution and asserts the observed infinity and a normal control case (`c=10`, `L=1000000`, result `10`). This execution closes the practical module-loading gap for the counterexample; it is runtime evidence, not an additional Lean theorem.

## R2: the sample criterion is not an exact equivalence

[verification/filter.R](verification/filter.R) sources the unchanged `R/filterByExpr.R`. Its `cpm` adapter passes the numeric matrix and positive library sizes to the original artifact through `verification/artifact.cjs`, then reconstructs the returned matrix in R. It replaces the R-to-Wasm ABI bridge; it does not rewrite the filtering algorithm or run a different filtering model. It does not execute the S3 dispatch and `.Call` machinery of `R/cpm.R`.

The script checks two concrete failures of the README's exact equivalence:

1. **Sufficiency fails with integer sample size.** `y = matrix(10,1,1)`, `lib.size = 1000000`, `min.sample.size = 1`, all other parameters at their defaults. The CPM is exactly 10, the scaled cutoff is exactly 10, and the required one sample qualifies. Nevertheless, the filter returns `FALSE`, because total count 10 fails `min.total.count = 15` (including its `1e-14` tolerance). Setting `min.total.count = 0` makes the same gene pass. The bundled manual explicitly documents this additional total-count condition. Thus this witness exposes an incomplete README requirement, rather than a violation of that manual's total-count rule.

2. **Necessity fails for an exact fractional sample cutoff, even with sufficient total count.** `y = matrix(c(15,0),1,2)`, `lib.size = c(1000000,1000000)`, `min.sample.size = 1 + 2^-48`, defaults otherwise. Exactly one sample meets the CPM cutoff; total count is 15. The required size is `1.0000000000000036`, strictly greater than one, yet the filter returns `TRUE`. Its comparison subtracts `tol = 1e-14` from the required sample size. Neither the README's exact equivalence nor the displayed cutoff formula in the manual includes this tolerance. If tolerance is intended as part of the requirement, that requirement needs to say so.

These are R execution results enforced by `stopifnot`, not machine-checked theorems about an R semantics. No universal theorem about `filterByExpr`, all presets, all designs, or S3 methods is claimed.

## Byte binding and reproduction

The subject is the supplied **96,558-byte** `edgeR.so`, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

[Proofs/Lifted.lean](Proofs/Lifted.lean) was generated with:

```sh
lake exe fva lift edgeR.so Proofs/Lifted.lean --ns Proofs.Lifted
```

It embeds all the bytes and proves `decode_eq` with the kernel. Its function 86 is module function index 160 after the 74 imported functions; function 133 is index 207 (`get_row`). The proof executes those exact generated bodies. FVA's link check compares the embedding with `edgeR.so` and checks the generated file. No C recompilation or source-to-Wasm equivalence assumption is used. The supplied C files are unchanged.

From this directory, run the complete check:

```sh
bash verification/check.sh
```

The script checks [verification/subjects.sha256](verification/subjects.sha256), builds the Lean proofs, runs both counterexample scripts, builds an FVA executable outside this project using the installed offline dependencies, and runs:

```sh
EXTERNAL_FVA trust . --spec-module Proofs.Spec --root-module Proofs
```

Here `EXTERNAL_FVA` is the executable the script builds in its temporary directory. A successful run exits zero, prints all subject hashes as `OK`, prints the R1 and R2 counterexamples and controls, obtains FVA `PASS`, and ends with `All checks passed: the R1 and R2 counterexamples were reproduced.` The FVA transcript is saved as [verification/trust.txt](verification/trust.txt). `PASS` validates the counterexample proposition, not the original universal requirements.

The components can also be run individually:

```sh
sha256sum -c verification/subjects.sha256
lake build
node verification/artifact.cjs
Rscript --vanilla --default-packages=base,stats verification/filter.R
```

The installed environment used Lean 4.35.0 with Mathlib v4.35.0, Node v26.11.1 and R 4.6.1. No downloaded packages are needed.

## Review and trust

The observed FVA verdict is **PASS**. Both `leanchecker` and the independently implemented `con-leche` accepted the exported proof bundle; the artifact link matched. FVA measured **37 code lines** of review surface.

Review the claim and concrete ABI environment in `Proofs/Spec.lean` (68 physical lines, 3,454 bytes). The generated `Proofs/Lifted.lean` is byte-bound and kernel-decoded; its 1,167,921 bytes need not be manually transcribed or trusted. `Proofs/Proof.lean` is checked proof code, with no `sorry`, native-decision axiom, or added axiom. FVA reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

For the execution evidence, read `verification/artifact.cjs` (83 lines, 3,529 bytes), `verification/filter.R` (35 lines, 1,768 bytes), and the reproduction driver `verification/check.sh` (33 lines, 1,410 bytes). The hash manifest (7 lines, 556 bytes) binds the unchanged subject files, including `README.md` (13 lines, 1,287 bytes) and `man/filterByExpr.Rd` (161 lines, 7,329 bytes). The relevant existing R code is `R/filterByExpr.R` (115 lines, 3,745 bytes) and, for the adapter correspondence, `R/cpm.R` (114 lines, 3,771 bytes). The ABI declaration is in `src/edgeR.h` (381 lines, 14,858 bytes); only the `cmx` structure and relevant signatures are needed. The manual's precise filtering formula and total-count condition also require human interpretation.

The formal result rests on FVA's pinned Wasm specifications and verified decoder/interpreter/numerics, its link and trust orchestration, Lean and the independent replay kernel, Mathlib, and the toolchain. The recorded canary run reports one known false-export acceptance by `leanchecker`, allowed by FVA's pinned known-acceptance policy; `con-leche` accepted none, rejected 69 and declined 3 of the 72 false-export canaries. The complete policy and results are in `verification/trust.txt`; PASS should not be interpreted as every checker rejecting every false canary.

The runtime demonstrations additionally trust Node's WebAssembly engine, R's interpreter and numeric operations, the small ABI adapters, and the operating system. FVA does not formally verify these runtime scripts or the English interpretation of the requirements. These boundaries are why the report distinguishes the Lean function-execution theorem from the full-module and R demonstrations.
