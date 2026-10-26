# Verification results

Both requirements fail on their stated domains. The evidence consists of executions of the original WebAssembly bytes, execution of the shipped R filtering code with an artifact-checked CPM adapter, and Frama-C 33.0 WP proofs of explicit witness models. The software and requirements were not changed. No universal correctness theorem is claimed.

## R1: intermediate overflow defeats the universal claim

Use a one-row, one-column double matrix with count `c = 0x1p+1020`, library size `L = 0x1p+1020`, and `nthreads = 1`. Both inputs are finite, positive, exactly representable binary64 numbers.

The machine-checked results in `verification/witness.wast`, generated and run by `verification/build_witness.py`, are:

- Calling the original exported `calc_cpm_raw` on this input writes **positive infinity** to its output cell.
- Evaluating the division-first binary64 expression `(0x1p+1020 / 0x1p+1020) * 1000000` returns **1000000**.

The mathematical value is also exactly 1000000. Its correctly rounded binary64 value has **zero rounding error**. The artifact instead executes `RN(RN(c * 1000000) / L)`: the intermediate multiplication overflows. Its absolute and relative error against this finite target are infinite. Thus no finite rounding-error bound for the computed result holds over all the inputs in R1, even when the exact final result is representable. Restricting the domain to avoid intermediate overflow would be a different requirement. If “as double-precision arithmetic allows” is intended to permit intermediate overflow, it permits infinite error here and does not guarantee a rounded CPM value.

The supporting WP theorem is the contract of `r1_reference_witness` in `verification/requirements.c`, with no preconditions:

```acsl
assigns \nothing;
ensures reference_exact: \result == 1000000.0;
```

Its body uses the exact witness inputs and division-first double arithmetic. This theorem proves the reference evaluation, not the artifact's overflowing execution; the latter is checked directly by Wasmtime's `assert_return`.

## R2: a boundary gene is rejected despite satisfying the count rules

Use the following matrix, all default filtering arguments, and no group, design, or explicit library sizes:

```r
y <- matrix(c(10,26,10,26), nrow=2)
#       sample1 sample2
# gene1      10      10
# gene2      26      26
filterByExpr(y)
```

Column sums are `(36,36)`, so the median library size is 36 and the required number of samples is 2. Gene 1 has exactly `min.count = 10` in both samples, and total count 20 exceeds `min.total.count = 15`. With equal library sizes, the documented scaling leaves the per-sample count threshold exactly 10. Neither the large-group adjustment nor the maximum-sample cap applies.

Nevertheless the checked result is `c(FALSE, TRUE)`. The artifact's CPM and the R cutoff for gene 1 differ by one binary64 step:

| Quantity | Exact value of the stored double | Decimal display |
| --- | --- | --- |
| Artifact CPM, `10 * 1000000 / 36` | `1193046471111111 / 4294967296` = `0x1.0f4471c71c71cp+18` | 277777.77777777775 |
| R cutoff, `10 / 36 * 1000000` | `4772185884444445 / 17179869184` = `0x1.0f4471c71c71dp+18` | 277777.77777777781 |

Consequently both `CPM >= CPM.Cutoff` comparisons are false. The `1e-14` tolerance is applied to the number of qualifying samples and the total count, not to the CPM comparison, so it does not rescue this gene.

The WP theorem is the contract of `r2_rounding_boundary` in `verification/requirements.c`, with no preconditions:

```acsl
assigns \nothing;
ensures rejected_despite_counts_and_total: \result == 0;
```

WP also proves every intermediate assertion, whose exact statements are:

```acsl
count >= 10.0;
cpm == 1193046471111111.0 / 4294967296.0;
cutoff == 4772185884444445.0 / 17179869184.0;
hits == 0;
keep_cpm == 0;
keep_total == 1;
```

Here ACSL divisions denote exact real division. The C computations being checked use double arithmetic. This is an explicit translation of the numerical tail for this input, not a formal translation of arbitrary R programs.

There is also a simpler logical failure of R2's literal “exactly when”: `filterByExpr(matrix(10,1,1), lib.size=1e6, min.sample.size=1)` returns `FALSE` although its only sample reaches the threshold. The additional total-count condition rejects total 10 against default 15. This extra condition is itself documented in `man/filterByExpr.Rd`; it is an omission in the literal README equivalence, not evidence that this particular total-count check contradicts the manual. The two-sample rounding counterexample above satisfies that extra condition too.

For the simpler input, WP checks `r2_rejects_witness` in the same C file, with no preconditions:

```acsl
assigns \nothing;
ensures rejected_by_total: \result == 0;
```

It additionally proves `cutoff == 10.0`, `hits == 1`, `keep_cpm == 1`, and `keep_total == 0`.

## Connection to the shipped code

`edgeR.so` is 96,558 bytes, SHA-256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

The Python harness checks this length and hash, then embeds **all original bytes verbatim** in a WAST `module binary`. It does not recompile the C source or replace the target function. Disassembly supplies import signatures only. The original `calc_cpm_raw` (function 160) and its original `get_row` (function 207) execute inside Wasmtime.

The environment supplies linear memory, a table, globals, a small zero-initialized bump allocator for `R_chk_calloc`, and a no-op `R_chk_free`. Other imported functions trap if called. Matrix structures use the wasm32 layout of `cmx` in `src/edgeR.h`: pointers at offsets 0 and 4, dimensions at 8 and 12, type at 16, integer flag at 20, physical stride at 24, and row-selection pointer at 28. The scalar witnesses use full double matrices. The two-sample witness uses a full count matrix and row-repeated library sizes (type 2). Inputs and allocations occupy separate memory regions beyond the module's static data. No constructor is needed for this raw numerical entry point.

For R2, `verification/check_r.R` sources the unmodified `R/filterByExpr.R` and invokes its actual generic/default method. That file's SHA-256 is checked by the Python harness:

```text
abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f
```

Native R cannot load this wasm library as a native `.so`. Therefore the R run supplies a narrowly scoped `cpm` adapter: it accepts only the two witness inputs and their expected library sizes. For the scalar case it returns 10, independently checked on the artifact. For the matrix case it returns `verification/artifact_cpm.R`, whose **four cells are individually asserted equal to the original artifact's outputs** in the same generated WAST test. The expected matrix is two identical columns `(0x1.0f4471c71c71cp+18, 0x1.60a5c71c71c72p+19)`. Those checks must pass before R runs.

The adapter bypasses `R/cpm.R`, its compressed-matrix helper, and the R `.Call` wrapper. The connection to the normal call path relies on reading `cpm.default` in `R/cpm.R`: with these positive numeric matrices and no offsets it passes the counts and column library sizes to the raw kernel. This is not a machine-checked proof of the R/C ABI or wrapper implementation. The filter's column sums, median, sample-size selection, cutoff, comparisons, total counts, and final conjunction all execute as shipped. No R filtering branch is replaced.

The Frama-C input is `verification/requirements.c`, an explicitly written witness model. It has no axioms, assumed helper contracts, or preconditions. WP checks it under `Typed+float` with runtime-error obligations; it is not a whole-library proof, a verified decompilation, or a proof of arbitrary matrices, memory safety, threading, or all R semantics. The counterexamples suffice to refute the universal requirements. Lean is not used.

## Reproduce every result

From this directory run:

```sh
bash verification/check.sh
```

This runs these commands in order, recording output in `verification/artifact.log`, `verification/r.log`, and `verification/wp.log`:

```sh
python3 verification/build_witness.py
Rscript --vanilla verification/check_r.R
frama-c --check-wp . verification/requirements.c \
  -wp -wp-rte -wp-model Typed+float -wp-prover alt-ergo \
  -wp-timeout 10 -wp-cache none
```

Success means exit status zero, both artifact `PASS` messages, both R `PASS` messages, **`Proved goals: 40 / 40`**, and the final `PASS: all artifact assertions, R witnesses, and WP goals checked`. The run used 22 Qed and 12 Alt-Ergo proofs plus 3 termination and 3 unreachable obligations. The wrapper's `--check-wp` rejects any unproved reported goal; proof cache reuse is disabled. The generated WAST can also be checked directly with `wasmtime wast -C cache=n verification/witness.wast` (zero exit status, normally no output).

The warning that `1e-14` becomes `0x1.6849b86a12b9bp-47` records its actual binary64 representation. WP also reports skipped alignment/function-pointer RTE guards; the model has neither pointer accesses nor function calls, so these guards are inapplicable. No goals remain unknown or timed out in the final run.

Installed versions used: Frama-C 33.0 (Arsenic), Alt-Ergo 2.5.4, Wasmtime 50.0.0, wasm-tools 1.262.0, R 4.6.1, Python 3.14.8. No network or additional packages are needed.

## Review and trust boundary

The following sizes count physical lines and bytes. Generated files are reproducible, not independent proof assumptions.

| File | Lines | Bytes | What a reviewer must check/trust |
| --- | ---: | ---: | --- |
| `verification/requirements.c` | 56 | 2,179 | Exact witness models and ACSL specifications; correspondence of their arithmetic to the selected R tail/reference |
| `verification/build_witness.py` | 113 | 6,457 | Hash checks, unchanged binary embedding, import environment, ABI layout, inputs, and WAST assertions |
| `verification/check_r.R` | 27 | 1,359 | Restricted adapter and assertions; use of the actual R filtering function |
| `verification/check.sh` | 10 | 471 | Ordered execution and propagation of failures through pipelines |
| `verification/artifact_cpm.R` (generated) | 1 | 107 | Exact shared CPM values; all cells checked against the artifact |
| `verification/witness.wast` (generated) | 222 | 302,983 | Executable import environment, original binary, and assertions; can be inspected independently |
| `R/filterByExpr.R` | 115 | 3,745 | Actual filtering program; R execution is part of the evidence |
| `R/cpm.R` | 114 | 3,771 | Read to justify the counts/library-size mapping to the raw kernel; not executed by this harness |
| `src/edgeR.h` | 381 | 14,858 | Matrix ABI definition used by the harness |
| `src/compute_cpm.c` | 266 | 6,996 | Explanatory source arithmetic; no source/binary equivalence is assumed for the directly executed witnesses |
| `man/filterByExpr.Rd` | 161 | 7,329 | Documented threshold, sample rule, and extra total-count condition |

The remaining trusted machinery is Frama-C's C/ACSL frontend, WP generation, IEEE floating-point model and Qed simplifier, Why3/Alt-Ergo, the supplied `frama-c --check-wp` wrapper, Wasmtime's validation and binary64 execution, wasm-tools' import disassembly, Python's standard library/hash implementation, R's interpreter and numerical primitives, and the host execution environment. These are trusted tools, not kernel-checked Lean proof terms. Logs are evidence of a run; the commands above regenerate the checks.
