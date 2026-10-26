Both README requirements fail as written. The supplied counterexamples use the
unchanged shipped artifact and unchanged R sources. There is no universal
correctness or finite rounding-error guarantee for R1, and no proof of R2's
equivalence. The positive formal results below certify the counterexamples'
Wasm computations under an explicit linked-state fixture.

Final FVA audit: **PASS**, using a verifier rebuilt outside this project.
All four claims were accepted by `leanchecker` (158 seconds) and the independent
`con-leche` kernel (136 seconds). The artifact link matched. FVA reports an
80-code-line project review surface: 35 in `Proofs.Spec` and 45 in
`Proofs.Fixture`. The complete output is in `verification/fva-trust.txt`.

For R1, take a one-row, one-column double matrix with count
`c = 2^1023` and library size `L = 2^1023`, and initialize the output buffer
with the count, as `cpm.default` does. Both inputs are finite, positive, exactly
representable doubles. The exact mathematical result is
`(2^1023 / 2^1023) * 1000000 = 1000000`, also exactly representable.
The artifact writes **positive infinity**, bits `0x7ff0000000000000`.
Its instruction order is multiplication by one million followed by division:
the intermediate multiplication overflows. Thus the error from the finite
mathematical target is unbounded; no finite absolute or relative error bound
holds over R1's stated domain. In particular this is not an unavoidable
overflow of the final mathematical result.

`Proofs.r1_overflow_holds` proves the input's binary64 decoding, positivity of
the library size, the exact real-valued target, and total termination without
trapping with that infinity written to memory in the fixture. The runtime
demonstration additionally instantiates the complete unchanged binary, calls
its exported `calc_cpm_raw`, and checks the output bits. The R demonstration
also executes the shipped `cpm.default` on this input.

For R2 there are two independent witnesses:

| Input and parameters | README's criterion | Actual result |
| --- | --- | --- |
| One sample: count `10`, library `1000000`, `min.sample.size=1`; other parameters default | One required sample reaches `min.count=10` | `FALSE`: total count `10` is below default `min.total.count=15` |
| Two samples: counts `[10,10]`, libraries `[18,18]`; all filtering parameters default, no design/group | Both required samples reach `min.count=10`; total count `20` also exceeds `15` | `FALSE`: each computed CPM is below the computed cutoff |

The first witness is a mismatch between README R2 and the documented extra
total-count condition: `man/filterByExpr.Rd` explicitly requires it and the
implementation applies it. It does not establish a defect relative to that
part of the manual. The second witness remains after including that condition.
Since the libraries are equal, their median is `18` and the documented scaled
threshold corresponds exactly to count `10`. The implementation nevertheless
compares these different binary64 values:

| Quantity | Exact binary64 bits | Decimal display |
| --- | --- | --- |
| Artifact CPM: `(10 * 1000000) / 18` | `0x4120f4471c71c71c` | `555555.5555555555` |
| R cutoff: `(10 / 18) * 1000000` | `0x4120f4471c71c71d` | `555555.55555555562` |

The artifact value is below the cutoff by one binary64 step, `2^-33`.
Its signed error relative to exact `10/18 * 1000000` is
`-1/19327352832`. This exact error and the strict inequality are proved in
Lean. `filterByExpr.default` applies `CPM >= CPM.Cutoff`, so neither sample
qualifies and the gene is rejected. Its `tol` adjusts the required sample
number and total-count threshold, not the CPM comparison. The R script
asserts both failures and a nearby passing control with counts `[20,20]`.
This second witness concerns equivalence to the exact scaled count threshold.
It is consistent with the manual's literal test on already rounded CPM values;
that test can disagree with the count-threshold reading at an equality boundary.

The exact theorem signatures in `Proofs/Proof.lean` are:

```lean
theorem Proofs.artifact_binding_holds : Proofs.artifact_binding
theorem Proofs.r1_overflow_holds : Proofs.r1_overflow
theorem Proofs.r2_cpm_bits_holds : Proofs.r2_cpm_bits
theorem Proofs.r2_rounding_gap_holds : Proofs.r2_rounding_gap
```

Their exact propositions, including the hexadecimal inputs and outputs, are
the four definitions in `Proofs/Spec.lean`. `artifact_binding` checks the
74 function imports, the export index `160`, defined function indices `86`
and `133` (the latter is `get_row`, function index `207`), and both signatures.
`r2_cpm_bits` proves the artifact's output bits for count `10` and library `18`.
`r2_rounding_gap` includes that result, proves binary64 division followed by
multiplication returns the cutoff bits above, and proves the exact real-valued
error and strict inequality. That cutoff execution is explicitly a Wasm
binary64 model of the two R arithmetic operations; the R execution itself is
a runtime demonstration, not a Lean formalization of R.

The artifact connection is to all **96,558 bytes** of `edgeR.so`, SHA256:

```text
e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb
```

`Proofs/Lifted.lean` was generated with FVA. Its `decode_eq` is kernel-checked
against the complete byte numeral. FVA's link check compares that numeral with
`edgeR.so` and independently regenerates the entire generated Lean file.
No C recompilation or replacement arithmetic implementation establishes these
formal results: the fixture installs the two actual decoded function bodies.

The formal fixture in `Proofs/Fixture.lean` installs only reachable functions,
supplies a zeroing bump allocator and a no-op free, initializes valid 1x1
matrix descriptors and buffers, and maps their imported calls to those fixture
functions. The theorems quantify over all FVA host relations, although these
calls only execute Wasm functions. They are `CallReturns` total-correctness
claims about this particular linked state. **No `Instantiated` or `LoaderReady`
theorem for the complete dynamic library is claimed.**

`verification/reproduce.py` covers that remaining connection by a runtime
demonstration: it SHA256-checks the artifact, embeds the original binary bytes
unchanged in a WAST script, supplies all imports, performs instantiation,
relocations and constructors, builds descriptors using the artifact's own
`make_cmx`, and calls the artifact's exported `calc_cpm_raw`. Allocator/free
imports have the same intended behavior as the formal fixture; constructor
registration and single-thread mutex imports return success. All other
imported functions trap if called. This harness does not simulate an entire
R process or claim correctness for other exports or host configurations.

`verification/filter.R` sources the unchanged `R/cpm.R` and `R/filterByExpr.R`.
Its two package integration shims implement matrix compression for these
one-row double inputs and the `.Call` bridge. Every CPM matrix supplied by
that bridge is accepted only after Wasmtime executes the complete original
`calc_cpm_raw` on the same 1xN inputs and checks every output's 64 bits.
Thus the bridge's R arithmetic is an asserted candidate output, not the
evidence for itself. Dispatch, cutoff arithmetic, median, sample counting,
total-count filtering and final conjunction execute in the shipped R source.
These R source SHA256 values are checked by the Python harness:

```text
b43ab97191a448ef8d141decdef802be3329801692a9c9a0618cf5ef874eb39b  R/cpm.R
abd43b83d5742dd789fb501ec49d073c690000e23d09604c4d085165a6c92f5f  R/filterByExpr.R
```

Run these commands from this directory, with the installed offline toolchain:

```bash
lake build
python3 verification/reproduce.py
OPENBLAS_NUM_THREADS=1 Rscript --vanilla verification/filter.R
bash verification/trust.sh > verification/fva-trust.txt 2>&1
cat verification/fva-trust.txt
```

Every checking command must exit zero. Lean prints `Build completed successfully`;
Python prints `All unchanged-artifact Wasmtime assertions passed.`; R prints
`All R assertions and their unchanged-artifact CPM checks passed.` The R failures
are expected counterexamples and asserted as such, not failed test runs.
FVA must report `fva trust: PASS`, four proved claims, both `leanchecker` and
`con-leche` accepted, and `Proofs.Lifted (edgeR.so) [lifted]: matches`.
PASS certifies the stated counterexample claims, not satisfaction of R1/R2.
Replay can take several minutes. `verification/trust.sh` copies the supplied
FVA package into a temporary directory and rebuilds the executable there,
using the already installed packages; it then judges this project and removes
the temporary copy. It needs no network. The BLAS setting prevents unnecessary
R startup threads and does not change any arithmetic used here.

The project-specific review material and its physical size are:

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `Proofs/Spec.lean` | 54 | 2601 | Exact claims and their interpretation |
| `Proofs/Fixture.lean` | 60 | 2675 | Linked-state fixture and cutoff model |
| `verification/reproduce.py` | 122 | 6121 | Full-binary runtime harness and source-byte checks |
| `verification/filter.R` | 51 | 2419 | R execution, package shims and assertions |
| `verification/trust.sh` | 31 | 1439 | External verifier build and invocation |
| `R/cpm.R` | 114 | 3771 | Shipped R wrapper executed by the demonstration |
| `R/filterByExpr.R` | 115 | 3745 | Shipped filter executed by the demonstration |

The manual's `min.total.count` condition and the README requirements must also
be read to judge intent (`man/filterByExpr.Rd`: 161 lines / 7,329 bytes).
The generated lift is 897 lines / 1,167,921 bytes and
the proof file is 70 lines / 2,608 bytes; their contents are checked by FVA,
so human inspection of those implementations is not part of the claimed
formal review surface. The runtime demonstrations additionally trust Python,
`wasm-tools`, Wasmtime and R and the explicitly listed shims. There is no
verified R interpreter or proof of the package integration shims.

The formal results retain FVA's documented base trust: its Wasm/binary/numeric
specifications, trust/link/export orchestration, Lean and the independently
replayed kernel, and the pinned Mathlib environment. Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` occur; there are no `sorry`,
custom axioms, `native_decide` or `bv_decide` proofs. FVA's canary results and
project code-line review count are recorded in `verification/fva-trust.txt`.
For the 72 bad canaries, `leanchecker` rejected 71 and accepted one documented
known case; `con-leche` rejected 69, declined three and accepted none. FVA's
required rejection coverage passed; neither replay crashed or timed out.
The FVA specification directory has 23 Lean files, 3,606 physical lines and
161,903 bytes. The trust orchestration in `FVA/Trust/*.lean` plus
`FVA/Tool/Trust.lean` has 5 files, 1,196 lines and 56,949 bytes. These are base
components, separate from the project-specific review surface.
The pinned canary set and documented acceptance table in `fva/trust/canaries/`
add 198 physical lines / 20,740 bytes.
Runtime checks
used Wasmtime 50.0.0, wasm-tools 1.262.0, Python 3.14.8 and R 4.6.1; formal
checks used Lean/Mathlib 4.35.0. Saved demonstration output is in
`verification/wasm-results.txt` and `verification/r-results.txt`.
