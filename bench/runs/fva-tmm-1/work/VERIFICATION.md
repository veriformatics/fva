# Verification of the shipped TMM factors

The ten-decimal-place agreement requirement **R3 is false**. Every paired
entry in the two shipped files differs by more than **0.001**. Sample 1 alone
is a counterexample: edgeR's `0.99099942459293067` and RNAnorm's
`0.9816880015656044` differ by exactly `0.00931142302732627`.

For **R1 and R2**, the certified absolute tolerance is **0.025 per factor**,
relative to the exact-real mathematical TMM model described below. This is a
coarse tolerance, not a claim of ten-digit numerical accuracy. An additional
proof shows that **both files have error greater than 0.02 for sample 3**
relative to that model. Runtime reproduction and mathematical accuracy are
separate results here.

Validation completed successfully: `lake build` passed and the external
FVA invocation returned **`fva trust: PASS`**. All four claims are proven;
all three blob links match. Independent replay accepted the exported
proofs in `leanchecker` (692 seconds) and `con-leche` (444 seconds). The
saved verdict is `verification/fva-trust.txt`.

## 1. Machine-checked statements

The main theorem declarations are in `Proofs/Proof.lean`, with
`R3Fails_holds` in `Proofs/Discrepancy.lean`:

```lean
theorem Proofs.R1_holds : Proofs.R1
theorem Proofs.R2_holds : Proofs.R2
theorem Proofs.R3Fails_holds : Proofs.R3Fails
theorem Proofs.tightAccuracyFails_holds : Proofs.tightAccuracyFails
```

Their exact proposition definitions are in `Proofs/Spec.lean`. In particular:

- `R1` existentially supplies a 454 × 7 natural-number matrix and seven exact
  decimal factors, proves that their encodings equal **all the bytes** of
  `counts.tsv` and `edger-factors.txt`, checks `matrixOK`, and proves
  `∀ j ∈ List.range 7, |(decimalValue ds[j]! : ℝ) - tmm xs j 3| ≤ 1 / 40`.
- `R2` is the same statement for `rnanorm-factors.txt`.
- `R3Fails` supplies exact decimal interpretations of both complete output
  files, proves that both lists have length seven, and proves
  `∀ j ∈ List.range 7, 1 / 1000 < |(decimalValue es[j]! : ℝ) - (decimalValue rs[j]! : ℝ)|`.
  This counterexample uses the supplied `counts.tsv` and its supplied outputs;
  it does not depend on the TMM model or on a proposed explanation of the bug.
- `tightAccuracyFails` binds the same three complete files, checks
  `matrixOK`, and proves both
  `1 / 50 < |(decimalValue es[2]! : ℝ) - tmm xs 2 3|` and
  `1 / 50 < |(decimalValue rs[2]! : ℝ) - tmm xs 2 3|`.
  Indices in Lean are zero based: index 2 is sample 3.

The supporting statements `Proofs.Numeric.factor0` through `factor6`, in
`Proofs/Numeric.lean`, certify the following closed intervals. The endpoints
shown here are exact decimals, not rounded displays of the bounds.

| Sample | Lower bound on mathematical TMM | Upper bound |
| --- | ---: | ---: |
| 1 | 0.975526 | 0.975529 |
| 2 | 1.281082 | 1.281085 |
| 3 | 1.147753 | 1.147756 |
| 4 | 0.956410 | 0.956413 |
| 5 | 0.815784 | 0.815787 |
| 6 | 0.932436 | 0.932439 |
| 7 | 0.958279 | 0.958282 |

For example, the exact third supporting statement is:

```lean
theorem Proofs.Numeric.factor2 :
  ((1147753 / 1000000 : ℝ) ≤ Proofs.tmm Proofs.Witness.matrix 2 3) ∧
  (Proofs.tmm Proofs.Witness.matrix 2 3 ≤ (286939 / 250000 : ℝ))
```

`Witness.counts_eq` connects `Witness.matrix` to the matrix file. The main
R1/R2 proofs use all seven supporting intervals, so they are included in the
independent replay of those proofs.

### Meaning and limits of the mathematical model

`Proofs/Model.lean` defines the reviewed mathematical specification:

1. Genes are rows, samples are columns; library sizes are column sums.
   Remove rows zero in every sample.
2. Use the linearly interpolated 75th percentile divided by library size.
   The reference is the unique sample closest to the mean of those seven
   values. The proof checks reference sample 4 and positive quartiles;
   the edgeR zero-quartile fallback does not apply.
3. For each comparison, exclude pairs with a zero count. Rank M by exact
   count ratios, and A by exact count products. These preserve the orders
   of their logarithms. Use **average ranks for exact ties**.
4. Retain ranks from `floor(0.3*n)+1` through `n-floor(0.3*n)` for M and
   `floor(0.05*n)+1` through `n-floor(0.05*n)` for A, inclusively.
5. Use inverse asymptotic binomial variance weights:
   `1 / ((1/a - 1/library) + (1/b - 1/referenceLibrary))`.
6. Take the weighted mean of natural log ratios, correcting for library
   sizes; subtract the mean of the seven log factors and exponentiate.
   Using natural logs here is algebraically equivalent to log2 followed
   by exponentiation with base 2.

This models the documented mathematical TMM procedure with the default
30% M / 5% A trimming, using the supplied implementations to make tie ranks,
quantile interpolation, and reference selection precise. The RNAnorm
procedure's A-trimming bullet repeats `m_trim`; its parameter documentation,
constructor default, and actual selection use `a_trim=0.05`, which is the
interpretation used here.

The checked library sizes are `[1261, 621, 755, 1097, 1916, 1136, 1219]`
(`Witness.lib0` through `lib6`). The checked normalized quartiles are
`[4/1261, 2/621, 2/755, 3/1097, 5/1916, 3/1136, 3/1219]`
(`Witness.q0` through `q6`), all far above the fallback threshold `1e-20`.

The model omits the `Acutoff=-1e10` test: each eligible count/library ratio
is at least `1/1916 > 1/2048`, so its base-2 logarithm is greater than -11.
Consequently every eligible A value is greater than -11, far above the
cutoff. The model correspondence, including
this inactive cutoff, is part of the review obligation, not a verified
translation of R or Python into Lean.

**There is no formal IEEE-754 model of R, NumPy, SciPy, sklearn, or their
logarithm libraries in this deliverable.** The exact-real rank rule can
select different genes from a floating-point evaluation near an exact tie.
Thus the interval table must not be presented as the result of executing
R or RNAnorm. R1/R2 are certified at the stated 0.025 tolerance against the
explicit mathematical specification; higher precision conformity to the
actual runtime implementations is supported only by the supplemental
reproduction checks below. No theorem asserts that either runtime is
correct on arbitrary input matrices.

### How the numerical proofs work

`Proofs/Bounds.lean` proves a rational logarithm enclosure from Mathlib's
`Real.sum_range_sub_log_div_le`. It uses 16 terms of the series with
`x=(q-1)/(q+1)` and remainder bound `2*|x|^33/(1-x^2)`. Powers of two reduce
large arguments to a small range. `Proofs/LogBounds.lean` contains checked
rational enclosures for the integer logarithms needed by this matrix.

Exact rational arithmetic determines the reference, tied ranks, selected
pairs, weights, and interval sums. The reference comparison's raw log
factor is proved exactly zero in `Proofs/SelfComparison.lean`. A general interval lemma encloses each
linear combination of logarithms. Finally, monotonicity of `log` and `exp`
proves each factor interval by enclosing the logarithms of its proposed
endpoints. Approximate host arithmetic proposes certificates; it never
establishes their acceptance. All finite calculations in the proofs are
kernel checked; no `sorry`, added axioms, `native_decide`, or `bv_decide`
is used.

## 2. Connection to the shipped bytes

FVA's `blob` command generated `Proofs/Counts.lean`, `Proofs/Edger.lean`, and
`Proofs/Rnanorm.lean`. Their packed numerals contain the following files,
including every tab, decimal digit, and final line feed:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

`Witness.counts_eq`, `Witness.edger_eq`, and `Witness.rnanorm_eq`, in
`Proofs/WitnessData.lean`, prove equality between each blob's entire byte
list and the mathematical data's encoding. They use FVA's verified byte
reader and a proven equivalent fast decimal printer. They are not hashes
or unchecked data imports. FVA's link check separately compares each blob
with the live file and verifies the generated module has not been edited.
Changing a shipped file without regenerating and re-proving the
certificates fails this link check.

The shipped matrix, output files, implementation sources, and README were
not modified. The R/Python sources serve as specification correspondence
and supplemental reproduction evidence; there is no claim that their
source code has been formally verified.

## 3. Rechecking

From this directory, with the installed Lean 4.35 / Mathlib v4.35.0 and
prebuilt FVA, run:

```sh
lake build
bash verification/check.sh
```

The first command must finish with `Build completed successfully`. The
second must exit 0 and print FVA's **PASS**, with all four claims proven,
all three byte links matching, and both default replay kernels accepting.
The script freezes a copy of the already-built FVA executable outside the
project *before* invoking its project build, copies its pinned dependency
manifest and canaries, runs `fva trust . --spec-module Proofs.Spec
--root-module Proofs --surface-budget 200`, and saves its full output in
`verification/fva-trust.txt`. A PASS certifies the four stated propositions;
it does not mean R3 holds. The proposition being proved for R3 is its
failure witness.

Optional supplemental checks:

```sh
sha256sum -c verification/artifacts.sha256
Rscript verification/reproduce-edger.R
python verification/reproduce-rnanorm.py
```

All three hash checks must say `OK`. The R check must print
`edgeR: exact byte reproduction PASS`. It directly sources the two shipped
R implementation files and compares the entire `%.17g` output with the
shipped file. The Python check must print
`RNAnorm NumPy reconstruction: exact byte reproduction PASS`. Because
SciPy/sklearn are not installed, this is an explicitly labelled
reconstruction using NumPy plus an average-rank implementation, not an
execution of the complete RNAnorm package. Both checks passed in this
environment. They are runtime evidence, not formal proofs of the runtimes.

The runtime checks find reference sample 4 in both cases. Their numbers of
retained genes illustrate the numerical rank issue:

| Sample | Exact mathematical ranks | Supplied edgeR R code | NumPy reconstruction |
| --- | ---: | ---: | ---: |
| 1 | 63 | 65 | 64 |
| 2 | 79 | 79 | 79 |
| 3 | 76 | 77 | 77 |
| 4 | 283 | 283 | 283 |
| 5 | 89 | 89 | 89 |
| 6 | 95 | 95 | 95 |
| 7 | 79 | 81 | 81 |

The runtime columns are diagnostic evidence. The formal counterexample to
R3 rests solely on exact decimal arithmetic and the bound output bytes.

To regenerate the untrusted proposed witnesses and numerical certificates:

```sh
python verification/generate.py
lake build
bash verification/check.sh
```

Regeneration is not required to check the delivered proofs. The generator
uses Python integers, fractions, and decimal approximations to propose
data and intervals; Lean checks the data encodings and every proposed
inequality independently.

## 4. Review and trust

The project-specific mathematical review surface consists of
`Proofs/Model.lean` (104 physical lines, 4634 bytes) and `Proofs/Spec.lean`
(42 physical lines, 1927 bytes). Read these together with the requirements
in `README.md`, `edgeR/man/calcNormFactors.Rd`, and the TMM documentation in
`rnanorm/between_sample.py`. The interpretation of those documents as the
explicit exact-real model and the choice of 0.025 tolerance are human
review obligations. In particular, accepting this coarse tolerance is
not evidence for a high precision scientific accuracy claim.

FVA reports **89 code lines** in the review surface: 64 in
`Proofs.Model` and 25 in `Proofs.Spec` (below the explicit budget of 200). Proofs, generated witness data, and proposed interval constants
need no correctness trust: the replay kernels check them against the
reviewed statements. `verification/generate.py` is an untrusted generator.
The 13-line `verification/check.sh` is orchestration that can be replaced
by the explicit `fva trust` invocation described above.

For the optional runtime results only, additionally trust R and its math
library plus the 21-line `verification/reproduce-edger.R`, or Python/NumPy
plus the 42-line `verification/reproduce-rnanorm.py`, respectively. These
scripts do not enter the formal proof's trusted base.

The source documents used in the correspondence review have these sizes:
`README.md`: 17 lines / 1642 bytes; `edgeR/man/calcNormFactors.Rd`: 122 lines /
7033 bytes; `rnanorm/between_sample.py`: 441 lines / 17490 bytes (the TMM class
starts at line 190). To review the implementation details used to resolve
the documentation, the two R files together are 352 lines / 12166 bytes;
`rnanorm/utils.py` is 54 lines / 1670 bytes. These are specification and
runtime-review inputs, not additional axioms of the Lean proofs.

FVA's reviewed-once `FVA/Spec` base comprises 23 Lean files, 3606 physical
lines / 161903 bytes. Its four `FVA/Trust` files comprise 887 lines / 40918
bytes; the report describes the glue and independent checks that use them.

The remaining trust is FVA's pinned specs and byte-link/export/canary glue,
the official Lean toolchain, pinned Mathlib and its standard axioms, and
the independent replay kernels. The full FVA report lists this boundary
and the accepted axiom sets: only `propext`, `Classical.choice`, and
`Quot.sound` occur in the four proofs. The canary report records Lean's
documented acceptance of the replaced-prelude canary; FVA guards that
assumption with its official-prelude check and the independent kernel
(`fva/trust/canaries/known.tsv`). Con-leche rejected 69 negative canaries,
declined three, and accepted none. No network service, compiler from R/Python to
WebAssembly, or source-execution assumption is needed for the formal
file-level results.
