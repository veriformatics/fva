# Verification

The two supplied factor files **disagree**, so R3 fails. R1 and R2 are also
refuted at absolute tolerance **10^-10** under the exact mathematical TMM
interpretation described below. These latter results distinguish the documented
formula from its floating-point implementation: they do **not** prove that the
files were produced incorrectly by the supplied R/Python programs.

## Statements and evidence

All indices in Lean are zero based; sample numbers here start at one.
The three certificate statements are in `Proofs/Spec.lean`, and their proofs
are in `Proofs/Proof.lean`:

```lean
theorem Proofs.R1_failure_holds : Proofs.R1_failure
theorem Proofs.R2_failure_holds : Proofs.R2_failure
theorem Proofs.R3_failure_holds : Proofs.R3_failure
```

Their exact definitions are:

```lean
def R1_failure : Prop :=
  FVA.Cert.Accepted TMM.RejectsDefaultTMM Counts.blob Edger.blob

def R2_failure : Prop :=
  FVA.Cert.Accepted TMM.RejectsDefaultTMM Counts.blob RNAnorm.blob

def R3_failure : Prop :=
  FVA.Cert.Accepted TMM.Disagree Edger.blob RNAnorm.blob
```

`FVA.Cert.Accepted R i o` means `R i.data o.data`. The complete relations,
including valid decimal scales and the file encodings, are in `Proofs/Model.lean`.

| Requirement | Machine-checked result |
| --- | --- |
| R1 | On the exact `counts.tsv`, at least one of edgeR's sample-3 and sample-4 outputs differs from exact default TMM by more than 10^-10, for **every positive common normalization divisor**. |
| R2 | The same counterexample holds for the RNAnorm outputs. |
| R3 | The first decimal values in the two exact output files differ by more than 10^-10. This result needs no TMM model. |

For R1/R2 the input is the entire shipped 454-by-7 matrix. Checked library
sizes are `[1261, 621, 755, 1097, 1916, 1136, 1219]`; sample 4 is the unique
reference selected by the mean upper-quartile criterion. Sample 3 has 205
positive pairs with the reference. Exact average ranks and the default trimming
retain 76 pairs. If

```
W = sum(weight * ln((observed/755)/(reference/1097))) / sum(weight),
weight = 1 / ((1/observed - 1/755) + (1/reference - 1/1097)),
```

on those retained pairs, the checked supporting theorems are:

```lean
theorem Proofs.mean_gt : (177/1000 : ℝ) < TMM.meanLog Proofs.matrix 2 3
theorem Proofs.rawFactor_gt :
  (119/100 : ℝ) < Real.exp (TMM.meanLog Proofs.matrix 2 3)
```

The reference's raw factor is 1. Thus any positive common normalizer requires
`factor[3] > 1.19 * factor[4]`. However, the supplied values are:

| File | Sample 3 | Sample 4 |
| --- | --- | --- |
| `edger-factors.txt` | 1.1253076397204775 | 0.95358597286325431 |
| `rnanorm-factors.txt` | 1.1270795948647565 | 0.9550875280917844 |

Both pairs satisfy the checked strict inequality
`output[3] + 10^-10 < 1.19 * (output[4] - 10^-10)`
(`Proofs.edger_gap`, `Proofs.rnanorm_gap`). It is impossible for both
coordinates to be within the tolerance. The proof needs neither the other
five weighted means nor a numerical estimate of the geometric mean.

For R3 the counterexample is sample 1:

```
edgeR:    0.99099942459293067
RNAnorm:  0.9816880015656044
absolute difference = 0.00931142302732627 > 0.0000000001
```

These are exact decimal/rational comparisons, not binary floating-point tests.
They also round differently to ten places: 0.9909994246 versus 0.9816880016.

## Meaning of the TMM model and limits

`Proofs/Model.lean` formalizes unsigned count matrices; removal of all-zero
rows for upper-quartile selection; the default interpolated 75th percentile;
a unique reference closest to the mean normalized quartile; exclusion of
zero-count pairs; exact average ranks; removal of floor(0.3*n) observations
from each M tail and floor(0.05*n) from each A tail by rank cutoffs; inverse
binomial-variance weighting; and the exponential of the weighted log mean.
It rejects **any** common positive divisor, which includes normalization by
the geometric mean. Natural logs replace log2 in the weighted mean and exp
replaces 2-to-the-power; this is the same mathematical raw factor. M ranks
are computed from count ratios and A ranks from count products, which avoids
rounding logarithms before ranking.

The edgeR manual specifies the reference rule, inverse-variance weighting,
zero exclusion and product-one rescaling. Defaults and average-rank boundary
handling are resolved using `edgeR/R/calcNormFactors.R`'s `.calcFactorTMM`
and `edgeR/R/normLibSizes.R`. RNAnorm's `TMM` docstring and its corresponding
methods supply the same mathematical interpretation. Its UQ rescaling before
reference selection multiplies every quartile and its mean by the same
positive constant, preserving the unique closest sample. The docstring's A
bullet repeats `m_trim`; the documented `a_trim` parameter and implementation
resolve this as the default 0.05 A trimming.

This is an explicitly reviewed **exact-real model**, not a formal semantics
of R, NumPy, SciPy, libm, or the supplied producer programs. Agreement with
those programs' floating-point execution remains unproved. If R1/R2 are
instead interpreted as agreement with those particular floating-point
executions, the counterexamples do not settle that interpretation; no such
conformance proof is claimed. The (10^{-10}) tolerance is absolute and is
chosen to match the precision scale in R3.

The distinction matters on this matrix. Gene 451 has counts (5,10) for
sample 3 and reference sample 4. Its exact M rank is 57, below the retained
lower cutoff 62. A supplementary NumPy calculation splits equal mathematical
ratios by floating-point rounding and gives this gene rank 67, retaining it.
Different floating-point A formulas also split boundary ties differently
between the two implementations. `verification/diagnose.py` illustrates this
and reproduces the supplied vectors to ordinary floating-point accuracy;
this script is diagnostic evidence, not part of the proof.

Additional Lean-checked statements in `Proofs/Conditions.lean` establish the
inactive A cutoff, the reference raw factor of 1, the pair counts, gene 451's
counts, and its exact doubled rank of 114. The generic bound
`TMM.log2_lower` proves positive counts in libraries of size at most 2000
have log2 expression greater than -4000, so the A cutoff -10^10 removes none.
These supporting statements are checked by `lake build`; the FVA certificate
roots are the three main theorems above.

## Binding to the shipped files

FVA's unedited generated blob modules are `Proofs/Counts.lean`,
`Proofs/Edger.lean` and `Proofs/RNAnorm.lean`. They contain the complete
bytes, byte counts and relative source paths. FVA compares them with the
files on disk and checks the generated module layout. No hash-only assumption or unverified manually entered vector substitutes
for a file.

`Proofs/Data.lean` proves that these blob bytes equal the model's TSV/decimal
renderings. Therefore the matrix, all seven decimal factors, sample order,
separators and final newlines are bound to the shipped bytes. Its rank and
quartile calculations use kernel reduction, never `native_decide`.
`Proofs/LogBounds.lean` derives rational lower bounds for real logarithms
from proved elementary logarithm inequalities. An exact rational power
comparison bounds ln(1.19) from above; no libm result is assumed.

Original file identities (SHA-256, supplied for identification; FVA checks
full byte equality):

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

## Rechecking offline

From this directory, using the installed Lean 4.35.0 and built Mathlib:

```sh
bash verification/check.sh
```

The script runs `lake build`, copies the supplied unmodified FVA package to
a fresh directory under `/tmp`, points that copy at the already installed
packages, rebuilds its executable outside this project, and runs:

```sh
/path/to/external/fva trust . --spec-module Proofs.Spec --root-module Proofs
```

Success means the shell command exits 0, Lake reports a successful build,
and FVA reports `PASS` for all three **failure certificates**. A PASS verifies
the counterexamples, not satisfaction of the README requirements. FVA checks
the axiom closure, artifact links, review surface, independent kernel replay
and false-theorem canaries. `verification/trust.txt` records the performed
run. The completed run returned **`fva trust: PASS`**, with Lean's checker
accepting in 341 seconds and con-leche accepting in 340 seconds. All three
blob links matched. FVA counted **82 reviewed code lines**: 12 in the claim
module and 70 in the model. A clean proof build includes substantial kernel
evaluation and may take several minutes.

The 72 known-false canaries produced 71 rejections and one known acceptance
in Lean's checker; con-leche rejected 69 and declined three, accepting none.
The known acceptance is the replaced-prelude case recorded in FVA's supplied
`trust/canaries/known.tsv`; FVA combines its official-prelude check with the
independent kernel. The certificate axiom closures contain only the standard
`propext`, `Classical.choice`, and `Quot.sound`. These are the actual recorded
trust results, rather than a claim that every kernel rejected every canary.

Optional regeneration/diagnosis commands:

```sh
python verification/generate.py
lake build
python verification/diagnose.py
```

The generator writes only `Proofs/Data.lean`; its proposed matrix and
intermediate results must still pass all Lean proofs. The diagnostic script
requires installed NumPy. Neither script modifies a shipped input/output.

## Review and trust

A reviewer must read the claim definitions and mathematical relation, and
compare that formalization with the local requirements/documentation. The
project's semantic review surface is `Proofs/Model.lean` (114 physical lines,
5312 bytes) and `Proofs/Spec.lean` (25 physical lines, 982 bytes).
`verification/check.sh` is 24 lines / 1011 bytes of reproducibility glue.
The original `README.md` is 17 lines / 1642 bytes; the edgeR manual is
122 lines / 7033 bytes. Relevant source defaults/rank conventions are in
`normLibSizes.R` (99 lines / 3950 bytes), `calcNormFactors.R` (253 lines /
8216 bytes), and RNAnorm's `between_sample.py` (441 lines / 17490 bytes;
TMM occupies lines 190–388).

The proofs, generated data, generator and diagnostic script do not need to
be trusted for the three certificate propositions: the kernel checks the
proofs and FVA checks blob linkage. The supporting Conditions theorems are
also checked by Lean. Residual trust includes the meaning of the reviewed
model relative to the prose, FVA's pinned specifications and trust-checking
glue, the installed Lean toolchain/kernels, and Mathlib at the pinned
v4.35.0 revision (`56a005855ea17e0b0958f73ec801ae140b0a1679`).
The supplied FVA specification directory has 23 Lean files, 3606 physical
lines / 161903 bytes. Its relevant audit glue (`Tool/Trust`, `Tool/Blob`,
`Tool/Pack`, `Trust/Collect`, `Trust/Replay`, `Trust/Canary`) has 1106 lines /
53601 bytes across six files. These are the supplied FVA base, reviewed once,
not new project definitions. There are no added axioms, `sorry`, or
native-decision axioms in the certificates.
