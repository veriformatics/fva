# Verification of the shipped TMM factor files

**Overall result: the requirements do not all hold. R3 is false.** The input
counterexample is the shipped `counts.tsv`, and every pair of corresponding
values in the two shipped factor files disagrees by more than `10^-10`.

R1 and R2 have conservative, machine-checked numerical bounds against the
explicit ideal-arithmetic TMM model below. The tolerances are **absolute 0.023
for R1** and **absolute 0.021 for R2**. These are deliberately coarse bounds,
not evidence of high-precision agreement with mathematical TMM. Both files
also fail an absolute `0.001` tolerance against that model at sample 3.

## Statements and results

The claim definitions are in `Proofs/Spec.lean`. Their proofs are in
`Proofs/Proof.lean`; the exact theorem declarations are:

```lean
theorem Proofs.R1_holds : Proofs.R1
theorem Proofs.R2_holds : Proofs.R2
theorem Proofs.R3_failure_holds : Proofs.R3_failure
theorem Proofs.R1_tight_failure_holds : Proofs.R1_tight_failure
theorem Proofs.R2_tight_failure_holds : Proofs.R2_tight_failure
```

The claims expand to the following statements (all namespace prefixes shown):

```lean
FVA.Cert.Accepted (Proofs.Model.Conforms (23 / 1000))
  Proofs.Counts.blob Proofs.Edge.blob
FVA.Cert.Accepted (Proofs.Model.Conforms (21 / 1000))
  Proofs.Counts.blob Proofs.Rna.blob
FVA.Cert.Accepted Proofs.Model.Disagree
  Proofs.Edge.blob Proofs.Rna.blob
FVA.Cert.Accepted (Proofs.Model.FailsTight (1 / 1000))
  Proofs.Counts.blob Proofs.Edge.blob
FVA.Cert.Accepted (Proofs.Model.FailsTight (1 / 1000))
  Proofs.Counts.blob Proofs.Rna.blob
```

`Conforms t` says that the input bytes encode a 454-by-7 natural-number matrix,
the output bytes encode seven valid finite decimals, and **each** decimal
differs from its sample's ideal TMM factor by at most `t`. `FailsTight t`
binds the same bytes and asserts error strictly greater than `t` at sample 3.
See `Proofs/Model.lean` for their complete definitions, including the encodings.

`Disagree` binds both complete output files, validates all their decimal
digits, and proves both:

* the first edgeR value minus the first RNAnorm value is exactly
  `931142302732627 / 100000000000000000 = 0.00931142302732627`;
* for every sample index `j : Fin 7`, the absolute difference is strictly
  greater than `1 / 10000000000`.

For example, the first shipped values are `0.99099942459293067` and
`0.9816880015656044`. This disproves R3 independently of the TMM model,
logarithm approximations, producer languages, and interpretation of exact ties.
It also rules out equality after rounding to ten decimal places.

## Meaning and limits of the R1/R2 model

`Proofs.Model.factor` is an exact-real interpretation of the documented TMM
equations, using default trimming fractions 0.30 and 0.05, inverse binomial
variance weights, and geometric-mean centering. All-zero genes are removed;
library sizes include every count. The reference is the sample whose type-7
upper quartile divided by its library size is closest to the mean of those
quantities, with the first index winning ties. It is sample 4 for this input.
Library sizes are exactly `[1261, 621, 755, 1097, 1916, 1136, 1219]`.

RNAnorm's A-trimming procedure bullet says `m_trim`, whereas its parameter
documentation and source use `a_trim`. This model uses `a_trim = 0.05`, as in
the default constructor and actual trimming code; it does not formalize the
contradictory literal reading of that bullet.

M ranks use exact count ratios and A ranks use exact count products. These
give the same ranks as the documented logarithmic expressions over the reals,
since the omitted library-size terms are constant within each comparison.
Tied values receive average ranks, as in the supplied implementations' rank
calls. The model uses natural logarithms followed by `Real.exp`; the base-2
conversion cancels algebraically. The ordinary TMM branch is appropriate here:
upper quartiles are positive, and positive counts and these small library sizes
keep all A-values far above the default `-1e10` cutoff. The reference comparison
has zero log ratios. This is a model for this dataset, not a verification of
every branch or every input of either library.

The proof establishes these **closed rational enclosures** for the ideal
factors. They are the exact statements of `Proofs.factor_0` through
`Proofs.factor_6` in `Proofs/Evidence.lean`, using `Proofs.Data.counts` as the
matrix witness:

| Sample | Lower bound | Upper bound |
|---|---:|---:|
| 1 | 0.975526 | 0.975529 |
| 2 | 1.281082 | 1.281085 |
| 3 | 1.147753 | 1.147756 |
| 4 | 0.956410 | 0.956413 |
| 5 | 0.815784 | 0.815787 |
| 6 | 0.932436 | 0.932439 |
| 7 | 0.958279 | 0.958282 |

The table bounds are exact rationals with denominator `1000000`, not rounded
floating-point test results. For example, sample 3's two shipped values are
`1.1253076397204775` and `1.1270795948647565`; both are more than `0.001` below
its certified ideal lower bound. The selected R1/R2 tolerances must therefore
not be confused with a ten-decimal or similarly tight accuracy guarantee.

Exact ties matter on this small-count matrix. For example, genes 163 and 355
have sample-1/reference counts `(8,13)` and `(13,8)`, so both exact A-rank keys
are `104`. At a trimming boundary, rounding can split an exact tie and change
which genes contribute. The two source files evaluate A differently:
`(log2(p)+log2(q))/2` versus `log2(p*q)/2`. Rounded M values can split ties too.
The diagnostic retained-gene counts are `[63,79,76,283,89,95,79]` for exact
ranking; the floating-point transcriptions keep
`[65,79,77,283,89,95,81]` and `[64,79,77,283,89,95,81]` respectively.

**Unproved stronger interpretation:** these proofs do not certify execution
of R, NumPy, scipy, sklearn, or their logarithm routines. If R1/R2 are intended
to demand tight reproduction of the particular floating-point rank decisions
of those runtimes, that interpretation remains unproved. The formal results
are the stated model bounds and failures, not an unstated change of tolerance
or a claim that the two implementations are equivalent.

`verification/reproduce.py` is a separate diagnostic NumPy transcription that
preserves the two source evaluation orders. On NumPy 2.5.4 it reproduces all
seven binary64 values from each file with maximum absolute error `0.0`.
`verification/reproduction.json` records the result. It does not execute either
original package and is not used by any Lean proof.

## Connection to exact shipped bytes

`Proofs/Counts.lean`, `Proofs/Edge.lean`, and `Proofs/Rna.lean` were generated by
FVA's `blob` command. They contain the packed byte numerals and lengths for
`counts.tsv` (6518 bytes), `edger-factors.txt` (138 bytes), and
`rnanorm-factors.txt` (133 bytes). FVA checks each generated module against its
canonical printer and the actual file on disk. The three `*_bytes` theorems
in `Proofs/Proof.lean` also check that these blobs are exactly the matrix and
decimal encodings used by the proofs, including tabs, decimal digits, order,
and final newlines. There is no substitution of regenerated output files.

SHA-256 identities:

```text
aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5  counts.tsv
df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943  edger-factors.txt
62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d  rnanorm-factors.txt
```

`verification/inputs.sha256` additionally records the README, documentation,
producer scripts, and supplied implementation sources. Those sources were not
modified. The original outputs are the certificate subjects; no WebAssembly
artifact was introduced.

## Rechecking

From this directory, with the installed offline Lean/Mathlib environment:

```sh
bash verification/check.sh
```

The script checks all recorded input hashes, runs `lake build`, copies the
unchanged FVA package to a fresh directory under `/tmp`, links it to the
already-installed packages, and rebuilds its executable outside this project.
It then runs exactly:

```sh
"$tmm_checker_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --kernel-limit 1200
```

Success means exit status 0, a successful Lake build, and **`fva trust: PASS`**,
with the three blob links matching and successful Lean and independent kernel
replays. The report is saved in `verification/trust.txt`. A PASS certifies the
five statements above, including the failures; it does **not** mean that R3
holds. Any failed hash, build, link, axiom audit, or required replay is a failed
verification run.

Optional diagnostic and regeneration commands are:

```sh
python3 verification/reproduce.py
python3 verification/generate.py
python3 verification/evidence.py
lake build
```

Regeneration is unnecessary for checking the submitted proofs. The generators
use Python integer/rational arithmetic and decimal logarithms to suggest
witnesses; Lean rejects incorrect suggestions. They need no network.

## Review and trust boundary

FVA reports a project-specific semantic review surface of **95 code lines**:
82 in `Proofs.Model` and 13 in `Proofs.Spec`. Including comments and blank lines:

| File | Physical lines | Bytes | What must be reviewed |
|---|---:|---:|---|
| `Proofs/Model.lean` | 125 | 5302 | Byte encodings, exact TMM interpretation, conformance and failure relations |
| `Proofs/Spec.lean` | 31 | 1449 | The five claims, subjects, tolerances and caveats |
| **Total** | **156** | **6751** | Correspondence of these statements to the README and supplied documentation |

The proof files (`Bounds`, `LogChecks`, `Calc/*`, `Evidence`, `Proof`) and the
generated data are kernel checked, not additional mathematical assumptions.
In particular, `Bounds.log_nat` derives rational log enclosures from Mathlib's
finite logarithm-series bounds after power-of-two range reduction. Sixteen
terms and an explicit rational remainder bound are used. Weighted averages,
centering, and exponentiation bounds are proved sound. Numeric checks use
kernel reduction; no `sorry`, custom axiom, `native_decide`, or floating-point
oracle is used to establish a claim.

The Python generators and diagnostic script are untrusted helpers:
`generate.py` is 109 lines / 5132 bytes, `evidence.py` is 102 lines / 5966 bytes,
and `reproduce.py` is 60 lines / 2471 bytes. The shell script is 24 lines /
1051 bytes and orchestrates ordinary commands; inspect its command sequence or
run those commands directly. These sizes can be checked with:

```sh
wc -l -c verification/*.py verification/check.sh
```

FVA's existing base is also trusted as documented in `fva/AGENT.md`: its specs
(3606 physical lines under `fva/FVA/Spec`), fact collection, byte-link and source
checks, exporter and kernel orchestration. The six relevant glue modules
`Trust/{Collect,Replay,Canary}` and `Tool/{Trust,Blob,Pack}` total 1106 lines /
53601 bytes. Their sources remain identical to the supplied copy. Residual
trust includes the installed Lean 4.35.0 kernels and compiler, independent
kernel, pinned Mathlib v4.35.0, package/cache integrity, and the OS/tool process
boundary. FVA's canaries and independent replay reduce this trust; they do not
prove that the English requirements and this mathematical model are identical.

## Recorded verification run

On 2026-10-26, `bash verification/check.sh` completed with exit status **0**
and **`fva trust: PASS`**. The executable was independently rebuilt at
`/tmp/fva-tmm-check.80saXg/.lake/build/bin/fva`.

* `leanchecker` accepted the exported proof closure in 788 seconds.
* Independent `con-leche` accepted it in 548 seconds. The replays ran concurrently.
* All three blob links matched their files.
* Each claim's axiom closure contained only the standard `propext`,
  `Classical.choice`, and `Quot.sound`.

The canary results must also be stated: of 72 known-false exports, Lean's checker
rejected 71 and accepted one **documented known exception**, the replaced-prelude
canary listed in `fva/trust/canaries/known.tsv`. That ledger explains Lean's
assumption of the official prelude and the additional prelude/independent-kernel
guards. `con-leche` rejected 69, declined 3, and accepted none. Neither checker
crashed or timed out on a canary. Thus PASS does not mean that every canary was
rejected by every checker. The complete verdict, vocabulary, links and trust
boundary are saved in `verification/trust.txt`.
