# Verification

R1 and R2 are checked at **absolute tolerance 0.025 per factor**, against the
explicit real-arithmetic default-TMM interpretation below. This is a coarse
per-output guarantee, not a ten-decimal-place guarantee. **R3 fails** on the
shipped matrix and factor files: sample 1 differs by 0.00931142302732627.

## Statements and evidence

The claims are in `Proofs/Spec.lean`; R1/R2 proofs are in `Proofs/Proof.lean`
and R3 proofs are in `Proofs/Discrepancy.lean` (imported by the root proof).
Their exact theorem declarations are:

```lean
theorem r1_holds : r1
theorem r2_holds : r2
theorem r3_failure_holds : r3_failure
theorem r3_witness_holds : r3_witness
```

Here are the full claim definitions (names are in namespace `Proofs`):

```lean
def r1 : Prop :=
  FVA.Cert.Accepted (Model.Accurate (1 / 40)) Counts.blob Edge.blob

def r2 : Prop :=
  FVA.Cert.Accepted (Model.Accurate (1 / 40)) Counts.blob Rna.blob

def r3_failure : Prop :=
  ¬ FVA.Cert.Accepted (Model.Agree (1 / 10^10)) Edge.blob Rna.blob

def r3_witness : Prop :=
  (Model.factors Edge.blob.data)[0]? = some (99099942459293067 / 10^17 : ℚ) ∧
  (Model.factors Rna.blob.data)[0]? = some (9816880015656044 / 10^16 : ℚ) ∧
  |((Model.factors Edge.blob.data)[0]?.getD 0) -
    ((Model.factors Rna.blob.data)[0]?.getD 0)| > (9 / 1000 : ℚ)
```

`Accepted R i o` means `R i.data o.data`. `Model.Accurate eps input output`
requires seven parsed output factors, seven mathematical TMM factors, and
`|(output_j : ℝ) - tmm_j| ≤ eps` for every corresponding pair.
`Model.Agree eps a b` requires `|a_j - b_j| ≤ eps` for every pair of parsed
decimal rationals. Thus R3 is refuted without any approximation to logarithms,
any reliance on the numerical model, or execution of either implementation.
The first values also plainly differ when rounded to ten decimal places.

The counterexample input is the entire shipped `counts.tsv`, with sample order
unchanged. Its first output factors are exactly 0.99099942459293067 and
0.9816880015656044; their difference is exactly
931142302732627 / 100000000000000000.

## Meaning of the R1/R2 formalization

`Proofs/Model.lean` is the reviewed specification. It parses the actual TSV
counts as natural numbers and the actual positive decimal output lines as exact
rationals. It removes all-zero rows, sums columns for library sizes, uses the
linearly interpolated 75th percentile divided by library size to choose the
reference nearest the mean, and uses the first minimum. For this input the
reference is column 4, the library sizes are
`[1261, 621, 755, 1097, 1916, 1136, 1219]`, and every normalized upper quartile
exceeds 10^-20.
The edgeR zero-quartile fallback therefore does not apply.

Zero count pairs are excluded. M ranks are ranks of normalized count ratios;
A ranks are ranks of count products. Since logarithm is strictly increasing,
these are their real-arithmetic M/A ranks. Ties receive their average one-based
rank. The retained rank intervals are
`floor(0.3*n)+1 .. n-floor(0.3*n)` for M and
`floor(0.05*n)+1 .. n-floor(0.05*n)` for A. The inverse variance weight is
`1 / (1/obs + 1/ref - 1/lib_obs - 1/lib_ref)`.
The model computes the weighted mean of natural log ratios, subtracts the mean
across seven samples, and exponentiates. This is the base-independent form of
the documented base-2 calculation and geometric-mean rescaling. No positive
pair in this small matrix approaches edgeR's A cutoff of -10^10.

RNAnorm's docstring mentions `m_trim` in its A-trimming bullet, but explicitly
documents the separate `a_trim` parameter. The formalization uses the declared
defaults `m_trim=0.3`, `a_trim=0.05`, consistent with both implementations.

The model uses exact real arithmetic, **including exact ties**. It is not a
formal interpreter for R, NumPy, SciPy, or IEEE library logarithms. The shipped
implementations can split mathematical ties through rounding; the two A-value
expressions also have different evaluation orders. The 0.025 tolerance is chosen
to cover the observed departures from this exact-tie interpretation. It should
not be read as a proof that either output has small rounding error relative to
an exact mathematical algorithm. No tighter R1/R2 guarantee is claimed here.

For context only, approximate model factors are
`[0.97552770, 1.28108361, 1.14775497, 0.95641187, 0.81578573, 0.93243786, 0.95828078]`.
These displayed approximations are not premises of the proofs.

## How the proofs work

`Proofs/Raw.lean` contains untrusted generated witnesses and checked equalities;
`Proofs/Data.lean` assembles them into the full sample equality:
`rows_eq` links the parsed counts to the complete literal matrix; `uq0` through
`uq6` and `ref_eq` check reference selection; `e0_eq` through `e6_eq` and `es_eq`
check all retained genes, ratios, and weights. The retained counts in exact
arithmetic are `[63,79,76,283,89,95,79]`.

`Proofs/Bounds.lean` proves a general analytical bound for `Real.log q` using
four terms of the atanh series at `z=(q-1)/(q+1)`, with remainder bound
`2*|z|^9/(1-z^2)`. It proves weighted-sum, centering, and exponential comparison
lemmas. `Data.bounds0` through `Data.bounds6` kernel-check rational log-score
intervals. `score_certificate` assembles them, and `accurate_of_bounds` converts
them to the seven real error inequalities in each claim. Computations use
kernel reflection (`kernel_rfl` or `decide +kernel`), not `native_decide` or
`bv_decide`. The generator's arithmetic and printed estimates are not trusted.

## Exact artifact binding

FVA-generated `Proofs/Counts.lean`, `Proofs/Edge.lean`, and `Proofs/Rna.lean`
embed all bytes, including tabs and final newlines, as packed numerals with
lengths and project-relative source paths. FVA's link audit compares these
numerals and lengths against the files and checks that the generated modules
are unchanged generator output. There is no compiled Wasm subject: the README
names the two text outputs as the artifacts, so these are FVA per-output
certificates.

| File | Bytes | SHA-256 |
|---|---:|---|
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

The R and Python source files are context for interpreting the requirements;
there is no theorem verifying their behavior on arbitrary inputs.

## Rechecking from this directory

No network is needed. Use the installed Lean 4.35.0 toolchain and existing
Mathlib/FVA builds:

```sh
bash verification/check.sh
```

The script runs `lake build`, then invokes an unchanged separate copy of the
supplied prebuilt FVA outside this project:

```sh
FVA_BINARY trust . --spec-module Proofs.Spec --root-module Proofs \
  --surface-budget 150 --json
```

Success is exit code 0 and `fva trust: PASS`. The full report is written to
`verification/trust.json`. PASS certifies the four statements above, including
the **failure** statement for R3; it does not mean all README requirements hold.
The audit includes artifact links, axiom checks, kernel replay, and known-false
kernel canaries.

Delivery run (2026-10-26): `lake build` and `bash verification/check.sh` both
exited 0; FVA returned **PASS**, with no issues or override flags. All three blob
links passed. Both `leanchecker` and `con-leche` accepted the export (the latter
reported 26,498 declarations in verified mode). The four proofs use only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The review surface
is **81 code lines**: 17 in `Proofs.Spec` and 64 in `Proofs.Model`.

The 72 known-false canaries produced 144 runs. As recorded in FVA's pinned known
acceptances, `leanchecker` accepted the replaced-prelude canary; `con-leche`
rejected it. `con-leche` declined three other canaries, all rejected by
`leanchecker`. There were no unknown canary acceptances. PASS uses FVA's rule
that a pinned known acceptance must be covered by another checker's rejection;
it does not assert that every checker rejected every canary.

Optional supplemental numerical checks:

```sh
Rscript verification/reproduce.R
python3 verification/reproduce.py
```

Success reports an exact byte match for edgeR and all errors below `1e-14` for
the NumPy transcription. The latter currently has maximum error zero. It is
a transcription of the numerical equations and default average ranks, not an
execution of the full RNAnorm package: SciPy/scikit-learn are unavailable.
These checks depend on the installed runtimes and numerical libraries and are
not used by the formal proofs. They never overwrite the shipped outputs.

To regenerate the untrusted concrete witnesses, optionally run
`python3 verification/generate.py`, then rerun the full check. This is unnecessary
for checking the delivered proof files.

## Review and trust

Read `Proofs/Spec.lean` and `Proofs/Model.lean` to judge whether the claims,
tolerance, parsing, and exact-arithmetic interpretation match the intended
requirements. Together they have 131 physical lines / 5670 bytes. FVA's
81-code-line review surface excludes comments and whitespace. The input is
specialized to seven samples; no generality to
other matrix shapes is claimed.

The proof files, generated witnesses, and Python generator need not be trusted:
the kernels check their conclusions. The optional reproduction scripts are
outside that proof chain (520 bytes R and 1662 bytes Python).

The remaining trusted base is FVA's pinned specification and trust machinery,
its file/link and export glue, the supplied toolchain and pinned Mathlib, and
the operating system/filesystem executing the checks. FVA cross-checks Lean's
kernel with the independent `con-leche` kernel and tests both on known-false
canaries. The separate checker is a copy of the supplied prebuilt binary, not
an independently obtained distribution; no vendored FVA source was modified.

For inherited-base size context, all 23 files under `fva/FVA/Spec/` total 3606
physical lines / 161903 bytes (a superset of the specification needed here).
The collection/link/export/canary glue in `FVA/Trust/{Collect,Replay,Canary}`,
`FVA/Tool/{Trust,Blob,Pack,BaseManifest}`, and `FVA/Lifted` totals 1404 physical
lines / 68979 bytes. The OS, Lean/compiler/kernel binaries, independent checker,
and pinned Mathlib are inherited infrastructure, not a newly verified part of
this project. `verification/check.sh` is 24 lines / 836 bytes; its exit-code and
JSON assertions are just orchestration, and the equivalent FVA command is above.
