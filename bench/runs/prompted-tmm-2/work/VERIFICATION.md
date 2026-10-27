# Verification of the shipped TMM factor files

The unconditional finding for the shipped factor files is **R3 fails**. The first factors differ by exactly
`0.00931142302732627`, far more than `1e-10`.

There is an important semantic distinction for R1 and R2. At absolute tolerance
`1e-10`, **both files fail exact mathematical TMM with average ranks for ties**,
formalized below. In contrast, executing the supplied edgeR source reproduces
all seven edgeR values with maximum absolute error **0** (checked at tolerance
`1e-14`). These statements concern different arithmetic semantics; the latter
is not a proof of accuracy relative to exact mathematical TMM.

The documentation does not give a floating-point operational specification.
This report does not claim that the supplied edgeR program fails to produce its
own output. Nor does it claim to have verified the Python interpreter and its
missing SciPy/scikit-learn dependencies. The proofs concern the two output files,
which README explicitly identifies as the verification targets; source files
and output files have not been changed.

## Check everything

From this directory, without network access:

```sh
python3 verification/check.py
```

Success ends with `ALL CHECKS PASSED: mathematical counterexamples and R3 failure
verified; both kernels reject the forgery.` It means that the verification
succeeded, **not** that all README requirements hold. Every subprocess must
succeed, except the deliberately false proof, which each checker must reject
for a type mismatch. Logs, exported proofs, and size information are written
under `verification/out/`.

The command checks input hashes and byte bindings, removes the project's build
cache (not the prebuilt package caches), rebuilds Lean proofs, exports their
complete dependency closures, checks them from an empty environment with Lean's
C++ kernel and with Nanoda's independent Rust kernel, runs positive and negative
controls, and executes the unchanged R implementation. It requires the supplied
Lean/Mathlib installation, `leanexport`, `leanchecker`, `nanoda_bin`, Python 3,
and R. The installed `lean4lean` could not read this Lean installation's object
file header and is **not counted as a successful checker**.

## Formal interpretation and results

The mathematical specification is `Proofs/Spec.lean`. It uses column sums as
library sizes, removes zero count pairs, selects sample 4 (one-based) by the
closest-to-mean normalized 75th percentile, trims each tail by 30% for M and 5%
for A with average ranks for ties, uses inverse asymptotic binomial variances,
and rescales the seven factors to geometric mean 1. Natural logarithms replace
log base 2 because the change of base cancels in the weighted log factor.
M ordering uses exact `obs/ref` ratios and A ordering exact `obs*ref` products;
positive library-size constants and logarithms preserve those orders.

The type-7 quartile is computed using zero-based order statistics and linear
interpolation. Order statistics are defined by cumulative counts, avoiding a
trusted external sort. All 454 rows have seven entries and a positive row sum.
The default A cutoff cannot remove any positive pair: `TMM.cutoff_irrelevant`
proves the actual log-base-2 A values exceed `-1e10` for every such pair.

RNAnorm's docstring has a typo: its A-trimming bullet says `m_trim`, while its
parameter documentation and default constructor specify `a_trim = 0.05`.
The formalization uses the latter, consistent with both supplied implementations.
It does not silently certify the conflicting literal reading of that bullet.
Ties and the arithmetic domain are explicit parts of this formal interpretation.
RNAnorm scales its upper-quartile factors by a common positive geometric mean;
this cannot change the index closest to their mean.

### R1

`Proofs/Results.lean` contains the exact theorem:

```lean
theorem R1_exact_counterexample :
    (1/1000 : ℝ) < |(Artifact.edge[0]! : ℝ) / 10^17 - factor counts 0 3|
```

Here `factor`, `counts`, and the theorem are in namespace `TMM`. Sample indices
are zero-based. The witness is the supplied `counts.tsv`, sample 1, with shipped
factor `0.99099942459293067`. `TMM.first_factor_upper` proves its exact TMM factor
is strictly less than `977/1000`. The error therefore exceeds `0.001`, and in
particular exceeds the stated tolerance `1e-10`.

Separately, `verification/replay.R` sources the actual supplied R files and
checks every shipped factor against `normLibSizes(x, method="TMM")`, with
absolute tolerance `1e-14`. This is a machine-checked execution result in R,
not a kernel proof of R semantics or a mathematical accuracy theorem.
Floating-point ranking of logarithms can split ties that exact rational ranking
preserves. Thus reproduction of the source's rounded computation does not
establish R1 under the exact mathematical specification.

### R2

`Proofs/Results.lean` contains:

```lean
theorem R2_exact_counterexample :
    (1/1000 : ℝ) < |(Artifact.rna[0]! : ℝ) / 10^17 - factor counts 0 3|
```

The witness is again the supplied matrix and sample 1, with shipped factor
`0.9816880015656044`. The same certified upper bound `977/1000` establishes an
error greater than `0.001`, hence failure at tolerance `1e-10`, for the stated
mathematical interpretation. No rewritten Python implementation or replacement
dependency is used as evidence. Reproduction by the full RNAnorm runtime is
**not proved or tested**: SciPy and scikit-learn are unavailable offline.

### R3

`Proofs/Artifact.lean` contains these exact statements in namespace `Artifact`:

```lean
theorem edge_bytes : parse edgeBytes = some edge
theorem rna_bytes : parse rnaBytes = some rna
theorem first_gap : edge[0]! - rna[0]! = 931142302732627
theorem R3_false : ¬ (∀ i : Fin 7, distance edge[i.val]! rna[i.val]! ≤ 10^7)
theorem different_truncated_10 : edge[0]! / 10^7 ≠ rna[0]! / 10^7
theorem different_rounded_10 :
    (edge[0]! + 5*10^6) / 10^7 ≠ (rna[0]! + 5*10^6) / 10^7
```

`edge` and `rna` are integer values in units of `10^-17`; `distance a b` is
`(a-b)+(b-a)` on natural numbers. Therefore `10^7` units is exactly `1e-10`.
The false universal statement requires just the first sample as a witness.
The two additional theorems reject equality of the first factors after either
truncation or nearest rounding to ten fractional decimal places. R3's failure
does not depend on any interpretation of TMM, reference selection, or ties.

Supporting public results are:

- `TMM.matrix_shape` and `TMM.quartiles` in `Proofs/Quartiles.lean` check the
  matrix shape, absence of all-zero rows, and quartiles `[4,2,2,3,5,3,3]`.
- `TMM.reference_correct : referenceOK counts 3` in that file checks reference
  selection against all seven samples.
- `TMM.cutoff_irrelevant` in `Proofs/Cutoff.lean` discharges the default cutoff.
- `TMM.first_factor_upper : factor counts 0 3 < (977/1000 : ℝ)` is the common
  analytic bound used for R1 and R2.

## Artifact linkage and proof construction

`verification/inputs.json` pins the SHA-256 digests of the original matrix,
both factor files, both supplied producer scripts, implementation sources,
documentation, README, CHECK, and license/version files. Hash checks alone are
not the logical linkage: `verification/check.py` additionally reconstructs the
factor files **byte for byte** from the ASCII line lists `Artifact.edgeBytes`
and `Artifact.rnaBytes`, and reconstructs `counts.tsv` **byte for byte** from
`TMM.counts` in `Proofs/DataBase.lean`. Each reconstruction includes every tab,
decimal character, line order, and final LF. The kernel checks decimal parsing
and the equality of the resulting integers to the factors used in the theorems.

The remaining data and certificates are untrusted proof inputs. `Proofs/Data0.lean`
through `Data6.lean` prove the positive pairs and retained pairs equal the
specification's computations on `counts`. `Proofs/Computation.lean` proves the
weighted logarithm sums equal compressed sums. `Proofs/Bounds.lean` proves a
rational enclosure method using Mathlib's logarithm series remainder theorem.
`Proofs/LogCertificates.lean` and `MeanCertificates.lean` instantiate it with
rational bounds. No floating-point computation, `native_decide`, `sorry`,
compiler-trust axiom, externally asserted numeric result, or certificate
producer is trusted in these proofs.

## Independent checking and false-proof controls

The exported NDJSON includes the proof bodies and every transitive dependency.
`leanchecker --from-export` reconstructs an empty Lean kernel environment;
Nanoda independently parses and typechecks the same closure. The only permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Nanoda is configured
to fail on every other axiom, including `sorryAx` and `Lean.trustCompiler`.
`verification/Audit.lean` also prints the axiom dependencies of the main results.

`verification/Positive.lean` proves `True` and must be accepted by both kernels.
`verification/Reject.lean` deliberately bypasses the elaborator's kernel check
solely to manufacture two false proofs: `KnownFalse : False` with body
`True.intro`, and `KnownFalseArithmetic : (0 : Nat) = 1` with body `Eq.refl 0`.
This fixture is isolated from the library and never imported by a real proof.
Each theorem exports separately and successfully, then Lean must reject each
one with `declaration type mismatch` and Nanoda must reject it at its
definitional-equality type check. The runner fails
if either checker accepts either false proof, or rejects for an unrelated
parsing/setup error.
This tests actual kernel rejection of a well-formed but false proof, rather
than just a tactic's inability to find a proof.

## Review surface and limitations

The project-specific review surface is deliberately separated from proof bulk:

| Material | Physical lines | Bytes | What to review |
|---|---:|---:|---|
| `Spec.lean` + `Artifact.lean` | 88 | 5,309 | Mathematical TMM definitions, decimal interpretation, and R3 statements; this whole-file count also includes their proof bodies/data. |
| These plus `Results.lean`, `Reference.lean`, `Quartiles.lean`, `Cutoff.lean` | 230 | 11,226 | Conservative whole-file budget covering all public statements and their new semantic definitions, except the separately bound matrix literal. |
| Matrix literal in `DataBase.lean` | 1 literal | 7,427 | 3,178 integer cells; checked against the input bytes rather than manually transcribed/trusted. |
| `verification/check.py` | 99 | 5,473 | Byte binding, clean build, export, checker invocation, and control enforcement. |
| `verification/replay.R` | 10 | 537 | The separate R execution claim. |
| `verification/footprint.py` | 84 | 3,331 | Size-reporting logic only; not trusted for mathematical truth. |
| Positive/negative Lean fixtures | 17 | 504 | The valid control and two deliberate false proofs. |
| `verification/Audit.lean` | 8 | 270 | Axiom audit commands. |

`verification/inputs.json` is a 16-line, 1,283-byte snapshot manifest. All 26 Lean,
Python, and R verification source files together contain **1,323 physical lines,
116,174 bytes**, including generated certificates and data. These totals exclude
this report, the snapshot manifest, the original software/data, and generated
build/export/log files. Certificate generators are not needed or trusted: the
provided proofs are rebuilt and their exported proof terms are independently
replayed.

For the full unfolded statement/definition closure, the measured inventory is
**2,100 declarations, 50,327 expression nodes, 2,177,815 bytes of expression JSON**.
It includes **938 definitions and 12 opaque definitions**, along with inductive
packages and types of referenced proof constants. There are 24 project constant
names in this closure, including one generated proof constant. The names and
counts are in `verification/out/footprint.json`; the expression-byte metric
excludes name/universe encoding and is not the size of the proof export.
The collector conservatively includes entire referenced inductive packages.

The much larger proof dependency closure contains **28,219 declarations**; both
kernels checked it successfully. Nanoda's log also reports one pretty-printer
error, `Unable to print axioms`, alongside **no typechecker errors** and exit
status 0. This diagnostic concerns printing, not proof acceptance. Both negative
controls separately exit nonzero at its type-equality assertion, as required.
The successful end-to-end transcript is in `verification/out/`.


The small project-specific semantic surface does not eliminate standard
mathematical foundations: a reviewer must also accept the meaning of Lean's
logic, natural/rational/real numbers, logarithm and exponential definitions,
and the ordinary axioms listed above. The footprint report follows every
transitively referenced definition, opaque definition body, and inductive
rule from theorem **types**, while excluding theorem proof bodies. Its full
name list makes the larger standard-library surface visible rather than
pretending that an import is free. Auxiliary proof definitions are not part
of the interpretation of the final mathematical statements, but their proofs
and dependencies are still replayed by both kernels.

The byte-binding and orchestration code, Python/OS file I/O, kernel binaries,
and export transport remain trusted infrastructure. The R replay additionally
trusts R and its numeric runtime. These are finite, fixed-input results; there
is no theorem about every input to either library. If R1/R2 are intended to
specify each library's exact floating-point operational behavior rather than
mathematical TMM, the R replay is the narrower positive result available for R1,
and R2 under that interpretation remains unverified. R3 is disproved either way.
