# Verification of the shipped TMM factors

The chosen accuracy tolerance is **absolute error ≤ 10⁻¹⁰ per factor**.

**R3 is false on the shipped bytes.** For R1 and R2, the proofs below give
counterexamples under an explicit exact-real interpretation of the documented
TMM calculation. They do **not** establish failure to reproduce the R or NumPy
floating point implementations. That distinction matters on this matrix.

## Results and exact theorem statements

All three requirement theorems are in [Proofs/Proof.lean](Proofs/Proof.lean).
Their exact statements, with namespace qualification, are:

```lean
theorem Proofs.R1_failure_holds : Proofs.R1_failure
theorem Proofs.R2_failure_holds : Proofs.R2_failure
theorem Proofs.R3_failure_holds : Proofs.R3_failure
```

The propositions are defined in [Proofs/Spec.lean](Proofs/Spec.lean), reproduced
below without their docstrings. Names are interpreted in namespace `Proofs`.

```lean
def R1_failure : Prop :=
  ∃ (xs : Matrix) (ds : List Decimal),
    Counts.blob.data = countBytes xs ∧ Edge.blob.data = factorBytes ds ∧
    xs.length = 454 ∧ (∀ row ∈ xs, row.length = 7) ∧ ds.length = 7 ∧
    reference xs = 3 ∧
    (decimalValue (ds[2]?.getD (0,0)) : ℝ) + 1/100 < factor xs 2

def R2_failure : Prop :=
  ∃ (xs : Matrix) (ds : List Decimal),
    Counts.blob.data = countBytes xs ∧ RNA.blob.data = factorBytes ds ∧
    xs.length = 454 ∧ (∀ row ∈ xs, row.length = 7) ∧ ds.length = 7 ∧
    reference xs = 3 ∧
    (decimalValue (ds[2]?.getD (0,0)) : ℝ) + 1/100 < factor xs 2

def R3_failure : Prop :=
  ∃ es rs : List Decimal,
    Edge.blob.data = factorBytes es ∧ RNA.blob.data = factorBytes rs ∧
    es.length = 7 ∧ rs.length = 7 ∧
    (∀ i ∈ List.range 7,
      1/10000000000 < |decimalValue (es[i]?.getD (0,0)) -
        decimalValue (rs[i]?.getD (0,0))|) ∧
    9/1000 < |decimalValue (es[0]?.getD (0,0)) - decimalValue (rs[0]?.getD (0,0))|
```

| Requirement | Machine-checked result | Concrete witness |
| --- | --- | --- |
| R1 | Under `Proofs.factor`, sample 3's shipped edgeR factor is more than `0.01` below the mathematical factor, hence fails the stated tolerance. | `counts.tsv`, sample 3: shipped `1.1253076397204775`; proven mathematical factor `> 1.14`. |
| R2 | Under the same mathematical TMM model, sample 3's shipped RNAnorm factor is more than `0.01` below the mathematical factor, hence fails the stated tolerance. | Same matrix and sample: shipped `1.1270795948647565`; proven mathematical factor `> 1.14`. |
| R3 | Every corresponding pair of shipped decimals differs by more than `10⁻¹⁰`. Sample 1 differs by more than `0.009`. This result is independent of the TMM model. | Sample 1: `0.99099942459293067` versus `0.9816880015656044`; exact difference `0.00931142302732627`. |

A single failing sample suffices to refute each universal per-sample accuracy
requirement. No assertion of agreement for the other samples is needed.

The key numerical theorem in [Proofs/ScoreData.lean](Proofs/ScoreData.lean) is:

```lean
theorem Proofs.factor_lower : (114/100 : ℝ) < Proofs.factor Proofs.matrix 2
```

`Proofs.matrix` is an untrusted printed witness whose full byte encoding is
proved equal to `Counts.blob.data`; it is not an assumed replacement input.
Indices in Lean are zero based, so index `2` is sample 3 and reference `3` is
sample 4.

## Meaning of the mathematical model

[Proofs/Model.lean](Proofs/Model.lean) defines the reviewed mathematical relation.
Both documented TMM procedures are interpreted as follows:

1. Sum each count column for its library size. Remove all-zero genes for reference
   selection. Compute the default linearly interpolated 75th percentiles and
   choose the first normalized quartile closest to their mean.
2. In each sample/reference comparison, retain positive count pairs. Rank M by
   the exact rational count ratio and A by the exact count product. These are
   their orders under exact logarithms. Assign **average ranks to exact ties**,
   as the supplied sources' `rank`/`rankdata` defaults do.
3. Use inclusive rank bounds with `floor(0.3*n)+1` and `floor(0.05*n)+1`, and the
   corresponding upper bounds. Use inverse asymptotic binomial variance weights.
4. Compute the weighted mean of natural log ratios. Exponentiate after subtracting
   the mean of the seven log scores. This is equivalent in exact arithmetic to
   base-2 log ratios followed by base-2 exponentiation and geometric centering.

The library sizes are `[1261, 621, 755, 1097, 1916, 1136, 1219]`. The selected
reference is sample 4. The exact-rank retained-pair counts are
`[63, 79, 76, 283, 89, 95, 79]`. These are checked in
[Proofs/Witness.lean](Proofs/Witness.lean), not accepted from Python.

The model is specialized to seven columns, and the claim checks that the actual
matrix has exactly 454 rows of seven entries. The reference quartiles are checked
exactly as `[4/1261, 2/621, 2/755, 3/1097, 5/1916, 3/1136, 3/1219]`.
[Proofs/Interpretation.lean](Proofs/Interpretation.lean) additionally proves:

- `Proofs.quartiles_above_threshold`: every reference-selection quartile exceeds
  `1/1000`, so edgeR's exceptional tiny-quartile reference fallback is irrelevant.
- `Proofs.cutoff_inactive`: every positive sample/reference count pair passes
  edgeR's default A cutoff of `-10^10`.

For RNAnorm's conflicting prose (the A-trimming bullet says `m_trim`, while the
parameter documentation defines `a_trim` for A), this model uses `a_trim = 0.05`,
as its parameter documentation and supplied implementation do.

The logarithms in these proofs are Mathlib's real logarithms. Rational interval
bounds follow from `Real.sum_range_le_log_div` and
`Real.log_div_le_sum_range_add`, using ten terms and range reduction by powers
of two. The weighted-sum bounds are proved in
[Proofs/Bounds.lean](Proofs/Bounds.lean) and
[Proofs/ScoreBounds.lean](Proofs/ScoreBounds.lean). All concrete rational checks
run through the Lean kernel; no `native_decide`, `bv_decide`, custom axiom, or
`sorry` is used.

### Limits of the R1/R2 conclusions

Documentation is not a formal specification of floating point rounding, `log2`,
or equality of rounded intermediate values. The translation above is a reviewed
exact-real mathematical specification. There is no formal semantics or general
correctness proof of the supplied R/Python source here, and no formal proof that
their machine computations approximate exact TMM within `10^-10`.

Consequently, if R1/R2 are instead understood as “reproduce exactly the specified
library's floating point procedure, including rounding-induced rank changes,”
those versions of R1/R2 remain **unproved**, rather than refuted by the exact-real
counterexamples. R3 remains false under either interpretation.

For diagnosis only, [verification/replay.py](verification/replay.py) replays the
NumPy formulas with average ranks, independently of Lean. It reproduces the
RNAnorm output within `2.3e-16`. Floating point ranks retain
`[64, 79, 77, 283, 89, 95, 81]` pairs. Computing the same weighted calculation
with exact ranks gives sample 3 approximately `1.147754971910146`. These decimal
approximations and the causal diagnosis are auxiliary numerical evidence;
the formal counterexamples rely only on the proved `> 1.14` bound.

## Connection to the exact artifact bytes

FVA generated [Proofs/Counts.lean](Proofs/Counts.lean),
[Proofs/Edge.lean](Proofs/Edge.lean), and
[Proofs/RNA.lean](Proofs/RNA.lean) with `fva blob`. They contain the complete
little-endian packed bytes, lengths, and project-relative source paths. The
claims refer directly to their `blob.data`. The proofs check full canonical TSV
and decimal encodings against those bytes, including tabs, decimal digits, and
final newlines. There is no hash-only premise in the theorems.

FVA's final trust check independently compares these generated modules and their
packed numerals with the files on disk. The files verified are:

| File | Bytes | SHA-256 (for identification) |
| --- | ---: | --- |
| `counts.tsv` | 6518 | `aa9abeaf77b5c06ca3200a374b82834c06ed59d4564eb69dcb18d1dcf0b112e5` |
| `edger-factors.txt` | 138 | `df500dba78cc7349d9c9959204de5c230343c6cb41c4efb753a8536d757df943` |
| `rnanorm-factors.txt` | 133 | `62fc3bea0957d7d91e676ba5a791c03ffff0bc94ebdd61b1de5e0f93f8a97d6d` |

The shipped inputs, outputs, producers, and library sources were not modified.

## Rechecking, offline

From this directory, with the supplied Lean/Mathlib/FVA installation:

```sh
bash verification/check.sh
```

The script copies the unchanged FVA package to a fresh `/tmp/fva-tmm-check.*`
directory, uses the installed pinned dependency packages, and rebuilds its
executable there. It then runs these substantive checks:

```sh
lake build
/tmp/fva-tmm-check.XXXXXX/.lake/build/bin/fva trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 200
```

The actual temporary path is selected by the script; the second block illustrates
its command arguments. No network, R installation, or Python scientific package
is required for the formal results. Python's standard library is used only to
locate the existing Lake package directory.

Success means that `lake build` exits 0 and prints `Build completed successfully`,
and `fva trust` exits 0 and prints `PASS`. Here **PASS means the counterexample
claims are proved**, not that the software meets its requirements. The full
FVA report is saved to [verification/trust.txt](verification/trust.txt).

**Recorded result:** `lake build` succeeded and the externally built FVA returned
`fva trust: PASS` (exit 0). `leanchecker` accepted the exported claims in 252 s;
the independent `con-leche` kernel accepted them in 175 s. All three blob links
matched. Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`
occur in the three proof closures.

The pinned 72 known-false canaries produced 71 rejections and one documented
acceptance in `leanchecker`; `con-leche` rejected 69 and declined three, accepting
none. FVA's verdict accounts for the documented acceptance and cross-kernel
coverage. There were no canary crashes or timeouts. Auxiliary interpretation
lemmas are checked by `lake build`; independent replay covers the three main
claims and their proof dependencies.

Optional auxiliary replay, requiring the already installed NumPy:

```sh
OPENBLAS_NUM_THREADS=1 python3 verification/replay.py
```

Its assertion requires reproduction of RNAnorm's seven values within `1e-12`.
It is not part of the formal certificate. `verification/generate.py` is an
optional untrusted witness printer; regenerating is unnecessary for checking
all delivered proofs.

## Review and trust surface

The essential project review surface is:

| File | Physical lines | Bytes | Why read it |
| --- | ---: | ---: | --- |
| `Proofs/Model.lean` | 100 | 4163 | Exact mathematical TMM, rank/tie rules, byte/decimal encodings. |
| `Proofs/Spec.lean` | 39 | 1721 | The precise three claims, including their artifact references and thresholds. |

Thus the mathematical translation and claims occupy **139 physical lines,
5884 bytes**. FVA reports **89 code lines** after excluding comments and blank
lines: 63 in `Proofs.Model` and 26 in `Proofs.Spec`.
A reviewer must compare this interpretation with `README.md`,
`edgeR/man/calcNormFactors.Rd`, RNAnorm's `TMM` docstring, and the supplied source
where tie/default details are needed. This natural-language-to-model
correspondence is not itself machine proved.

Supporting Lean proof/witness files total **833 physical lines, 71,223 bytes**.
They are kernel checked; their numeric witnesses and proof-generation choices
need not be trusted. The three generated FVA blob modules total 63 physical lines
and 15,266 bytes; FVA checks their format and byte links.

`verification/check.sh` is 13 lines/640 bytes and orchestrates checking;
`verification/generate.py` is 65 lines/6357 bytes and prints untrusted witnesses;
`verification/replay.py` is 32 lines/1472 bytes and supplies auxiliary evidence.
Only the orchestration must be followed to ensure the advertised checks were
actually run. No numerical answer from either Python script is a proof premise.

The remaining trusted foundation is the supplied FVA specifications and trust
orchestration, the pinned Mathlib and Lean toolchain, and their kernels. The
external FVA build has executable SHA-256
`5a4c6e4cdeb91cd5594cc00d75c1cf70384931b8497b7e60dedbbb2b30611407`,
identical to the supplied executable. FVA's report records its independent
kernel replays, known-false kernel canaries, axiom audit, byte links, and
review-surface count.
