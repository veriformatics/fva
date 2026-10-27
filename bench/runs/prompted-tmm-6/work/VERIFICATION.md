R3 is false for the shipped bytes. R1 and R2 have machine-checked counterexamples at absolute tolerance **10⁻¹⁰ under exact mathematical TMM with average ranks for ties**. That qualification matters: the supplied floating-point programs can split mathematical ties before ranking. This verification does not equate an exact mathematical specification with the operational semantics of R, NumPy, or SciPy.

| Requirement | Result |
|---|---|
| R1 | `Verification.R1_failure` refutes simultaneous correctness of samples 1 and 4 under the mathematical interpretation below. Separately, executing the unchanged shipped R functions reproduces **all bytes** of `edger-factors.txt`. A formal proof of R execution semantics is not supplied. |
| R2 | `Verification.R2_failure` gives the corresponding mathematical counterexample for samples 1 and 4. Execution of the full Python package is not established: the supplied source is a package fragment, and SciPy and scikit-learn are absent. |
| R3 | `Verification.R3_failure` unconditionally refutes agreement within 10⁻¹⁰. The exact first-sample difference is **0.00931142302732627**. This also precludes agreement after rounding to ten decimal places. |

The exact requirement-facing statements, in [Proofs/Results.lean](Proofs/Results.lean), are:

```lean
theorem R1_failure : ¬ FitsPair edge (1 / 10^10)
theorem R2_failure : ¬ FitsPair rna (1 / 10^10)
theorem R3_failure : |edge[0]! - rna[0]!| > (1 : ℚ) / 10^10
theorem R3_gap : edge[0]! - rna[0]! = (931142302732627 : ℚ) / 10^17
```

Here `edge` and `rna` are the exact decimal rationals from the two output files, in file order. Indexing starts at zero. `FitsPair f t` says that there exist mathematically correct first and fourth factors, each at absolute distance at most `t` from the respective artifact value. Its mathematical specification is [Proofs/Spec.lean](Proofs/Spec.lean), which should be read in full.

The input counterexample is the unchanged **entire `counts.tsv`**, not a replacement test matrix. [Proofs/Data.lean](Proofs/Data.lean) proves that it has 454 rows, seven columns per row, and no all-zero row; its library sizes are `[1261, 621, 755, 1097, 1916, 1136, 1219]`. The reference selected by the nearest-to-mean upper quartile rule is sample 4 (`reference = 3`). For samples 1 and 4 there are 244 jointly positive genes. Exact average ranks and default trims retain 63 genes; the full retained list is checked against the input in `retained_eq`.

The specification uses default M trimming 0.3 and A trimming 0.05, inverse asymptotic binomial variance weights, and common positive geometric rescaling. Since logarithms are strictly increasing, it ranks M by the exact count ratio and A by the exact count product. Twice an average rank is `2 * number_strictly_below + number_equal + 1`; this specifies ties explicitly. Upper quartiles use linear interpolation at positions 339 and 340, with weights 1/4 and 3/4. The fallback reference rule in edgeR is inactive because these quartiles are positive and far above 10⁻²⁰. RNAnorm's preliminary common geometric rescaling of quartiles does not change the nearest-to-mean choice in exact arithmetic. Its A-trim parameter description and default `.05` are used; the earlier bullet repeating `m_trim` for A appears to be a documentation typo.

`DocumentedPair first fourth` is the necessary relation `first = rawFirst * scale`, `fourth = scale`, for a common positive `scale`. Comparing the reference with itself gives raw factor one. Consequently the common normalization cancels, and the other five factors need not be modeled. [Proofs/Semantics.lean](Proofs/Semantics.lean) additionally proves `cutoff_inactive`: the default edgeR A cutoff of −10¹⁰ excludes none of this comparison's positive pairs.

[Proofs/Bounds.lean](Proofs/Bounds.lean) proves the exact statement

```lean
theorem rawFirst_upper : rawFirst < 41 / 40
```

The proof bounds the inverse-variance weighted natural logarithm by `3/125`. It checks rational eighth-power inequalities, then applies `log x ≤ x - 1`; it uses no floating-point logarithm oracle or numerical axiom. Exponentiation converts the logarithmic bound to the factor bound. Natural logarithms give the same factor as the documented base-two formulation. Both shipped pairs violate this necessary ratio bound even allowing 10⁻¹⁰ absolute error per factor. This proves that **at least one of samples 1 and 4** is outside that tolerance for each file; it does not assert that every sample is incorrect.

The interpretation limit is substantive. The documentation does not specify an IEEE-754 execution model, logarithm implementation, or a tolerance for numerical tie splitting. The supplied code ranks already-rounded M and A arrays. For example, running edgeR retains 65 genes in this comparison, whereas exact ranking retains 63. Thus these R1/R2 theorems refute the stated mathematical specification; they are not proofs that either artifact disagrees with its own generating routine. If R1/R2 are intended to mean agreement with those finite-precision routines rather than mathematical TMM, **R1 has an execution demonstration only, and R2 remains unproved**. R3's counterexample needs none of these interpretation choices.

Artifact binding is performed by [verification/embed.py](verification/embed.py). Its `--check` mode regenerates the expected Lean source **in memory** and compares it byte for byte with [Proofs/Artifact.lean](Proofs/Artifact.lean). That file embeds both the original ASCII strings, including final newlines, and their parsed integers/exact decimal rationals. It is not silently updated by checking. [verification/original-sha256.json](verification/original-sha256.json) also pins the original README, CHECK, data, outputs, scripts, implementation files, and documentation. No shipped implementation, data, or factor file was edited. The models above are specifications against which the actual output bytes are checked, not replacement implementations whose output is passed off as the artifact.

From this directory, the single offline check command is:

```sh
python3 verification/check.py
```

Success is exit status zero and the final line:

```text
VERIFICATION SUCCESS: artifact binding, proofs, four kernels, and negative controls passed
```

[verification/check.py](verification/check.py) checks the hashes and byte embedding, deletes locally built proof modules, rebuilds with `lake --no-cache build`, and executes [verification/reproduce.R](verification/reproduce.R). That R check sources the shipped functions and compares their formatted result with the original output bytes without overwriting the file. The checker then exports the named results and their transitive dependencies with `leanexport`, audits every exported axiom, and replays the same proof terms through:

- Lean's default kernel (`leanchecker --from-export`);
- the separate Lean implementation `lean4lean --import`;
- the Rust checker `nanoda_bin`;
- the Rust checker `con-ron` in its default verified mode.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Neither `sorryAx` nor compiler-trust axioms are permitted. Tactics and certificate calculations need not be trusted: the exported terms are checked independently. Logs and exports are retained in `.verification/`.

Each kernel must first accept a valid `True.intro : True` control, then reject the same exported theorem with its declared type changed to `False`, with the declaration moved after the declaration of `False`. This is a well-formed false proof, not a malformed input file. Nanoda reports its type-comparison rejection via exit 101 and a `self.def_eq(u, v)` assertion; the driver requires that specific diagnostic. The other checkers must return rejection status 1. A second control, the deliberately `sorry`-based theorem of `False` in [FalseControl.lean](FalseControl.lean), must fail the axiom audit. That negative fixture is not among the exported verification results. These tests demonstrate rejection of these false proofs; they do not prove the kernels themselves correct.

The human review surface and trusted machinery are accounted for as follows:

- **Mathematical meaning:** all 22 custom definitions in `Proofs/Spec.lean`, **62 lines / 3,105 bytes**, plus the four theorem statements above. The entire results file, including proof bodies, is only **33 lines / 1,056 bytes**. The correspondence between these definitions and the prose documentation, including the tie policy and numerical interpretation, remains a human judgment.
- **Artifact definitions:** `Proofs/Artifact.lean`, **6 definitions, 9 physical lines / 21,369 bytes**. This includes redundant raw text and 3,178 matrix entries plus 14 exact factor values. These data are checked by the binder rather than requiring manual transcription review.
- **Binding and orchestration:** `verification/embed.py`, **29 lines / 1,276 bytes**; `verification/check.py`, **117 lines / 5,622 bytes**; `verification/reproduce.R`, **8 lines / 499 bytes**; original hash manifest, **16 lines / 1,283 bytes**. The Python interpreter, its integer/Fraction/JSON/file operations, process execution, R for the supplemental reproduction, filesystem, and installed tool binaries are trusted infrastructure.
- **Library meaning and proof foundations:** Lean 4.35.0 and Mathlib v4.35.0 definitions of lists, naturals, integers, rationals, reals, logarithm, exponential, order, and arithmetic, transitively. They are not included in the small custom-definition count. The complete dependency closure is exported and independently replayed; its size is recorded below. Semantic trust in these library definitions and the three permitted axioms remains necessary.
- **Proof bodies:** `Proofs/Data.lean`, `Proofs/Bounds.lean`, and `Proofs/Semantics.lean` contain computational certificates and derivations. They are checked, rather than assumed. The original requirements and documentation must still be read to assess the mathematical interpretation: README is 17 lines / 1,642 bytes; edgeR's manual is 122 lines / 7,033 bytes; the supplied RNAnorm file is 441 lines / 17,490 bytes, with TMM beginning at line 190.

For exact reproduction of size counts, use `wc -l -c` on the named files. Counts include comments and blank lines and do not disguise large generated data as a small semantic definition. Proof replay also covers the library dependencies, rather than trusting cached theorem certificates as axioms.

The final export contains **1,352,276 NDJSON records**, **71,827,342 bytes**, including 4,289 definitions, 14 opaque declarations, 566 inductive blocks, 10,724 theorem declarations, and 3 axioms. These counts include the transitive Lean/Mathlib foundation and proof-support declarations, not just the custom specification. All four replays accepted this export.
