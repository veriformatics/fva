Both README requirements have counterexamples on their stated domains. The supplied implementation files and `edgeR.so` were left unchanged.

| Requirement | Result | Witness |
| --- | --- | --- |
| R1 | Fails for unrestricted positive library sizes and finite counts. | `c = L = 2^1023`: the artifact returns positive infinity; the exact CPM is the representable number `1000000`. |
| R2 | The README's biconditional fails. | One gene, one sample, count `10`, library size `1000000`, required samples `1`, default minimum count `10`: the gene qualifies in one sample but is discarded by the default total-count minimum of `15`. |

Run everything offline, from this directory, with:

```sh
python3 verification/check.py
```

Success means exit status zero and the final line:

```text
VERIFICATION PASSED: both README requirements have reproducible counterexamples.
```

Here, “passed” means the failure demonstrations, proof replays, and rejection controls all passed. The command regenerates `.verification/`, measures the implementations again, generates `Proofs/Observed.lean`, builds the proofs, exports their dependency closure, and checks it in four kernels. A missing tool, changed supplied input, unexpected implementation result, rejected positive proof, or accepted negative control makes the command fail. The tool locations are derived from `lean --print-prefix`; this installation supplies the additional checkers in `/opt/lean/bin`. No download is needed.

For R1, the exact input and output binary64 encodings are:

| Quantity | Hexadecimal encoding | Meaning |
| --- | --- | --- |
| Count and library size | `7fe0000000000000` | `2^1023`, finite, positive, and exactly represented |
| Correct target | `412e848000000000` | `1000000`, exactly represented |
| Actual output | `7ff0000000000000` | Positive infinity |

The count is an integer and is no larger than the library size. The exact mathematical expression is `(2^1023 / 2^1023) * 1000000 = 1000000`. Correctly rounding that exact target incurs zero error. The observed absolute and relative errors are infinite in the extended-real sense, so an unconditional finite rounding-error bound cannot hold over R1's stated domain. The actual WebAssembly performs `f64.mul` by `1000000` before `f64.div`; the intermediate product overflows. This demonstration establishes the failure of the unrestricted requirement. Bounds for a restricted domain excluding intermediate overflow and underflow have not been proved.

For R2, reproduce the R-level witness as:

```r
y <- matrix(10, nrow=1, ncol=1)
filterByExpr(y, lib.size=1e6, min.sample.size=1)
# FALSE
```

The median library size is `1e6`; the CPM cutoff is exactly `10`; the artifact computes CPM `10`; the number of qualifying samples is `1`. The sample requirement is also `1`. Nevertheless, `10 >= 15 - 1e-14` is false, and the implementation returns `FALSE`. Setting `min.total.count=0` returns `TRUE`. A separate count-`20` control passes the default filter.

The fuller manual in [man/filterByExpr.Rd](man/filterByExpr.Rd) explicitly documents the additional total-count condition. Thus this witness exposes an omission in the README's “exactly when” requirement, rather than establishing a defect relative to that fuller documentation. No universal equivalence to the entire manual is claimed.

The exact Lean statements are in [Proofs/Claims.lean](Proofs/Claims.lean), in namespace `Verification`:

```lean
theorem r1_counterexample :
    positiveNormal Observed.countBits ∧ positiveNormal Observed.libraryBits ∧
    normalRatio Observed.countBits = (2^1023, 1) ∧
    normalRatio Observed.libraryBits = (2^1023, 1) ∧
    (0 < (2^1023 : Nat)) ∧
    (2^1023 : Nat) / 2^1023 * 1000000 = 1000000 ∧
    positiveNormal Observed.targetBits ∧
    (normalRatio Observed.targetBits).1 = 1000000 * (normalRatio Observed.targetBits).2 ∧
    Observed.outputBits = 0x7ff0000000000000 ∧
    ¬ positiveNormal Observed.outputBits ∧ Observed.outputBits ≠ Observed.targetBits

theorem r2_counterexample :
    Observed.geneCount = 10 ∧ Observed.minCount = 10 ∧
    Observed.qualifying = 1 ∧ Observed.required = 1 ∧ Observed.kept = false ∧
    ¬ (Observed.kept = true ↔ Observed.required ≤ Observed.qualifying)
```

Both use ordinary kernel reduction with `decide`. Both have no axiom dependencies. There is no `native_decide`, floating-point evaluation inside a proof, compiler-trust axiom, or assumed execution theorem. The two custom interpretation definitions are:

```lean
def positiveNormal (bits : Nat) : Prop :=
  0 < bits / 2^52 ∧ bits / 2^52 < 2047

def normalRatio (bits : Nat) : Nat × Nat :=
  let e := bits / 2^52
  ((2^52 + bits % 2^52) * 2^(e - 1075), 2^(1075 - e))
```

`normalRatio` gives a numerator/denominator pair for a positive normal binary64 encoding. `positiveNormal` restricts its interpretation to that domain. The nine generated literal definitions in namespace `Observed` are:

```lean
def countBits : Nat := 9214364837600034816
def libraryBits : Nat := 9214364837600034816
def targetBits : Nat := 4696837146684686336
def outputBits : Nat := 9218868437227405312
def geneCount : Nat := 10
def minCount : Nat := 10
def qualifying : Nat := 1
def required : Nat := 1
def kept : Bool := false
```

These theorems certify the exact decoding, target arithmetic, and logical contradiction for measured values. Artifact execution is part of the trusted measurement boundary: the Lean theorems do not contain a formal WebAssembly or R execution relation. The requested failure demonstrations are direct executions of the supplied implementations; no handwritten replacement algorithm is used as proof of their behavior.

The artifact connection is checked as follows:

1. [verification/inputs.sha256](verification/inputs.sha256) pins all supplied requirements, documentation, R/C sources, and the binary. The binary must be exactly **96,558 bytes**, SHA-256 **`e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb`**. The check fails if any pinned input changes.
2. [verification/probe.wat](verification/probe.wat) calls the original `calc_cpm_raw` export. It supplies valid one-by-one full double `cmx` structures using the layout in `src/edgeR.h`, initializes the caller-owned CPM buffer with the count, and requests one thread. It checks that inputs and a neighboring guard are preserved. Data relocation is run before the call.
3. The entire original `edgeR.so` is loaded separately in Wasmtime and Node/V8. Neither execution uses a recompiled C function, extracted arithmetic fragment, or modified binary. `get_row` and all other internal calls execute the artifact's own code. Both runtimes must produce identical output bits for the overflow witness and zero/count-10/count-20 controls.
4. The generated support modules supply linear memory, the table, import globals, a fresh aligned zeroing allocator, and a non-reclaiming `R_chk_free`. Every other imported function traps if called. The allocation/free substitutes are sufficient for these bounded executions and perform no CPM arithmetic. Import declarations are obtained using `wasm-tools print`; the original artifact is also validated.
5. [verification/filter.R](verification/filter.R) sources both supplied R files unchanged and executes their actual `cpm` and `filterByExpr` methods. Native R cannot load this WebAssembly side module, and the rest of the edgeR package is absent. The script therefore supplies the missing `makeCompressedMatrix` plumbing and intercepts the foreign `.Call` boundary: it accepts only the exact one-by-one witness/control requests and returns their CPM results already cross-checked by both WebAssembly runtimes. The R filtering logic, dispatch, parameter defaults, threshold calculation, and final conjunction run from the supplied files. This is a narrow foreign-call bridge, not a full edgeR package installation.

The proof export `.verification/proofs.ndjson` is replayed from its dependency closure by:

| Checker | Check performed |
| --- | --- |
| `leanchecker --from-export` | Lean's C++ kernel replays the exported declarations. This supplements frontend checking. |
| `con-leche --verified --jobs=1` | A separate checker implemented in Lean accepts the same export. |
| `con-ron --verified --jobs=1` | A Rust implementation of the ConLeche design accepts the same export. It shares that design; it is additional implementation diversity. |
| `nanoda_bin` | A separate Rust type checker accepts the same export with an **empty permitted-axiom list** and hard errors on unpermitted axioms. |

The independent implementations include ConLeche and Nanoda, in addition to the standard Lean kernel. The exporter is a transport tool: these checkers recheck the terms and their definitions. Their logs, configurations, and executable SHA-256 hashes are regenerated under `.verification/`. `lean4lean` is not used: the installed binary expects a different `.olean` header. The selected export-based checkers accept this toolchain's format.

[verification/Forge.lean](verification/Forge.lean) deliberately constructs a well-formed `.olean` with the invalid theorem `forgedFalse : False` and proof term `True.intro`, using kernel checking bypassed **only in this negative fixture**. Compilation of this fixture must succeed, and all four export replays must reject its actual type mismatch. Nanoda reports that rejection by a failed definitional-equality assertion and nonzero exit. The harness checks rejection diagnostics, so a missing file or unrelated startup failure cannot stand in for rejection. [verification/Sorry.lean](verification/Sorry.lean) supplies a second negative control, `False` proved using `sorry`; the strict axiom audit must reject `sorryAx`. No positive proof imports either fixture.

The custom formal review surface is **54 lines, 2,055 bytes**, comprising `Proofs.lean`, `Proofs/Claims.lean`, and generated `Proofs/Observed.lean`; this includes proof bodies and administrative lines. It contains two theorem statements, two interpretation definitions, and nine literal observations. All their transitive standard-library dependencies are exported and checked too: **245 declaration records** (161 definitions, 53 theorems, 31 inductive blocks), **0 axiom records**, in **508,144 bytes / 9,384 NDJSON lines**. Inductive blocks account for the different constant count reported by Nanoda. Standard meanings of natural-number arithmetic, equality, propositions, products, and Boolean values remain part of the interpretation a reviewer accepts; they are not hidden new assumptions or a model of edgeR.

The complete additional executable/formal review material is:

| File | Lines | Bytes | Review purpose |
| --- | ---: | ---: | --- |
| `Proofs.lean` | 1 | 21 | Library entry point |
| `Proofs/Claims.lean` | 41 | 1,625 | Exact statements, decoding definitions, proofs |
| `Proofs/Observed.lean` | 12 | 409 | Fresh measured literals |
| `verification/check.py` | 241 | 12,458 | Hash checking, import generation, execution, observation capture, replay and negative controls |
| `verification/probe.wat` | 27 | 1,555 | ABI layout, initialization and actual export call |
| `verification/run.mjs` | 16 | 785 | Second runtime's direct binary loading and execution |
| `verification/filter.R` | 38 | 2,026 | R execution and restricted foreign-call bridge |
| `verification/inputs.sha256` | 9 | 708 | Supplied-input identity |
| `verification/Forge.lean` | 11 | 348 | Invalid-proof rejection fixture |
| `verification/Sorry.lean` | 1 | 39 | Unpermitted-axiom rejection fixture |
| **Total** | **397** | **19,974** | Excludes this explanatory report and generated logs |

Those sizes are recomputed into `.verification/sizes.tsv`; the full proof census is in `.verification/proof-census.json`. Generated support WAT modules are mechanically expanded from the artifact imports and `check.py`; a reviewer can inspect them in `.verification/`. The trusted execution infrastructure includes Python and its standard library, R, Node/V8, Wasmtime, `wasm-tools`, the OS/hardware, the SHA-256 identity check, and the ABI/bridge choices above. Proof acceptance additionally relies on the correctness of at least one appropriately configured kernel and on the stated interpretation of the formal propositions. No verified compiler, verified runtime, or universal program-correctness result is asserted.

The successful run used Lean **4.35.0**, Wasmtime **50.0.0**, wasm-tools **1.262.0**, Node **26.11.1**, and R **4.6.1**. `.verification/versions.txt`, `.verification/checkers.sha256`, the four `kernel-*.log` files, the `reject-*.log` files, `.verification/observations.json`, and `.verification/filter.tsv` record the reproducible evidence.
