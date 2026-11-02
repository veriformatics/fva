# explainer-d56 report (D56 fva explain on the 30 archived fva-arm specs)

Coverage = 30/30 runs with requirement JSON; 75/75 requirement comparisons; 48 mapped agreements; 27 mapped disagreements; 0 rows not comparable. Execution failures are not disagreement or agreement.

Fresh trust: PASS 29; FAIL 1. Label compatibility is separate from fresh proof acceptance.

| run | requirements file | explain rc | fresh trust | per-requirement explain verdicts | shipped M3 verdicts | agreement (k/n) | disagreements (row ids) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| fva-edger-cpm-1 | requirements/edger-cpm.md | 1 | PASS | R1=weaker; R2=missing | R1=not proven, reported; R2=not proven, reported | 1/2 | fva-edger-cpm-1/R1 |
| fva-edger-cpm-2 | requirements/edger-cpm.md | 1 | PASS | R1=weaker; R2=missing | R1=not proven, reported; R2=not proven, reported | 1/2 | fva-edger-cpm-2/R1 |
| fva-edger-cpm-3 | requirements/edger-cpm.md | 1 | PASS | R1=weaker; R2=missing | R1=not proven, reported; R2=not proven, reported | 1/2 | fva-edger-cpm-3/R1 |
| fva-edger-cpm-4 | requirements/edger-cpm.md | 1 | PASS | R1=different; R2=different | R1=not proven, reported; R2=not proven, reported | 2/2 | none |
| fva-edger-cpm-5 | requirements/edger-cpm.md | 1 | PASS | R1=weaker; R2=missing | R1=not proven, reported; R2=not proven, reported | 1/2 | fva-edger-cpm-5/R1 |
| fva-glm-iround-1 | requirements/glm-iround.md | 1 | PASS | R1=different | R1=not proven, reported | 1/1 | none |
| fva-glm-iround-2 | requirements/glm-iround.md | 1 | PASS | R1=different | R1=not proven, reported | 1/1 | none |
| fva-glm-iround-3 | requirements/glm-iround.md | 1 | PASS | R1=different | R1=not proven, reported | 1/1 | none |
| fva-glm-iround-4 | requirements/glm-iround.md | 1 | PASS | R1=different | R1=not proven, reported | 1/1 | none |
| fva-glm-iround-5 | requirements/glm-iround.md | 1 | PASS | R1=weaker | R1=not proven, reported | 0/1 | fva-glm-iround-5/R1 |
| fva-lz4-c-1 | requirements/lz4-c.md | 1 | PASS | R1=weaker; R2=weaker; R3=weaker | R1=not proven, reported; R2=weaker; R3=weaker | 2/3 | fva-lz4-c-1/R1 |
| fva-lz4-c-2 | requirements/lz4-c.md | 1 | PASS | R1=weaker; R2=weaker; R3=weaker | R1=not proven, reported; R2=weaker; R3=weaker | 2/3 | fva-lz4-c-2/R1 |
| fva-lz4-c-3 | requirements/lz4-c.md | 1 | PASS | R1=weaker; R2=weaker; R3=weaker | R1=not proven, reported; R2=weaker; R3=weaker | 2/3 | fva-lz4-c-3/R1 |
| fva-lz4-c-4 | requirements/lz4-c.md | 1 | PASS | R1=missing; R2=weaker; R3=weaker | R1=not proven, reported; R2=weaker; R3=weaker | 3/3 | none |
| fva-lz4-c-5 | requirements/lz4-c.md | 1 | PASS | R1=weaker; R2=weaker; R3=weaker | R1=weaker; R2=weaker; R3=weaker | 3/3 | none |
| fva-lz4-rust-1 | requirements/lz4-rust.md | 1 | PASS | R1=missing; R2=weaker; R3=missing | R1=not proven, reported; R2=weaker; R3=weaker | 2/3 | fva-lz4-rust-1/R3 |
| fva-lz4-rust-2 | requirements/lz4-rust.md | 1 | PASS | R1=missing; R2=weaker; R3=weaker | R1=not proven, reported; R2=weaker; R3=weaker | 3/3 | none |
| fva-lz4-rust-3 | requirements/lz4-rust.md | 1 | PASS | R1=weaker; R2=weaker; R3=weaker | R1=weaker; R2=weaker; R3=weaker | 3/3 | none |
| fva-lz4-rust-4 | requirements/lz4-rust.md | 1 | PASS | R1=different; R2=different; R3=different | R1=not proven, reported; R2=weaker; R3=weaker | 1/3 | fva-lz4-rust-4/R2, fva-lz4-rust-4/R3 |
| fva-lz4-rust-5 | requirements/lz4-rust.md | 1 | FAIL | R1=missing; R2=weaker; R3=weaker | R1=not proven, reported; R2=weaker; R3=weaker | 3/3 | none |
| fva-lz4-wasm-3 | requirements/lz4-wasm.md | 1 | PASS | R1=weaker; R2=weaker; R3=missing | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 1/3 | fva-lz4-wasm-3/R1, fva-lz4-wasm-3/R2 |
| fva-lz4-wasm-4 | requirements/lz4-wasm.md | 1 | PASS | R1=weaker; R2=weaker; R3=missing | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 1/3 | fva-lz4-wasm-4/R1, fva-lz4-wasm-4/R2 |
| fva-lz4-wasm-5 | requirements/lz4-wasm.md | 1 | PASS | R1=different; R2=weaker; R3=missing | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 2/3 | fva-lz4-wasm-5/R2 |
| fva-lz4-wasm-6 | requirements/lz4-wasm.md | 1 | PASS | R1=weaker; R2=weaker; R3=missing | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 1/3 | fva-lz4-wasm-6/R1, fva-lz4-wasm-6/R2 |
| fva-lz4-wasm-7 | requirements/lz4-wasm.md | 1 | PASS | R1=missing; R2=weaker; R3=missing | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 2/3 | fva-lz4-wasm-7/R2 |
| fva-tmm-1 | requirements/tmm.md | 1 | PASS | R1=different; R2=different; R3=different | R1=faithful; R2=faithful; R3=not proven, reported | 1/3 | fva-tmm-1/R1, fva-tmm-1/R2 |
| fva-tmm-2 | requirements/tmm.md | 1 | PASS | R1=different; R2=different; R3=different | R1=faithful; R2=faithful; R3=not proven, reported | 1/3 | fva-tmm-2/R1, fva-tmm-2/R2 |
| fva-tmm-3 | requirements/tmm.md | 1 | PASS | R1=weaker; R2=weaker; R3=different | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 1/3 | fva-tmm-3/R1, fva-tmm-3/R2 |
| fva-tmm-4 | requirements/tmm.md | 1 | PASS | R1=weaker; R2=weaker; R3=different | R1=faithful; R2=faithful; R3=not proven, reported | 1/3 | fva-tmm-4/R1, fva-tmm-4/R2 |
| fva-tmm-5 | requirements/tmm.md | 1 | PASS | R1=different; R2=different; R3=different | R1=not proven, reported; R2=not proven, reported; R3=not proven, reported | 3/3 | none |

## Mapping explain → M3 (locked before the first comparison)

- `matches` or `stronger` → `faithful`: the claims cover at least the stated requirement.
- `weaker` → `weaker`: the requirement's own observable is covered on a smaller domain or with a weaker conclusion.
- `missing` → `missing` or `not proven, reported`: no covering claim; M3 distinguishes omissions from explicitly open work.
- `different` → `not proven, reported`: coarse non-coverage bucket, including claims that refute rather than establish a requirement.
- `vacuous` → `false claim`: no substantive guarantee.

Agreement is label compatibility under this fixed, coarse mapping, not semantic equivalence. In particular, `different` cannot itself distinguish a sound refutation from an unrelated claim; `missing` cannot establish that a report disclosed the gap. M3 grades the run's whole report, while explain sees neutralized claim statements and the supplied requirements. Raw labels, reasons, and every mismatch remain visible. Proof validity is separate from M3 and label agreement.

## Disagreements (one section per row id: claim text, explain reason, shipped M3 reason)

### fva-edger-cpm-1/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every count `c` and library size `L > 0`, the counts-per-million value that `calc_cpm_raw` computes is `c / L × 10⁶`, rounded as double-precision arithmetic allows; state the rounding error you prove.
- Explain reason: The claims only concern specific calls and memory setups, and none states the required result for every count and positive library size or proves a rounding-error bound. Claims 1 and 2 are explicitly false; claim 3’s premise requires a positive floating-point value divided by itself, so it does not establish the general formula.
- Shipped M3 reason (.scratch/teammates/reviewer-18/verdicts.md:7, J1): `Proofs/Spec.lean:28-34` proves a terminating, nontrapping call writing +∞, finite positive c=L=2^1023, and exact real CPM=10⁶. `Proofs/Context.lean:49-71` installs all decoded functions but supplies the allocation/import state; no full-module instantiation theorem. This contradicts a universal finite-error interpretation, not IEEE instruction semantics. Report anchor (`rg -Fn`): `no universal finite-error guarantee has been established` (`VERIFICATION.md:11`). No restricted-domain accuracy theorem is substituted for R1. Concrete full-binary confirmation appears in `verification/artifact_test.py:82-89`; recorded command `python3 verification/artifact_test.py; Rscript --vanilla verification/filter_test.R` at decoded event-log line 103 reports both PASS markers, exit 0.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r2_total_witness`

```lean
(FVA.Wasm.Exec.CallReturns (fun x x_1 x_2 x_3 => False) (Proofs.inputStore 4621819117588971520 4696837146684686336)
    Proofs.linked.2 "calc_cpm_raw"
    [FVA.Wasm.Exec.Val.i32 32768, FVA.Wasm.Exec.Val.i32 32800, FVA.Wasm.Exec.Val.i32 32840, FVA.Wasm.Exec.Val.i32 1]
    fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧ mem.read 32840 8 = 4621819117588971520) ∧
  Proofs.filterDecision 1 1 10 15 = false
```

`Proofs.r2_rounding_witness`

```lean
(FVA.Wasm.Exec.CallReturns (fun x x_1 x_2 x_3 => False) (Proofs.inputStore 4621819117588971520 4625759767262920704)
    Proofs.linked.2 "calc_cpm_raw"
    [FVA.Wasm.Exec.Val.i32 32768, FVA.Wasm.Exec.Val.i32 32800, FVA.Wasm.Exec.Val.i32 32840, FVA.Wasm.Exec.Val.i32 1]
    fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧ mem.read 32840 8 = 4693019397977130780) ∧
  FVA.Wasm.Exec.Must (fun x x_1 x_2 x_3 => False)
      (fun x =>
        match x with
        | FVA.Wasm.Exec.Outcome.returned s vs => vs = [FVA.Wasm.Exec.Val.i32 0]
        | FVA.Wasm.Exec.Outcome.trapped s => False)
      Proofs.cutoffComparison ∧
    Proofs.filterDecision 0 2 20 15 = false
```

`Proofs.r1_counterexample`

```lean
(FVA.Wasm.Exec.CallReturns (fun x x_1 x_2 x_3 => False) (Proofs.inputStore Proofs.huge Proofs.huge) Proofs.linked.2
    "calc_cpm_raw"
    [FVA.Wasm.Exec.Val.i32 32768, FVA.Wasm.Exec.Val.i32 32800, FVA.Wasm.Exec.Val.i32 32840, FVA.Wasm.Exec.Val.i32 1]
    fun s vs => vs = [] ∧ ∃ mem, s.mems[0]? = some mem ∧ mem.read 32840 8 = 9218868437227405312) ∧
  (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt Proofs.huge).IsNum ∧
    0 < FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt Proofs.huge) ∧
      FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt Proofs.huge) /
            FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt Proofs.huge) *
          1000000 =
        1000000
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-edger-cpm-2/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every count `c` and library size `L > 0`, the counts-per-million value that `calc_cpm_raw` computes is `c / L × 10⁶`, rounded as double-precision arithmetic allows; state the rounding error you prove.
- Explain reason: These claims establish an export and instruction sequence plus arithmetic facts for fixed binary64 values, but do not relate the function’s output to every count and positive library size or prove a rounding-error bound.
- Shipped M3 reason (.scratch/teammates/reviewer-18/verdicts.md:9, J3): `Proofs/Spec.lean:31-52` proves artifact export/selected-instruction identity, finite positive c=L=2^1020, exact target 10⁶, and singleton IEEE multiplication/division outcomes +∞. It does not prove the function reaches the selected instructions. Report anchor: `selected inner-loop instruction sequence` (`VERIFICATION.md:24`); the opening explicitly disclaims complete C-function execution proof (`:3`). `verification/check.R:22-27` calls the original artifact through the narrow FFI replacement and asserts overflow; retained `verification/counterexamples.txt:1` records it. Class = reported failure of unrestricted finite accuracy, with arithmetic-model support and executed full-artifact evidence, not all-input correctness.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.overflow_witness`

```lean
Proofs.artifact_arithmetic ∧
  (Proofs.dbl 9200854038717923328).IsNum ∧
    0 < FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (Proofs.dbl 9200854038717923328) ∧
      FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (Proofs.dbl 9200854038717923328) /
              FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (Proofs.dbl 9200854038717923328) *
            1000000 =
          1000000 ∧
        FVA.Wasm.Num.fmul FVA.Wasm.Num.f64fmt (Proofs.dbl 9200854038717923328) (Proofs.dbl 4696837146684686336) =
            {FVA.Wasm.Num.FVal.inf false} ∧
          FVA.Wasm.Num.fdiv FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.FVal.inf false) (Proofs.dbl 9200854038717923328) =
            {FVA.Wasm.Num.FVal.inf false}
```

`Proofs.threshold_witness`

```lean
Proofs.artifact_arithmetic ∧
  FVA.Wasm.Num.fmul FVA.Wasm.Num.f64fmt (Proofs.dbl 4621819117588971520) (Proofs.dbl 4696837146684686336) =
      {Proofs.dbl 4711630319722168320} ∧
    FVA.Wasm.Num.fdiv FVA.Wasm.Num.f64fmt (Proofs.dbl 4711630319722168320) (Proofs.dbl 4630263366890291200) =
        {Proofs.dbl 4688515798349760284} ∧
      FVA.Wasm.Num.fdiv FVA.Wasm.Num.f64fmt (Proofs.dbl 4621819117588971520) (Proofs.dbl 4630263366890291200) =
          {Proofs.dbl 4598675619503873138} ∧
        FVA.Wasm.Num.fmul FVA.Wasm.Num.f64fmt (Proofs.dbl 4598675619503873138) (Proofs.dbl 4696837146684686336) =
            {Proofs.dbl 4688515798349760285} ∧
          FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (Proofs.dbl 4688515798349760284) <
            FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (Proofs.dbl 4688515798349760285)
```

`Proofs.artifact_arithmetic`

```lean
{ name := "calc_cpm_raw", desc := FVA.Wasm.ExportDesc.func 160 } ∈ Proofs.Lifted.module.exports ∧
  Proofs.cellCode =
    [FVA.Wasm.Instr.localGet 5, FVA.Wasm.Instr.localGet 5,
      FVA.Wasm.Instr.load FVA.Wasm.NumType.f64 { align := 3, offset := 0 },
      FVA.Wasm.Instr.fconst FVA.Wasm.Width.w64 4696837146684686336,
      FVA.Wasm.Instr.fbinop FVA.Wasm.Width.w64 FVA.Wasm.FBinOp.mul, FVA.Wasm.Instr.localGet 11,
      FVA.Wasm.Instr.localGet 0, FVA.Wasm.Instr.iconst FVA.Wasm.Width.w32 3,
      FVA.Wasm.Instr.ibinop FVA.Wasm.Width.w32 FVA.Wasm.IBinOp.shl,
      FVA.Wasm.Instr.ibinop FVA.Wasm.Width.w32 FVA.Wasm.IBinOp.add,
      FVA.Wasm.Instr.load FVA.Wasm.NumType.f64 { align := 3, offset := 0 },
      FVA.Wasm.Instr.fbinop FVA.Wasm.Width.w64 FVA.Wasm.FBinOp.div,
      FVA.Wasm.Instr.store FVA.Wasm.NumType.f64 { align := 3, offset := 0 }]
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-edger-cpm-3/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every count `c` and library size `L > 0`, the counts-per-million value that `calc_cpm_raw` computes is `c / L × 10⁶`, rounded as double-precision arithmetic allows; state the rounding error you prove.
- Explain reason: The claims do not establish the required result for every count and positive library size; claims 2–4 cover only fixed inputs. In particular, claim 4 says equal inputs of 2^1023 leave positive infinity, rather than the required 1,000,000. No general rounding-error bound is stated.
- Shipped M3 reason (.scratch/teammates/reviewer-18/verdicts.md:11, J5): `Proofs/Spec.lean:22-29` proves finite positive input interpretation, exact target 10⁶, and `∀ H, CallReturns ...` with +∞ output. `Proofs/Fixture.lean:15-47` binds the original two reachable functions and explicit Wasm allocator/free; other module loading remains outside the theorem. `verification/wasm-results.txt:1-4` records original-binary execution; `verification/r-results.txt:1` records the R-wrapper demonstration. Report anchor: `claims about this particular linked state.` (`VERIFICATION.md:100`), immediately followed by the no-`Instantiated`/`LoaderReady` disclaimer. No global rounding bound is claimed.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.artifact_binding`

```lean
(List.filter
        (fun i =>
          match i.desc with
          | FVA.Wasm.ImportDesc.func x => true
          | x => false)
        Proofs.Lifted.module.imports).length =
    74 ∧
  Proofs.Lifted.module.exports.contains { name := "calc_cpm_raw", desc := FVA.Wasm.ExportDesc.func 160 } = true ∧
    Proofs.Lifted.module.funcs[86]? = some Proofs.Lifted.func86 ∧
      Proofs.Lifted.module.funcs[133]? = some Proofs.Lifted.func133 ∧
        Proofs.Lifted.module.types[17]? =
            some
              {
                params :=
                  [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                    FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
                results := [] } ∧
          Proofs.Lifted.module.types[4]? =
              some
                {
                  params :=
                    [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                      FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
                  results := [] } ∧
            Proofs.Lifted.func86.type = 17 ∧ Proofs.Lifted.func133.type = 4
```

`Proofs.r2_rounding_gap`

```lean
Proofs.r2_cpm_bits ∧
  (∀ (H : FVA.Wasm.Exec.HostSem),
      FVA.Wasm.Exec.Must H
        (fun x =>
          match x with
          | FVA.Wasm.Exec.Outcome.returned s vs => vs = [FVA.Wasm.Exec.Val.f64 4693019397977130781]
          | FVA.Wasm.Exec.Outcome.trapped s => False)
        Proofs.cutoffConfig) ∧
    FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt 4693019397977130780) =
        10 / 18 * 1000000 - 1 / 19327352832 ∧
      FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt 4693019397977130780) <
        FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt (FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt 4693019397977130781)
```

`Proofs.r2_cpm_bits`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H (Proofs.fixtureStore 4621819117588971520 4625759767262920704) Proofs.fixtureInstance
    "calc_cpm_raw" Proofs.fixtureArgs fun s vs => vs = [] ∧ Proofs.outputBits s = 4693019397977130780
```

`Proofs.r1_overflow`

```lean
FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt 9214364837600034816 = FVA.Wasm.Num.FVal.normal false 0 1023 ∧
  0 < 2 ^ 1023 ∧
    2 ^ 1023 / 2 ^ 1023 * 1000000 = 1000000 ∧
      ∀ (H : FVA.Wasm.Exec.HostSem),
        FVA.Wasm.Exec.CallReturns H (Proofs.fixtureStore 9214364837600034816 9214364837600034816) Proofs.fixtureInstance
          "calc_cpm_raw" Proofs.fixtureArgs fun s vs => vs = [] ∧ Proofs.outputBits s = 9218868437227405312
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-edger-cpm-5/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every count `c` and library size `L > 0`, the counts-per-million value that `calc_cpm_raw` computes is `c / L × 10⁶`, rounded as double-precision arithmetic allows; state the rounding error you prove.
- Explain reason: These claims verify an export and instruction pattern, plus two exact execution cases; they do not establish the computed value for every count and positive library size or state a rounding-error bound. The examples in claims 2 and 3 guarantee outputs only for their exact bit-pattern pairs.
- Shipped M3 reason (.scratch/teammates/reviewer-18/verdicts.md:15, J9): `Proofs/Spec.lean:56-58` proves total execution of the actual selected 13 instructions, starting with local pointers/memory fixed by `cellStart`; it does not establish reachability from export entry. `artifact_binding` (`:43-51`) ties that fragment to the decoded artifact. Whole-function Wasmtime/Node executions produce the same +∞ (`verification/check.log:12-15`). Report anchor: `The Lean execution proofs start at the update fragment. They do not prove` (`VERIFICATION.md:135`). This supports the disclosed concrete failure, not a whole-function formal theorem or all-input error bound.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.artifact_binding`

```lean
(Proofs.Lifted.module.exports.any fun e =>
      e.name == "calc_cpm_raw" &&
        match e.desc with
        | FVA.Wasm.ExportDesc.func n => n == 160
        | x => false) =
    true ∧
  (List.filter
          (fun i =>
            match i.desc with
            | FVA.Wasm.ImportDesc.func x => true
            | x => false)
          Proofs.Lifted.module.imports).length =
      74 ∧
    Proofs.Lifted.module.funcs[86]? = some Proofs.Lifted.func86 ∧
      Proofs.rawCell =
        [FVA.Wasm.Instr.localGet 5, FVA.Wasm.Instr.localGet 5,
          FVA.Wasm.Instr.load FVA.Wasm.NumType.f64 { align := 3, offset := 0 },
          FVA.Wasm.Instr.fconst FVA.Wasm.Width.w64 4696837146684686336,
          FVA.Wasm.Instr.fbinop FVA.Wasm.Width.w64 FVA.Wasm.FBinOp.mul, FVA.Wasm.Instr.localGet 11,
          FVA.Wasm.Instr.localGet 0, FVA.Wasm.Instr.iconst FVA.Wasm.Width.w32 3,
          FVA.Wasm.Instr.ibinop FVA.Wasm.Width.w32 FVA.Wasm.IBinOp.shl,
          FVA.Wasm.Instr.ibinop FVA.Wasm.Width.w32 FVA.Wasm.IBinOp.add,
          FVA.Wasm.Instr.load FVA.Wasm.NumType.f64 { align := 3, offset := 0 },
          FVA.Wasm.Instr.fbinop FVA.Wasm.Width.w64 FVA.Wasm.FBinOp.div,
          FVA.Wasm.Instr.store FVA.Wasm.NumType.f64 { align := 3, offset := 0 }]
```

`Proofs.r2_boundary`

```lean
Proofs.artifact_binding ∧
  ∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.Must H (Proofs.wrote 4693019397977130780) (Proofs.cellStart 4621819117588971520 4625759767262920704)
```

`Proofs.r1_overflow`

```lean
Proofs.artifact_binding ∧
  ∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.Must H (Proofs.wrote 9218868437227405312) (Proofs.cellStart 9214364837600034816 9214364837600034816)
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-glm-iround-5/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every finite `x` with `0 ≤ x ≤ 2147483647`, `iround(x)` returns the integer nearest to `x`. When `x` lies exactly halfway between two integers, either of them is accepted. (The lower bound is the documented precondition; the upper bound keeps the nearest integer within the `i32` result.)
- Explain reason: This claim covers only one input, a floating-point value just below 0.5, and requires output 1. R1 requires nearest-integer behavior for every finite input in the full range; this input’s nearest integer is 0, so the claimed output does not satisfy even that case.
- Shipped M3 reason (.scratch/teammates/reviewer-55/verdicts.md:11, J5): - Cited statement = `r1_counterexample_holds : r1_counterexample`, `bench/runs/fva-glm-iround-5/work/Proofs/Proof.lean:12`; claim `bench/runs/fva-glm-iround-5/work/Proofs/Spec.lean:11–18`.
- Program = decoded `Proofs.Lifted.module`, `bench/runs/fva-glm-iround-5/work/Proofs/Lifted.lean:13–40`; theorem about shipped bytes under FVA semantics. Domain = the finite binary64 value `0x3fdfffffffffffff`, exact `1/2 − 1/18014398509481984`, within `[0,2147483647]`. Every execution returns 1; 0 strictly closer than 1. This refutes universal R1, rather than proving only a convenient sub-domain. Fuel 10 affects proof computation alone.
- Report witness (M4 extraction): **yes** — `bench/runs/fva-glm-iround-5/work/VERIFICATION.md:3–14`: same bits, exact decimal `0.499999999999999944488848768742172978818416595458984375` (CLI `0.49999999999999994`), artifact **1**, closer integer **0**. Matched exact anchor: `**R1 is false.**` (`:3`).
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r1_counterexample`

```lean
have bits := 4602678819172646911;
have x := FVA.Wasm.Num.ofBits FVA.Wasm.Num.f64fmt bits;
x.IsNum ∧
  FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt x = 1 / 2 - 1 / 18014398509481984 ∧
    0 ≤ FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt x ∧
      FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt x ≤ 2147483647 ∧
        |FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt x - 0| < |FVA.Wasm.Num.FVal.toReal FVA.Wasm.Num.f64fmt x - 1| ∧
          FVA.Wasm.Exec.Returns Proofs.Lifted.module "iround" [FVA.Wasm.Exec.Val.f64 bits] [FVA.Wasm.Exec.Val.i32 1]
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-c-1/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Among the addresses 131072 to 2097151, `LZ4_decompress_safe` reads only bytes of `src[0 .. srcSize)` and `dst[0 .. dstCapacity)`, and writes only bytes of `dst[0 .. dstCapacity)`, whatever the bytes at `src` are.
- Explain reason: Claim 8 covers only zero-capacity calls with an in-bounds nonzero source and says the store is unchanged; claim 9 checks one specific zero-capacity input. Neither constrains reads or writes for general inputs and capacities, and neither ensures writes stay within the destination buffer.
- Shipped M3 reason (.scratch/teammates/reviewer-37/verdicts.md:9, J1): `emptyBlock_holds` (`Proofs/Proof.lean:25`) and `zeroCapacity_holds` (`:33`) constrain the **final store** (`Proofs/Spec.lean:28–47`): respectively the fixed call `(131072,196608,1,0)` on byte 0 in the initialized store, and all i32 src/dst/source-size values at capacity 0 in `callerStore mem`, subject to src nonzero and its first byte in memory. They do not constrain reads or intermediate writes. `validModule_holds` is Wasm typing, not a caller-buffer footprint. Exact report anchor: `Final-state equality does not establish an access footprint:` (`VERIFICATION.md:9`). No R1 access theorem is claimed, and the omission is reported. Thus `not proven, reported`, not a trace-safety proof for a small input domain.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.zeroCapacity`

```lean
∀ (H : FVA.Wasm.Exec.HostSem) (mem : FVA.Wasm.Exec.MemInst) (src dst n : BitVec 32),
  src ≠ 0 →
    src.toNat < mem.size →
      FVA.Wasm.Exec.CallReturns H (Proofs.callerStore mem) Proofs.initialInst "LZ4_decompress_safe"
        [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 n, FVA.Wasm.Exec.Val.i32 0]
        fun s vs =>
        s = Proofs.callerStore mem ∧ vs = [FVA.Wasm.Exec.Val.i32 (if n = 1#32 ∧ mem.byte src.toNat = 0 then 0 else -1)]
```

`Proofs.emptyBlock`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H (Proofs.initialStore.withBytes 131072 [0]) Proofs.initialInst "LZ4_decompress_safe"
    [FVA.Wasm.Exec.Val.i32 131072, FVA.Wasm.Exec.Val.i32 196608, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 0]
    fun s vs => vs = [FVA.Wasm.Exec.Val.i32 0] ∧ s = Proofs.initialStore.withBytes 131072 [0]
```

Ruling (MAIN): shipped M3 stands. The claims constrain the final store (guard or source bytes after the call), not the access trace R1 names; the rubric's observable rule makes that `not proven, reported`. Explain judged only the narrow domain, with no notion of a different observable: a limit of the requirement-mode check, not of the run.

### fva-lz4-c-2/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Among the addresses 131072 to 2097151, `LZ4_decompress_safe` reads only bytes of `src[0 .. srcSize)` and `dst[0 .. dstCapacity)`, and writes only bytes of `dst[0 .. dstCapacity)`, whatever the bytes at `src` are.
- Explain reason: These claims check particular inputs and preserve only the two guard bytes in those examples. They do not guarantee that every call reads and writes only within the permitted buffers, as R1 requires.
- Shipped M3 reason (.scratch/teammates/reviewer-37/verdicts.md:12, J4): `DecodeCase` observes **final output/guard bytes** for seven fixed input/output/capacity tuples (`Proofs/Spec.lean:13–58`), all at src 131072/dst 196608 with destination prefilled 165, under every host semantics/fitting fresh instance. The separate empty-source and one-byte/zero-capacity boundary claims constrain **return values**, not accesses (`:61–70`). None excludes reads elsewhere or records writes followed by restoration; the guard postcondition does not even preserve every address outside the destination. Exact report anchor: `There is no R1 theorem.` (`VERIFICATION.md:7`). Therefore R1 is `not proven, reported`.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.extendedLiterals`

```lean
Proofs.DecodeCase [240, 0, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
  [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79] 15
```

`Proofs.literalBlock`

```lean
Proofs.DecodeCase [80, 65, 66, 67, 68, 69] [65, 66, 67, 68, 69] 5
```

`Proofs.zeroOffset`

```lean
Proofs.DecodeCase [3, 0, 0, 80, 65, 66, 67, 68, 69] [0, 0, 0, 0, 0, 0, 0, 65, 66, 67, 68, 69] 12
```

`Proofs.emptyBlockPositive`

```lean
Proofs.DecodeCase [0] [] 1
```

`Proofs.extendedMatch`

```lean
Proofs.DecodeCase [31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70] (List.replicate 20 65 ++ [66, 67, 68, 69, 70]) 25
```

`Proofs.overlappingMatch`

```lean
Proofs.DecodeCase [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70] 13
```

`Proofs.emptyBlock`

```lean
Proofs.DecodeCase [0] [] 0
```

Ruling (MAIN): shipped M3 stands. The claims constrain the final store (guard or source bytes after the call), not the access trace R1 names; the rubric's observable rule makes that `not proven, reported`. Explain judged only the narrow domain, with no notion of a different observable: a limit of the requirement-mode check, not of the run.

### fva-lz4-c-3/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Among the addresses 131072 to 2097151, `LZ4_decompress_safe` reads only bytes of `src[0 .. srcSize)` and `dst[0 .. dstCapacity)`, and writes only bytes of `dst[0 .. dstCapacity)`, whatever the bytes at `src` are.
- Explain reason: These claims do not establish the memory-access limits for arbitrary inputs. Claim 1 leaves the store unchanged only when the input length is zero; claim 2 checks output and guard bytes only for thirteen fixtures.
- Shipped M3 reason (.scratch/teammates/reviewer-37/verdicts.md:15, J7): `caseCorrect` checks **final source/output/guard bytes** for the 13 fixed tuples in `cases`, all at src 131072/dst 196608, their listed sizes/capacities, with destination/guards prefilled 165 in every fresh instance; the guards cover only eight bytes on each side (`Proofs/Spec.lean:28–62`). `zeroInputRejected` additionally quantifies over all i32 pointers/capacities and arbitrary caller bytes written at zero, with source size fixed at 0, but constrains only **final-store equality and return −1** (`:65–71`). Neither proposition constrains individual accesses. Exact report anchor: `There is no general access-trace invariant` (`VERIFICATION.md:11`). R1 is explicitly left unproved; verdict = `not proven, reported`.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.zeroInputRejected`

```lean
FVA.Wasm.Exec.Instantiable Proofs.Lifted.module ∧
  ∀ (H : FVA.Wasm.Exec.HostSem) (s : FVA.Wasm.Exec.Store) (inst : FVA.Wasm.Exec.ModuleInst),
    FVA.Wasm.Exec.Instance Proofs.Lifted.module H s inst →
      ∀ (src dst capacity : BitVec 32) (memory : List UInt8),
        FVA.Wasm.Exec.CallReturns H (s.withBytes 0 memory) inst "LZ4_decompress_safe"
          [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 0,
            FVA.Wasm.Exec.Val.i32 capacity]
          fun s' vs => s' = s.withBytes 0 memory ∧ vs = [FVA.Wasm.Exec.Val.i32 4294967295]
```

`Proofs.regressionCases`

```lean
FVA.Wasm.Exec.Instantiable Proofs.Lifted.module ∧ ∀ c ∈ Proofs.cases, Proofs.caseCorrect c
```

Ruling (MAIN): shipped M3 stands. The claims constrain the final store (guard or source bytes after the call), not the access trace R1 names; the rubric's observable rule makes that `not proven, reported`. Explain judged only the narrow domain, with no notion of a different observable: a limit of the requirement-mode check, not of the run.

### fva-lz4-rust-1/R3

- Explain = `missing`; shipped M3 = `weaker`.
- Requirement: If `lz4_decompress` returns a value `r` that is not negative, then `r ≤ cap`, the `n` bytes at `src` split into LZ4 sequences as the format defines them, each match offset between 1 and the number of bytes decoded before that match, and `dst[0 .. r)` holds their decoded content, of length `r`. A block that breaks only the end-of-block conditions may decode, because the format allows a decoder to accept it.
- Explain reason: No claim states that every nonnegative return corresponds to a valid sequence split, in-range match offsets, and the decoded content in the output. Fixed test cases and the zero-length result do not establish this for arbitrary calls.
- Shipped M3 reason (.scratch/teammates/reviewer-47/verdicts.md:9, J3): Anchor: `e.result.toNat = e.output.length ∧ e.output.length ≤ e.cap` at Spec:62. Same finite domain/program as J2; observable = return/output with r≤cap. For each of the six successful concrete byte strings, a sequence decomposition and offsets can be checked directly against the format; exact result/output is proved. Ten rejections do not supply the universal converse. Missing = every other input/nonnegative return, a general sequence-decomposition relation, placements/capacities/caller memory. Report: `No general implication from a nonnegative return to an LZ4 sequence decomposition was proved.` at VERIFICATION:11. This is a disclosed restriction, not a false verification claim.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.empty_input_preserves_store`

```lean
FVA.Wasm.Exec.Instantiable Proofs.Lifted.module ∧
  ∀ (H : FVA.Wasm.Exec.HostSem) (s : FVA.Wasm.Exec.Store) (inst : FVA.Wasm.Exec.ModuleInst),
    FVA.Wasm.Exec.Instance Proofs.Lifted.module H s inst →
      ∀ (src dst cap : BitVec 32) (p : ℕ) (bytes : List UInt8),
        FVA.Wasm.Exec.CallReturns H (s.withBytes p bytes) inst "lz4_decompress"
          [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 cap]
          fun s' vs => s' = s.withBytes p bytes ∧ vs = [FVA.Wasm.Exec.Val.i32 4294967295]
```

`Proofs.concrete_examples`

```lean
∀ e ∈ Proofs.examples, Proofs.ExampleCorrect e
```

`Proofs.initializes`

```lean
FVA.Wasm.Exec.Instantiable Proofs.Lifted.module
```

Ruling (MAIN): shipped M3 `weaker` stands. The case table states R3's observable (exact result and output, r ≤ cap) for each of its six successful inputs, a finite sub-domain; explain found no claim stating R3 because none is universal. Explain error (`missing` for a finite case statement).

### fva-lz4-rust-4/R2

- Explain = `different`; shipped M3 = `weaker`.
- Requirement: If the `n` bytes at `src` are a valid independent block of the LZ4 block format, as `lz4_Block_format.md` defines it: a block whose matches refer only to bytes already decoded from this block (`lz4_decompress` takes no dictionary and no previous block), and its decoded content fits in `cap` bytes, then `lz4_decompress` returns the length `r` of the decoded content, and afterwards `dst[0 .. r)` holds that content.
- Explain reason: No claim guarantees decoding for every valid independent LZ4 block that fits in the destination. Claim_4 covers only a one-byte source containing zero and fixed arguments; it does not establish the general valid-block condition or decoded content.
- Shipped M3 reason (.scratch/teammates/reviewer-47/verdicts.md:17, J11): Anchor: `mem.byte src.toNat = 0 →` at Spec:38; call fixes n1/cap0 (Spec:40). Observable = total return0 + unchanged final store; decoded content empty, hence exact output vacuous. Domain = every host/store/inst/src/dst/memory satisfying actual decoder binding, memory0 binding and source readability; includes README-conforming empty-block calls. Missing = all nonempty content, cap>0 and general valid-block refinement. Report explicitly states scope. Program = artifact decoder, not source model; successful artifact instantiation is a separate theorem.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.artifactProfile`

```lean
Proofs.Lifted.module.imports = [] ∧
  Proofs.Lifted.module.start = none ∧
    Proofs.Lifted.module.mems = [{ min := 32, max := some 32 }] ∧
      Proofs.Lifted.module.exports[2]? = some { name := "lz4_decompress", desc := FVA.Wasm.ExportDesc.func 7 } ∧
        Proofs.Lifted.module.funcs[7]? = some Proofs.Lifted.func7 ∧
          Proofs.Lifted.func7.type = 4 ∧
            Proofs.Lifted.module.types[4]? =
              some
                {
                  params :=
                    [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                      FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
                  results := [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32] }
```

`Proofs.artifactInitializes`

```lean
FVA.Wasm.Exec.Instantiable Proofs.Lifted.module
```

`Proofs.zeroLengthRejected`

```lean
∀ (H : FVA.Wasm.Exec.HostSem) (s : FVA.Wasm.Exec.Store) (inst : FVA.Wasm.Exec.ModuleInst) (src dst cap : BitVec 32),
  s.funcs[7]? =
      some
        (FVA.Wasm.Exec.FuncInst.wasm
          {
            params :=
              [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
            results := [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32] }
          inst Proofs.Lifted.func7) →
    FVA.Wasm.Exec.Must H (fun o => o = FVA.Wasm.Exec.Outcome.returned s [FVA.Wasm.Exec.Val.i32 4294967295])
      (FVA.Wasm.Exec.invokeConfig s 7
        [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 cap])
```

`Proofs.emptyBlockDecoded`

```lean
∀ (H : FVA.Wasm.Exec.HostSem) (s : FVA.Wasm.Exec.Store) (inst : FVA.Wasm.Exec.ModuleInst) (src dst : BitVec 32)
  (mem : FVA.Wasm.Exec.MemInst),
  s.funcs[7]? =
      some
        (FVA.Wasm.Exec.FuncInst.wasm
          {
            params :=
              [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
            results := [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32] }
          inst Proofs.Lifted.func7) →
    inst.mems = [0] →
      s.mems[0]? = some mem →
        src.toNat + 1 ≤ mem.size →
          mem.byte src.toNat = 0 →
            FVA.Wasm.Exec.Must H (fun o => o = FVA.Wasm.Exec.Outcome.returned s [FVA.Wasm.Exec.Val.i32 0])
              (FVA.Wasm.Exec.invokeConfig s 7
                [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 1,
                  FVA.Wasm.Exec.Val.i32 0])
```

Ruling (MAIN): shipped M3 `weaker` stands. The claims prove the requirement's own observable (return and output) on a sub-domain (a one-byte zero block); a narrower domain is `weaker` under both label sets. Explain error (`different` for a narrower domain).

### fva-lz4-rust-4/R3

- Explain = `different`; shipped M3 = `weaker`.
- Requirement: If `lz4_decompress` returns a value `r` that is not negative, then `r ≤ cap`, the `n` bytes at `src` split into LZ4 sequences as the format defines them, each match offset between 1 and the number of bytes decoded before that match, and `dst[0 .. r)` holds their decoded content, of length `r`. A block that breaks only the end-of-block conditions may decode, because the format allows a decoder to accept it.
- Explain reason: No claim establishes the required relationship between every nonnegative return and the block's sequences, match offsets, and decoded output. Claim_3 guarantees a negative result for n = 0, while emptyBlockDecoded covers only one constrained call and says nothing about those general properties.
- Shipped M3 reason (.scratch/teammates/reviewer-47/verdicts.md:18, J12): Anchor: `Must H (fun o => o = .returned s [.i32 0])` at Spec:39. Observable = nonnegative return/output for [0] with cap0, all symbolic states/addresses under J11's hypotheses. For that success, r=0≤cap, input is a single final-literal sequence, there are no offsets, content is empty. This supports R3 on a proper subdomain even though the report's R3 row emphasizes zero-length rejection. The n0 negative-return theorem alone would not prove success soundness. Missing = all other successful inputs/caps and general decomposition/content relation. Report leaves R3 open; no full verification assertion.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.artifactProfile`

```lean
Proofs.Lifted.module.imports = [] ∧
  Proofs.Lifted.module.start = none ∧
    Proofs.Lifted.module.mems = [{ min := 32, max := some 32 }] ∧
      Proofs.Lifted.module.exports[2]? = some { name := "lz4_decompress", desc := FVA.Wasm.ExportDesc.func 7 } ∧
        Proofs.Lifted.module.funcs[7]? = some Proofs.Lifted.func7 ∧
          Proofs.Lifted.func7.type = 4 ∧
            Proofs.Lifted.module.types[4]? =
              some
                {
                  params :=
                    [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                      FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
                  results := [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32] }
```

`Proofs.artifactInitializes`

```lean
FVA.Wasm.Exec.Instantiable Proofs.Lifted.module
```

`Proofs.zeroLengthRejected`

```lean
∀ (H : FVA.Wasm.Exec.HostSem) (s : FVA.Wasm.Exec.Store) (inst : FVA.Wasm.Exec.ModuleInst) (src dst cap : BitVec 32),
  s.funcs[7]? =
      some
        (FVA.Wasm.Exec.FuncInst.wasm
          {
            params :=
              [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
            results := [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32] }
          inst Proofs.Lifted.func7) →
    FVA.Wasm.Exec.Must H (fun o => o = FVA.Wasm.Exec.Outcome.returned s [FVA.Wasm.Exec.Val.i32 4294967295])
      (FVA.Wasm.Exec.invokeConfig s 7
        [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 cap])
```

`Proofs.emptyBlockDecoded`

```lean
∀ (H : FVA.Wasm.Exec.HostSem) (s : FVA.Wasm.Exec.Store) (inst : FVA.Wasm.Exec.ModuleInst) (src dst : BitVec 32)
  (mem : FVA.Wasm.Exec.MemInst),
  s.funcs[7]? =
      some
        (FVA.Wasm.Exec.FuncInst.wasm
          {
            params :=
              [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32,
                FVA.Wasm.ValType.num FVA.Wasm.NumType.i32, FVA.Wasm.ValType.num FVA.Wasm.NumType.i32],
            results := [FVA.Wasm.ValType.num FVA.Wasm.NumType.i32] }
          inst Proofs.Lifted.func7) →
    inst.mems = [0] →
      s.mems[0]? = some mem →
        src.toNat + 1 ≤ mem.size →
          mem.byte src.toNat = 0 →
            FVA.Wasm.Exec.Must H (fun o => o = FVA.Wasm.Exec.Outcome.returned s [FVA.Wasm.Exec.Val.i32 0])
              (FVA.Wasm.Exec.invokeConfig s 7
                [FVA.Wasm.Exec.Val.i32 src, FVA.Wasm.Exec.Val.i32 dst, FVA.Wasm.Exec.Val.i32 1,
                  FVA.Wasm.Exec.Val.i32 0])
```

Ruling (MAIN): shipped M3 `weaker` stands. The claims prove the requirement's own observable (return and output) on a sub-domain (a one-byte zero block); a narrower domain is `weaker` under both label sets. Explain error (`different` for a narrower domain).

### fva-lz4-wasm-3/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Every block that `lz4BlockEncode` returns is a valid block of the LZ4 block format, as `lz4_Block_format.md` defines it, and decoding it gives back exactly the encoded input.
- Explain reason: Claim 1 covers only one particular 13-byte encoder call, and claim 4 concerns decoding rather than showing that all encoder outputs are valid LZ4 blocks or round-trip correctly. The claims do not establish the requirement for every block the encoder returns.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:9, J1): The encoder's returned block must be valid and decode to the input. `r1_holds` proves a genuine instance plus a total returning call after the README's table/input preparation. The observed block `50 61 62 63 64 58 05 00 40 31 32 33 34` has five initial literals, offset 5 / match length 4, then four final literals. Its decoded length is 13; four < five final literals and 13 − 5 = eight < twelve last-match distance. Either violation refutes R1's validity conjunct; no universal round-trip theorem is required. Exact report anchor: `Both violate the mandatory “End of block conditions”` (`VERIFICATION.md:59`). The absent general formal LZ4 predicate is disclosed by `There is no full formalization of the prose LZ4 format here.` (`:22`), not sold as a theorem.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r1`

```lean
(∀ (H : FVA.Wasm.Exec.HostSem), FVA.Wasm.Exec.Instance Proofs.Lifted.module H Proofs.fresh.1 Proofs.fresh.2) ∧
  ∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.CallReturns H Proofs.encoderStore Proofs.fresh.2 "lz4BlockEncode"
      [FVA.Wasm.Exec.Val.i32 262144, FVA.Wasm.Exec.Val.i32 13, FVA.Wasm.Exec.Val.i32 262200] fun s vs =>
      vs = [FVA.Wasm.Exec.Val.i32 13] ∧ Proofs.bytesAt s 262200 13 = some Proofs.encoderOutput
```

`Proofs.r2`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 100 Proofs.validBlock) Proofs.fresh.2 "lz4BlockDecode"
    [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 10, FVA.Wasm.Exec.Val.i32 0] fun s vs =>
    vs = [FVA.Wasm.Exec.Val.i32 1] ∧ Proofs.bytesAt s 0 13 = some (65 :: List.replicate 12 0)
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-3/R2

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every valid block of the LZ4 block format, `lz4BlockDecode` writes exactly the block's decoded content and returns its length.
- Explain reason: These claims cover only a few specified one-byte or ten-byte inputs, not every valid LZ4 block. Claim 2 even says one particular call traps, so the claims do not guarantee correct decoding for all valid blocks.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:10, J2): The valid block `13 41 01 00 50 42 43 44 45 46` denotes one `A`, seven more by offset-1 overlap copying, then `BCDEF`: 13 bytes. Five final literals and last-match distance 12 satisfy the format. `r2_holds` proves a total return of 1 with output `41` plus twelve zeros, for disjoint in-memory input `[100,110)` and output at 0. Exact report anchor: `The artifact instead returns **1**.` (`VERIFICATION.md:86`). R2 imposes no input-before-output layout, so this witness is within its domain. The additional one-byte empty-block trap also contradicts the required return of zero.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.emptyBlockTrap`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallTraps H (Proofs.fresh.1.withBytes 65535 [0]) Proofs.fresh.2 "lz4BlockDecode"
    [FVA.Wasm.Exec.Val.i32 65535, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 0] fun x => True
```

`Proofs.r3`

```lean
(∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 0 [0, 0, 0]) Proofs.fresh.2 "lz4BlockDecode"
      [FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 1024] fun x vs =>
      vs = [FVA.Wasm.Exec.Val.i32 0]) ∧
  ∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 0 [0, 1, 0]) Proofs.fresh.2 "lz4BlockDecode"
      [FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 1024] fun x vs =>
      vs = [FVA.Wasm.Exec.Val.i32 4]
```

`Proofs.r2`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 100 Proofs.validBlock) Proofs.fresh.2 "lz4BlockDecode"
    [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 10, FVA.Wasm.Exec.Val.i32 0] fun s vs =>
    vs = [FVA.Wasm.Exec.Val.i32 1] ∧ Proofs.bytesAt s 0 13 = some (65 :: List.replicate 12 0)
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-4/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Every block that `lz4BlockEncode` returns is a valid block of the LZ4 block format, as `lz4_Block_format.md` defines it, and decoding it gives back exactly the encoded input.
- Explain reason: This checks one fixed 13-byte encoder input and its output, not every block the encoder may return or whether decoding each result recovers its input.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:12, J4): The returned block must be valid and decode to the input. Here the kernel-checked call returns the block `50 61 62 63 64 65 05 00 40 65 66 67 68` after the prescribed hash-table initialization. It has five literals, offset 5 / match length 4, and four final literals: final count four < five and last-match distance eight < twelve. The separate `initialization` claim certifies a fresh instance and successful growth to five pages. Exact report anchor: `A validity failure alone refutes R1's conjunction; this example does not claim a separate encoder round-trip failure.` (`VERIFICATION.md:19`). Manual token interpretation is expressly separated from machine-checked execution (`:86`).
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r1_counterexample`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H Proofs.encoderStore Proofs.allocation.2 "lz4BlockEncode"
    [FVA.Wasm.Exec.Val.i32 262144, FVA.Wasm.Exec.Val.i32 13, FVA.Wasm.Exec.Val.i32 262208] fun s vs =>
    vs = [FVA.Wasm.Exec.Val.i32 13] ∧ Proofs.bytesAt s 262208 13 = Proofs.badBlock
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-4/R2

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every valid block of the LZ4 block format, `lz4BlockDecode` writes exactly the block's decoded content and returns its length.
- Explain reason: These check decoder results for only a few fixed inputs, not every valid LZ4 block. The claims do not establish the required behavior across all valid blocks.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:13, J5): Block `17 61 01 00 50 62 63 64 65 66` decodes to twelve `a` bytes plus `bcdef`, length 17; offset 1, five trailing literals and last-match distance 16 satisfy the format. The proven call returns 1 and leaves output `61` + sixteen zeros. Input `[100,110)` and output `[0,17)` are disjoint, and the requirement has no buffer-order restriction. Exact anchor: `The shipped decoder instead returns **1**.` (`VERIFICATION.md:29`).
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r3_counterexample`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  (FVA.Wasm.Exec.CallReturns H (Proofs.allocation.1.withBytes 0 [0, 0, 0]) Proofs.allocation.2 "lz4BlockDecode"
      [FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 1024] fun x vs =>
      vs = [FVA.Wasm.Exec.Val.i32 0]) ∧
    FVA.Wasm.Exec.CallReturns H (Proofs.allocation.1.withBytes 0 [0, 1, 0]) Proofs.allocation.2 "lz4BlockDecode"
      [FVA.Wasm.Exec.Val.i32 0, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 1024] fun x vs =>
      vs = [FVA.Wasm.Exec.Val.i32 4]
```

`Proofs.r2_counterexample`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H (Proofs.allocation.1.withBytes 100 Proofs.validBlock) Proofs.allocation.2 "lz4BlockDecode"
    [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 10, FVA.Wasm.Exec.Val.i32 0] fun s vs =>
    vs = [FVA.Wasm.Exec.Val.i32 1] ∧ Proofs.bytesAt s 0 17 = 97 :: List.replicate 16 0
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-5/R2

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every valid block of the LZ4 block format, `lz4BlockDecode` writes exactly the block's decoded content and returns its length.
- Explain reason: These claims cover only particular inputs, not every valid block; moreover, r3_counterexample says the one-byte zero block returns 0, and r2_counterexample says a format-valid 10-byte block decoding to 13 bytes instead returns 1 and writes a different 13-byte pattern. They do not guarantee exact decoding in general.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:16, J8): `r2_counterexample` proves both `Format.decode validBlock = some decodedBlock` with length 13 and the actual call's total return 1 / output `41` followed by twelve zeros. The format is independently readable: one `A`, offset-1 match of seven bytes, then five final literals `BCDEF`, last-match distance 12. Exact anchor: `with the rest of memory initially zero. It returns 1.` (`VERIFICATION.md:101`). The disjoint buffers satisfy the README. RG1 records a source/destination wording error in the causal diagnosis; it leaves the proven return and requirement refutation intact.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r3_counterexample`

```lean
Proofs.Format.decode [0] = some [] ∧
  (∀ (H : FVA.Wasm.Exec.HostSem),
      ∃ c c',
        FVA.Wasm.Exec.Steps H
            (FVA.Wasm.Exec.invokeConfig (Proofs.emptyStore 1) 3
              [FVA.Wasm.Exec.Val.i32 200, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 300])
            c ∧
          Proofs.nextByteRead 20 c.instrs = some 201 ∧ FVA.Wasm.Exec.Step H c c') ∧
    (∀ (H : FVA.Wasm.Exec.HostSem),
        FVA.Wasm.Exec.CallReturns H (Proofs.emptyStore 0) Proofs.allocation.2 "lz4BlockDecode"
          [FVA.Wasm.Exec.Val.i32 200, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 300] fun x vs =>
          vs = [FVA.Wasm.Exec.Val.i32 0]) ∧
      ∀ (H : FVA.Wasm.Exec.HostSem),
        FVA.Wasm.Exec.CallReturns H (Proofs.emptyStore 1) Proofs.allocation.2 "lz4BlockDecode"
          [FVA.Wasm.Exec.Val.i32 200, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 300] fun x vs =>
          vs = [FVA.Wasm.Exec.Val.i32 4]
```

`Proofs.r2_counterexample`

```lean
Proofs.Format.decode Proofs.validBlock = some Proofs.decodedBlock ∧
  Proofs.decodedBlock.length = 13 ∧
    ∀ (H : FVA.Wasm.Exec.HostSem),
      FVA.Wasm.Exec.CallReturns H Proofs.decoderStore Proofs.allocation.2 "lz4BlockDecode"
        [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 10, FVA.Wasm.Exec.Val.i32 0] fun s vs =>
        vs = [FVA.Wasm.Exec.Val.i32 1] ∧ Proofs.bytesAt s 0 13 = some (65 :: List.replicate 12 0)
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-6/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Every block that `lz4BlockEncode` returns is a valid block of the LZ4 block format, as `lz4_Block_format.md` defines it, and decoding it gives back exactly the encoded input.
- Explain reason: The claims only show an instance/store setup and one fixed 13-byte encoding result. They do not establish that every input the encoder returns produces a valid LZ4 block that decodes back to that input.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:18, J10): The artifact call returns `50 61 62 63 64 65 05 00 40 57 58 59 5a`; `r1` also negates `endConditions 13 5 4`. That predicate is exactly five-or-more final literals and last-match start + twelve ≤ decoded size. The token parse gives the supplied arguments: five initial literals, offset 5 / match length 4, then four final literals. `preparation` proves the fresh instance, possible four-page growth, every initialized hash word and the input bytes. Exact anchor: `This positive-length result refutes R1's validity conjunct` (`VERIFICATION.md:27`). Format interpretation is still reviewable, not concealed by a full-format claim.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.preparation`

```lean
(∀ (H : FVA.Wasm.Exec.HostSem), FVA.Wasm.Exec.Instance Proofs.Lifted.module H Proofs.fresh.1 Proofs.fresh.2) ∧
  (∃ m m', Proofs.fresh.1.mems[0]? = some m ∧ m.grow 4 = some m' ∧ m'.pages = 5) ∧
    (∀ i < 65536, ∃ m, Proofs.encoderStore.mems[0]? = some m ∧ m.read (4 * i) 4 = 4294901760) ∧
      Proofs.bytesAt Proofs.encoderStore 262144 Proofs.encoderInput
```

`Proofs.r1`

```lean
(∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.CallReturns H Proofs.encoderStore Proofs.fresh.2 "lz4BlockEncode"
      [FVA.Wasm.Exec.Val.i32 262144, FVA.Wasm.Exec.Val.i32 13, FVA.Wasm.Exec.Val.i32 262200] fun s vs =>
      vs = [FVA.Wasm.Exec.Val.i32 13] ∧ Proofs.bytesAt s 262200 Proofs.encoderOutput) ∧
  ¬Proofs.endConditions 13 5 4
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-6/R2

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every valid block of the LZ4 block format, `lz4BlockDecode` writes exactly the block's decoded content and returns its length.
- Explain reason: These cover only a few fixed inputs, including a one-byte decode that returns 0 and a specified 13-byte block that returns 1. They do not guarantee correct decoding for every valid block.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:19, J11): `shortValid` is sufficient for its stated subset: two sequences without extensions, positive offset into already emitted literals, valid literal/match nibbles, forward-overlap content and both end conditions. Its concrete witness `10 41 01 00 80 42 43 44 45 46 47 48 49` denotes five `A`s plus `BCDEFGHI`, length 13, trailing literal count eight and last-match distance twelve. `r2` proves this certificate plus actual return 1 and wrong output. Exact anchor: ``Call `lz4BlockDecode(100, 13, 0)`. It returns 1.`` (`VERIFICATION.md:49`). A sound valid subset is enough to refute an every-valid-block requirement; no universal decoder verification is claimed.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r3_dependence`

```lean
(∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 100 [0, 0, 0]) Proofs.fresh.2 "lz4BlockDecode"
      [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 1000] fun s vs =>
      vs = [FVA.Wasm.Exec.Val.i32 0] ∧ Proofs.bytesAt s 1000 [0, 0, 0, 0]) ∧
  ∀ (H : FVA.Wasm.Exec.HostSem),
    FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 100 [0, 1, 0]) Proofs.fresh.2 "lz4BlockDecode"
      [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 1000] fun s vs =>
      vs = [FVA.Wasm.Exec.Val.i32 4] ∧ Proofs.bytesAt s 1000 [0, 0, 0, 0]
```

`Proofs.r3`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallTraps H (Proofs.fresh.1.withBytes 65535 [0]) Proofs.fresh.2 "lz4BlockDecode"
    [FVA.Wasm.Exec.Val.i32 65535, FVA.Wasm.Exec.Val.i32 1, FVA.Wasm.Exec.Val.i32 0] fun x => True
```

`Proofs.r2`

```lean
Proofs.shortValid Proofs.validBlock Proofs.decodedContent ∧
  Proofs.decodedContent.length = 13 ∧
    ∀ (H : FVA.Wasm.Exec.HostSem),
      FVA.Wasm.Exec.CallReturns H (Proofs.fresh.1.withBytes 100 Proofs.validBlock) Proofs.fresh.2 "lz4BlockDecode"
        [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 13, FVA.Wasm.Exec.Val.i32 0] fun s vs =>
        vs = [FVA.Wasm.Exec.Val.i32 1] ∧ Proofs.bytesAt s 0 [65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-lz4-wasm-7/R2

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: For every valid block of the LZ4 block format, `lz4BlockDecode` writes exactly the block's decoded content and returns its length.
- Explain reason: The claim covers only one fixed decoder input, not every valid LZ4 block. Its example returns 1 while specifying 13 output bytes, so it does not even guarantee the decoded length matches the output content for that call.
- Shipped M3 reason (.scratch/teammates/reviewer-12/verdicts.md:22, J14): The valid block `13 41 01 00 50 42 43 44 45 46` denotes eight `A`s plus `BCDEF`, length 13, with five final literals and last-match distance 12. The theorem proves a total return of 1 and output `41` + twelve zeros for disjoint input `[100,110)` / output `[32,45)`. Exact anchor: `The theorem proves that the decoder returns **1**` (`VERIFICATION.md:67`). This refutes writing exactly the decoded content and returning its length; a buffer-order precondition absent from the README cannot exclude the witness.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r2_counterexample`

```lean
∀ (H : FVA.Wasm.Exec.HostSem),
  FVA.Wasm.Exec.CallReturns H Proofs.decoderStore Proofs.allocation.2 "lz4BlockDecode"
    [FVA.Wasm.Exec.Val.i32 100, FVA.Wasm.Exec.Val.i32 10, FVA.Wasm.Exec.Val.i32 32] fun s vs =>
    vs = [FVA.Wasm.Exec.Val.i32 1] ∧ Proofs.memoryBytes s 32 13 = [65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-tmm-1/R1

- Explain = `different`; shipped M3 = `faithful`.
- Requirement: Each value in `edger-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as edgeR documents TMM in `edgeR/man/calcNormFactors.Rd` (default arguments).
- Explain reason: Claim 3 bounds each edgeR factor's difference from its computed statistic by 1/40, but the requirement does not define that statistic as edgeR's documented TMM factor or provide a tolerance. Claim 1 instead asserts a large difference at the third position; neither guarantees R1.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:7, J1): `bench/runs/fva-tmm-1/work/Proofs/Spec.lean:11-14`, `Proofs/Model.lean:55-102`, `Proofs/Proof.lean:9`: byte-bound all-seven-factor theorem; exact-average ties, absolute tolerance 0.025.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.tightAccuracyFails`

```lean
∃ xs es rs,
  Proofs.Counts.blob.data = Proofs.matrixText xs ∧
    Proofs.Edger.blob.data = Proofs.factorText es ∧
      Proofs.Rnanorm.blob.data = Proofs.factorText rs ∧
        Proofs.matrixOK xs ∧
          ↑1 / ↑50 < |↑(Proofs.decimalValue es[2]!) - Proofs.tmm xs 2 3| ∧
            ↑1 / ↑50 < |↑(Proofs.decimalValue rs[2]!) - Proofs.tmm xs 2 3|
```

`Proofs.R2`

```lean
∃ xs ds,
  Proofs.Counts.blob.data = Proofs.matrixText xs ∧
    Proofs.Rnanorm.blob.data = Proofs.factorText ds ∧
      Proofs.matrixOK xs ∧
        ds.length = 7 ∧ ∀ j ∈ List.range 7, |↑(Proofs.decimalValue ds[j]!) - Proofs.tmm xs j 3| ≤ 1 / 40
```

`Proofs.R1`

```lean
∃ xs ds,
  Proofs.Counts.blob.data = Proofs.matrixText xs ∧
    Proofs.Edger.blob.data = Proofs.factorText ds ∧
      Proofs.matrixOK xs ∧
        ds.length = 7 ∧ ∀ j ∈ List.range 7, |↑(Proofs.decimalValue ds[j]!) - Proofs.tmm xs j 3| ≤ 1 / 40
```

Ruling (MAIN): shipped M3 `faithful` stands. The claims bind the shipped output bytes to the run's exact-real TMM model within the tolerance the run states (R1/R2 let the run state it); reviewer-24 checked the model against the edgeR/RNAnorm documentation. Explain cannot read the documentation the requirement cites, so it cannot confirm that the model is the documented method: a limit of the requirement-mode check on requirements that cite external documents.

### fva-tmm-1/R2

- Explain = `different`; shipped M3 = `faithful`.
- Requirement: Each value in `rnanorm-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as RNAnorm documents TMM in the docstring of its class `TMM` (default arguments).
- Explain reason: Claim 2 only bounds RNAnorm factors against the computed statistic within 1/40; it does not establish that statistic as RNAnorm's documented TMM factor or specify a requirement-level tolerance. Claim 4 concerns disagreement with edgeR, not correctness against the documented method.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:8, J2): `bench/runs/fva-tmm-1/work/Proofs/Spec.lean:19-22`, `Proofs/Model.lean:55-102`, `Proofs/Proof.lean:36`: same documented exact-real TMM policy, all seven RNAnorm decimal values within 0.025.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.R2`

```lean
∃ xs ds,
  Proofs.Counts.blob.data = Proofs.matrixText xs ∧
    Proofs.Rnanorm.blob.data = Proofs.factorText ds ∧
      Proofs.matrixOK xs ∧
        ds.length = 7 ∧ ∀ j ∈ List.range 7, |↑(Proofs.decimalValue ds[j]!) - Proofs.tmm xs j 3| ≤ 1 / 40
```

`Proofs.R3Fails`

```lean
∃ es rs,
  Proofs.Edger.blob.data = Proofs.factorText es ∧
    Proofs.Rnanorm.blob.data = Proofs.factorText rs ∧
      es.length = 7 ∧
        rs.length = 7 ∧ ∀ j ∈ List.range 7, 1 / 1000 < |↑(Proofs.decimalValue es[j]!) - ↑(Proofs.decimalValue rs[j]!)|
```

Ruling (MAIN): shipped M3 `faithful` stands. The claims bind the shipped output bytes to the run's exact-real TMM model within the tolerance the run states (R1/R2 let the run state it); reviewer-24 checked the model against the edgeR/RNAnorm documentation. Explain cannot read the documentation the requirement cites, so it cannot confirm that the model is the documented method: a limit of the requirement-mode check on requirements that cite external documents.

### fva-tmm-2/R1

- Explain = `different`; shipped M3 = `faithful`.
- Requirement: Each value in `edger-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as edgeR documents TMM in `edgeR/man/calcNormFactors.Rd` (default arguments).
- Explain reason: R1 guarantees closeness only to its model’s values, not that those values are edgeR’s documented TMM factors; its tolerance is also 0.023. R1_tight_failure says the third Edge value differs from a different model’s third value by more than 0.001, which does not establish the required factor values.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:10, J4): `bench/runs/fva-tmm-2/work/Proofs/Spec.lean:11`, `Proofs/Model.lean:64-103`, `Proofs/Proof.lean:15`: exact-byte certificate, exact-average ties, all seven absolute errors ≤0.023.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.R1`

```lean
FVA.Cert.Accepted (Proofs.Model.Conforms (23 / 1000)) Proofs.Counts.blob Proofs.Edge.blob
```

`Proofs.R1_tight_failure`

```lean
FVA.Cert.Accepted (Proofs.Model.FailsTight (1 / 1000)) Proofs.Counts.blob Proofs.Edge.blob
```

Ruling (MAIN): shipped M3 `faithful` stands. The claims bind the shipped output bytes to the run's exact-real TMM model within the tolerance the run states (R1/R2 let the run state it); reviewer-24 checked the model against the edgeR/RNAnorm documentation. Explain cannot read the documentation the requirement cites, so it cannot confirm that the model is the documented method: a limit of the requirement-mode check on requirements that cite external documents.

### fva-tmm-2/R2

- Explain = `different`; shipped M3 = `faithful`.
- Requirement: Each value in `rnanorm-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as RNAnorm documents TMM in the docstring of its class `TMM` (default arguments).
- Explain reason: R2 guarantees closeness only to its model’s values, not that those values are RNAnorm’s documented TMM factors; its tolerance is 0.021. R2_tight_failure additionally says the third Rna value differs from another model’s third value by more than 0.001, so these claims do not establish the documented factors.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:11, J5): `bench/runs/fva-tmm-2/work/Proofs/Spec.lean:15`, `Proofs/Model.lean:64-103`, `Proofs/Proof.lean:19`: exact-byte certificate under the same stated tie policy, all seven absolute errors ≤0.021.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.R2_tight_failure`

```lean
FVA.Cert.Accepted (Proofs.Model.FailsTight (1 / 1000)) Proofs.Counts.blob Proofs.Rna.blob
```

`Proofs.R2`

```lean
FVA.Cert.Accepted (Proofs.Model.Conforms (21 / 1000)) Proofs.Counts.blob Proofs.Rna.blob
```

Ruling (MAIN): shipped M3 `faithful` stands. The claims bind the shipped output bytes to the run's exact-real TMM model within the tolerance the run states (R1/R2 let the run state it); reviewer-24 checked the model against the edgeR/RNAnorm documentation. Explain cannot read the documentation the requirement cites, so it cannot confirm that the model is the documented method: a limit of the requirement-mode check on requirements that cite external documents.

### fva-tmm-3/R1

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Each value in `edger-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as edgeR documents TMM in `edgeR/man/calcNormFactors.Rd` (default arguments).
- Explain reason: This only asserts that some Counts and Edge blobs with the stated shapes satisfy an inequality. It does not establish that the fixed files’ values are the edgeR TMM factors, nor does it compare all seven factors with TMM’s documented computation.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:13, J7): `Spec.R1_failure` binds the actual count/output encodings, matrix shape, seven factors and reference 3, then proves shipped sample 3 +0.01 < exact factor. `ScoreData.factor_lower` (`:65`) proves factor >1.14. Shipped value = 1.1253076397204775, so this genuinely refutes the selected tolerance. Exact report anchor: `They do **not** establish failure to reproduce the R or NumPy` (`VERIFICATION.md:7`). The report does not claim that the same file fails its own floating-point producer. Interpretation lemmas additionally check the inactive A cutoff and reference fallback.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.R1_failure`

```lean
∃ xs ds,
  Proofs.Counts.blob.data = Proofs.countBytes xs ∧
    Proofs.Edge.blob.data = Proofs.factorBytes ds ∧
      List.length xs = 454 ∧
        (∀ row ∈ xs, row.length = 7) ∧
          ds.length = 7 ∧
            Proofs.reference xs = 3 ∧ ↑(Proofs.decimalValue (ds[2]?.getD (0, 0))) + 1 / 100 < Proofs.factor xs 2
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-tmm-3/R2

- Explain = `weaker`; shipped M3 = `not proven, reported`.
- Requirement: Each value in `rnanorm-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as RNAnorm documents TMM in the docstring of its class `TMM` (default arguments).
- Explain reason: This only asserts that some Counts and RNA blobs with the stated shapes satisfy an inequality. It does not establish that the fixed files’ values are the RNAnorm TMM factors, nor does it compare all seven factors with TMM’s documented computation.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:14, J8): `Spec.R2_failure` substitutes the full RNAnorm output encoding and shipped sample 3 = 1.1270795948647565; the same >1.14 factor bound gives >0.01 error. Exact policy/tolerance are stated at `VERIFICATION.md:3,79`. Float-runtime conformity is expressly left open (`:125`). The counterexample is neither a silent weakening nor a false positive verification claim.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.R2_failure`

```lean
∃ xs ds,
  Proofs.Counts.blob.data = Proofs.countBytes xs ∧
    Proofs.RNA.blob.data = Proofs.factorBytes ds ∧
      List.length xs = 454 ∧
        (∀ row ∈ xs, row.length = 7) ∧
          ds.length = 7 ∧
            Proofs.reference xs = 3 ∧ ↑(Proofs.decimalValue (ds[2]?.getD (0, 0))) + 1 / 100 < Proofs.factor xs 2
```

Ruling (MAIN): shipped M3 stands. The run refutes the requirement (a machine-checked counterexample: a sound refutation = `not proven, reported`, grading ruling); its claims state a result the requirement rules out, which D64's definitions label `different`; explain's `weaker` is the pre-D64 label confusion these prompts (d8cbbb3) still had. Explain error.

### fva-tmm-4/R1

- Explain = `weaker`; shipped M3 = `faithful`.
- Requirement: Each value in `edger-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as edgeR documents TMM in `edgeR/man/calcNormFactors.Rd` (default arguments).
- Explain reason: This only says the Edge file passes a seven-value check within 1/40; it does not establish that the values match edgeR’s documented TMM factors within a stated, suitably precise tolerance. The certificate model and output bytes are not specified here, so the requirement is not guaranteed.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:16, J10): `bench/runs/fva-tmm-4/work/Proofs/Spec.lean:12-13`, `Proofs/Model.lean:49-90`, `Proofs/Proof.lean:18`: exact-byte parsed-output certificate; exact-average ties, all seven absolute errors ≤0.025.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r1`

```lean
FVA.Cert.Accepted (Proofs.Model.Accurate (1 / 40)) Proofs.Counts.blob Proofs.Edge.blob
```

Ruling (MAIN): shipped M3 `faithful` stands. The claims bind the shipped output bytes to the run's exact-real TMM model within the tolerance the run states (R1/R2 let the run state it); reviewer-24 checked the model against the edgeR/RNAnorm documentation. Explain cannot read the documentation the requirement cites, so it cannot confirm that the model is the documented method: a limit of the requirement-mode check on requirements that cite external documents.

### fva-tmm-4/R2

- Explain = `weaker`; shipped M3 = `faithful`.
- Requirement: Each value in `rnanorm-factors.txt` is, within a tolerance that you state, the TMM normalization factor of its sample for `counts.tsv`, as RNAnorm documents TMM in the docstring of its class `TMM` (default arguments).
- Explain reason: This only says the Rna file passes a seven-value check within 1/40; it does not establish that the values match RNAnorm’s documented TMM factors within a stated, suitably precise tolerance. The certificate model and output bytes are not specified here, so the requirement is not guaranteed.
- Shipped M3 reason (.scratch/teammates/reviewer-24/verdicts.md:17, J11): `bench/runs/fva-tmm-4/work/Proofs/Spec.lean:19-20`, `Proofs/Model.lean:49-90`, `Proofs/Proof.lean:26`: same seven-coordinate guarantee for RNAnorm at stated 0.025, not tight float-runtime verification.
- Claim text (elaborated statements passed to explain; all claims shown if it selected none):

`Proofs.r2`

```lean
FVA.Cert.Accepted (Proofs.Model.Accurate (1 / 40)) Proofs.Counts.blob Proofs.Rna.blob
```

Ruling (MAIN): shipped M3 `faithful` stands. The claims bind the shipped output bytes to the run's exact-real TMM model within the tolerance the run states (R1/R2 let the run state it); reviewer-24 checked the model against the edgeR/RNAnorm documentation. Explain cannot read the documentation the requirement cites, so it cannot confirm that the model is the documented method: a limit of the requirement-mode check on requirements that cite external documents.

## Per-requirement table

| row id | explain | shipped M3 | mapped agreement | claims / failure evidence |
| --- | --- | --- | --- | --- |
| fva-edger-cpm-1/R1 | weaker | not proven, reported | no | Proofs.r2_total_witness, Proofs.r2_rounding_witness, Proofs.r1_counterexample |
| fva-edger-cpm-1/R2 | missing | not proven, reported | yes | none |
| fva-edger-cpm-2/R1 | weaker | not proven, reported | no | Proofs.overflow_witness, Proofs.threshold_witness, Proofs.artifact_arithmetic |
| fva-edger-cpm-2/R2 | missing | not proven, reported | yes | none |
| fva-edger-cpm-3/R1 | weaker | not proven, reported | no | Proofs.artifact_binding, Proofs.r2_rounding_gap, Proofs.r2_cpm_bits, Proofs.r1_overflow |
| fva-edger-cpm-3/R2 | missing | not proven, reported | yes | none |
| fva-edger-cpm-4/R1 | different | not proven, reported | yes | Proofs.r1_overflow |
| fva-edger-cpm-4/R2 | different | not proven, reported | yes | Proofs.r1_overflow |
| fva-edger-cpm-5/R1 | weaker | not proven, reported | no | Proofs.artifact_binding, Proofs.r2_boundary, Proofs.r1_overflow |
| fva-edger-cpm-5/R2 | missing | not proven, reported | yes | none |
| fva-glm-iround-1/R1 | different | not proven, reported | yes | Proofs.r1_counterexample |
| fva-glm-iround-2/R1 | different | not proven, reported | yes | Proofs.R1_counterexample |
| fva-glm-iround-3/R1 | different | not proven, reported | yes | Proofs.r1_counterexample |
| fva-glm-iround-4/R1 | different | not proven, reported | yes | Proofs.R1Counterexample |
| fva-glm-iround-5/R1 | weaker | not proven, reported | no | Proofs.r1_counterexample |
| fva-lz4-c-1/R1 | weaker | not proven, reported | no | Proofs.zeroCapacity, Proofs.emptyBlock |
| fva-lz4-c-1/R2 | weaker | weaker | yes | Proofs.longMatchCase, Proofs.shortcutCase, Proofs.literalCase, Proofs.overlapCase, Proofs.zeroOffsetCase, Proofs.zeroCapacity, Proofs.emptyBlock |
| fva-lz4-c-1/R3 | weaker | weaker | yes | Proofs.zeroCapacity, Proofs.emptyBlock |
| fva-lz4-c-2/R1 | weaker | not proven, reported | no | Proofs.extendedLiterals, Proofs.literalBlock, Proofs.zeroOffset, Proofs.emptyBlockPositive, Proofs.extendedMatch, Proofs.overlappingMatch, Proofs.emptyBlock |
| fva-lz4-c-2/R2 | weaker | weaker | yes | Proofs.extendedLiterals, Proofs.literalBlock, Proofs.zeroOffset, Proofs.emptyBlockPositive, Proofs.extendedMatch, Proofs.overlappingMatch, Proofs.emptyBlock |
| fva-lz4-c-2/R3 | weaker | weaker | yes | Proofs.extendedLiterals, Proofs.literalBlock, Proofs.emptySource, Proofs.zeroOffset, Proofs.zeroCapacityByte, Proofs.emptyBlockPositive, Proofs.extendedMatch, Proofs.overlappingMatch, Proofs.emptyBlock |
| fva-lz4-c-3/R1 | weaker | not proven, reported | no | Proofs.zeroInputRejected, Proofs.regressionCases |
| fva-lz4-c-3/R2 | weaker | weaker | yes | Proofs.zeroInputRejected, Proofs.regressionCases |
| fva-lz4-c-3/R3 | weaker | weaker | yes | Proofs.zeroInputRejected, Proofs.regressionCases |
| fva-lz4-c-4/R1 | missing | not proven, reported | yes | none |
| fva-lz4-c-4/R2 | weaker | weaker | yes | Proofs.literal, Proofs.overlap, Proofs.zero_offset, Proofs.empty_positive, Proofs.shortcut, Proofs.empty_zero, Proofs.literal_extension, Proofs.match_extension |
| fva-lz4-c-4/R3 | weaker | weaker | yes | Proofs.too_small, Proofs.literal, Proofs.bad_offset, Proofs.overlap, Proofs.zero_offset, Proofs.empty_positive, Proofs.shortcut, Proofs.empty_zero, Proofs.no_input, Proofs.literal_extension, Proofs.truncated, Proofs.match_extension |
| fva-lz4-c-5/R1 | weaker | weaker | yes | Proofs.reject_no_input, Proofs.reject_past_offset, Proofs.source_at_end, Proofs.overlap_match, Proofs.empty_room, Proofs.reject_zero_capacity, Proofs.zero_offset, Proofs.destination_at_end, Proofs.one_literal, Proofs.empty_zero, Proofs.extended_match, Proofs.extended_literals |
| fva-lz4-c-5/R2 | weaker | weaker | yes | Proofs.source_at_end, Proofs.overlap_match, Proofs.empty_room, Proofs.zero_offset, Proofs.destination_at_end, Proofs.one_literal, Proofs.empty_zero, Proofs.extended_match, Proofs.extended_literals |
| fva-lz4-c-5/R3 | weaker | weaker | yes | Proofs.source_at_end, Proofs.overlap_match, Proofs.empty_room, Proofs.zero_offset, Proofs.destination_at_end, Proofs.one_literal, Proofs.empty_zero, Proofs.extended_match, Proofs.extended_literals |
| fva-lz4-rust-1/R1 | missing | not proven, reported | yes | Proofs.empty_input_preserves_store, Proofs.concrete_examples, Proofs.initializes |
| fva-lz4-rust-1/R2 | weaker | weaker | yes | Proofs.concrete_examples |
| fva-lz4-rust-1/R3 | missing | weaker | no | none |
| fva-lz4-rust-2/R1 | missing | not proven, reported | yes | none |
| fva-lz4-rust-2/R2 | weaker | weaker | yes | Proofs.one_literal |
| fva-lz4-rust-2/R3 | weaker | weaker | yes | Proofs.empty_block, Proofs.zero_offset, Proofs.one_literal, Proofs.zero_input |
| fva-lz4-rust-3/R1 | weaker | weaker | yes | Proofs.wide64, Proofs.fast_wild_copy, Proofs.small_capacity, Proofs.relaxed_end, Proofs.empty_block, Proofs.zero_offset, Proofs.wide32, Proofs.truncated_literals, Proofs.hello_block, Proofs.truncated_length, Proofs.extended_match, Proofs.external_offset, Proofs.overlap_one, Proofs.truncated_offset, Proofs.extended_literals, Proofs.overlap_two, Proofs.fast_overlap |
| fva-lz4-rust-3/R2 | weaker | weaker | yes | Proofs.wide64, Proofs.fast_wild_copy, Proofs.relaxed_end, Proofs.wide32, Proofs.hello_block, Proofs.extended_match, Proofs.overlap_one, Proofs.extended_literals, Proofs.overlap_two, Proofs.fast_overlap |
| fva-lz4-rust-3/R3 | weaker | weaker | yes | Proofs.wide64, Proofs.fast_wild_copy, Proofs.small_capacity, Proofs.relaxed_end, Proofs.empty_block, Proofs.zero_offset, Proofs.wide32, Proofs.truncated_literals, Proofs.hello_block, Proofs.truncated_length, Proofs.extended_match, Proofs.external_offset, Proofs.overlap_one, Proofs.truncated_offset, Proofs.extended_literals, Proofs.overlap_two, Proofs.fast_overlap |
| fva-lz4-rust-4/R1 | different | not proven, reported | yes | Proofs.artifactProfile, Proofs.artifactInitializes, Proofs.zeroLengthRejected, Proofs.emptyBlockDecoded |
| fva-lz4-rust-4/R2 | different | weaker | no | Proofs.artifactProfile, Proofs.artifactInitializes, Proofs.zeroLengthRejected, Proofs.emptyBlockDecoded |
| fva-lz4-rust-4/R3 | different | weaker | no | Proofs.artifactProfile, Proofs.artifactInitializes, Proofs.zeroLengthRejected, Proofs.emptyBlockDecoded |
| fva-lz4-rust-5/R1 | missing | not proven, reported | yes | none |
| fva-lz4-rust-5/R2 | weaker | weaker | yes | Proofs.literalBlock, Proofs.overlappingBlock, Proofs.emptyBlock |
| fva-lz4-rust-5/R3 | weaker | weaker | yes | Proofs.literalBlock, Proofs.overlappingBlock, Proofs.emptyBlock |
| fva-lz4-wasm-3/R1 | weaker | not proven, reported | no | Proofs.r1, Proofs.r2 |
| fva-lz4-wasm-3/R2 | weaker | not proven, reported | no | Proofs.emptyBlockTrap, Proofs.r3, Proofs.r2 |
| fva-lz4-wasm-3/R3 | missing | not proven, reported | yes | Proofs.emptyBlockTrap, Proofs.r3, Proofs.r2 |
| fva-lz4-wasm-4/R1 | weaker | not proven, reported | no | Proofs.r1_counterexample |
| fva-lz4-wasm-4/R2 | weaker | not proven, reported | no | Proofs.r3_counterexample, Proofs.r2_counterexample |
| fva-lz4-wasm-4/R3 | missing | not proven, reported | yes | none |
| fva-lz4-wasm-5/R1 | different | not proven, reported | yes | Proofs.r1_counterexample |
| fva-lz4-wasm-5/R2 | weaker | not proven, reported | no | Proofs.r3_counterexample, Proofs.r2_counterexample |
| fva-lz4-wasm-5/R3 | missing | not proven, reported | yes | none |
| fva-lz4-wasm-6/R1 | weaker | not proven, reported | no | Proofs.preparation, Proofs.r1 |
| fva-lz4-wasm-6/R2 | weaker | not proven, reported | no | Proofs.r3_dependence, Proofs.r3, Proofs.r2 |
| fva-lz4-wasm-6/R3 | missing | not proven, reported | yes | Proofs.r3 |
| fva-lz4-wasm-7/R1 | missing | not proven, reported | yes | Proofs.r3_counterexample, Proofs.r2_counterexample |
| fva-lz4-wasm-7/R2 | weaker | not proven, reported | no | Proofs.r2_counterexample |
| fva-lz4-wasm-7/R3 | missing | not proven, reported | yes | Proofs.r3_counterexample, Proofs.r2_counterexample |
| fva-tmm-1/R1 | different | faithful | no | Proofs.tightAccuracyFails, Proofs.R2, Proofs.R1 |
| fva-tmm-1/R2 | different | faithful | no | Proofs.R2, Proofs.R3Fails |
| fva-tmm-1/R3 | different | not proven, reported | yes | Proofs.R3Fails |
| fva-tmm-2/R1 | different | faithful | no | Proofs.R1, Proofs.R1_tight_failure |
| fva-tmm-2/R2 | different | faithful | no | Proofs.R2_tight_failure, Proofs.R2 |
| fva-tmm-2/R3 | different | not proven, reported | yes | Proofs.R3_failure |
| fva-tmm-3/R1 | weaker | not proven, reported | no | Proofs.R1_failure |
| fva-tmm-3/R2 | weaker | not proven, reported | no | Proofs.R2_failure |
| fva-tmm-3/R3 | different | not proven, reported | yes | Proofs.R3_failure |
| fva-tmm-4/R1 | weaker | faithful | no | Proofs.r1 |
| fva-tmm-4/R2 | weaker | faithful | no | Proofs.r2 |
| fva-tmm-4/R3 | different | not proven, reported | yes | Proofs.r3_witness, Proofs.r3_failure |
| fva-tmm-5/R1 | different | not proven, reported | yes | Proofs.R1_failure |
| fva-tmm-5/R2 | different | not proven, reported | yes | Proofs.R3_failure |
| fva-tmm-5/R3 | different | not proven, reported | yes | Proofs.R1_failure, Proofs.R3_failure, Proofs.R2_failure |

## Attempts + limits

- Initial clean-pass build failures: `fva-lz4-c-2` (rc 2; `Proofs/Startup.lean:71:40: Unknown identifier FVA.Wasm.Valid.InitProof.steps_values`), `fva-lz4-rust-1` (rc 2; `Proofs/Execution.lean:21:20: Unknown identifier FVA.Wasm.Valid.InitProof.steps_values`), and `fva-lz4-rust-5` (rc 2; `Proofs.ZeroOffset`: `Lean exited with code 137`). Initial outputs/rc/metadata = `out/retries/<run>/attempt-1/`. Exit 137 alone does not prove an OOM cause.
- MAIN-approved proof compatibility: exactly one body-only name replacement in each of `fva-lz4-c-2/Proofs/Startup.lean` and `fva-lz4-rust-1/Proofs/Execution.lean`, `FVA.Wasm.Valid.InitProof.steps_values` → `FVA.Wasm.Exec.Ref.steps_values`. Every spec and theorem statement stays byte-identical (apart from spec claim marks/import); every other archived Lean file stays byte-identical. Exact diffs = `out/<run>.proof-api.diff`; original/migrated SHA + replacement counts = `out/proof-api-migrations.json`. The validator permits those two exact replacements alone, and fresh `fva trust` checks the migrated proofs.
- `fva-lz4-rust-5` retried unchanged after other modules cached, under the same 20 GiB/no-swap cap: build and explanation completed, all three labels are comparable, but fresh trust is FAIL (`con-leche timed out the export`; `no kernel outside Lean's own lineage accepted the export`). Its mapped 3/3 is not a fresh proof PASS. Sequence = `out/current.log`, `out/retry-rust5.log`, then the two API reruns in `out/api-reruns.log`.
- Runtime-example coverage: the clean worktree has no `.tools/`, hence no `.tools/bin/wasmtime` (`binaryValue` calls this exact path). No binary-output validation is claimed. The requirement comparison uses the claim statements and generated explanations; rendered example status alone is not evidence that the shipped binary traps. This limit does not justify rerunning the language-model judgments.
- Reported comparison batch = clean revision `d8cbbb324e46f8f435ea842bbf129f0008cbb68e`; private detached worktree `.scratch/worktrees/explainer-d56`; binary sha256 `4a7e0f4324e27c0ff59e682221d343f3c7fe28ddf1f5a5ad017b109de545b0d2`. `lake build fva` and `scripts/fetch-canaries` passed there; build log = `out/prepare-clean.log`. Every run uses this worktree's binary; MAIN's mutable working binary is excluded. Model/effort = shipped defaults (`gpt-6-luna`, `medium`).
- Sandbox-compatible dependencies = one owned, clean-revision `fva init` package at `build/clean-package/fva`, with a private copy of the benchmark's pinned package store under its `.lake/packages`. Each scratch project points `fva/` there and rewrites only `packagesDir` in its manifest/lakefile to `fva/.lake/packages`. Per-run patches + dependency provenance = `out/<run>.package.diff` and `out/<run>.package.json`. Spec text stays unchanged except the explicit claim marks/import; proof edits are limited to the two body-only qualified names above.
- Superseded dirty-snapshot diagnostics = `out/diagnostic-dirty-snapshot/` (two completed explanations, then the batch stopped with rc 143). Those outputs and saved texts are excluded from the reported comparison. All thirty clean-revision attempts start without a saved explanation; a diagnostic error is not counted unless the clean batch reproduces it.
- Original pass: 30/30 archives rebuilt by `bench/grade/rebuild`; 30/30 current `fva explain … --requirements … --json` invocations attempted serially under a 20 GiB memory cap. Every invocation exited 2 before a model call: `fva explain: fva trust gave no report (rc 1)`. Empty stdout `.json` files are retained as raw command output, not represented as valid JSON. Stderr, rc, command metadata and rebuild logs = `out/original/`; sequence = `out/baseline.log`.
- Root cause confirmed with the sandbox's own `spawnArgs`: historical `packagesDir` points outside the project at the benchmark's shared package store; today's sandbox covers that path. Diagnostic (`out/sandbox-build-probe.log`, rc 1): `info: mathlib: materializing new dependency`; `error: read-only file system (error code: 30)`; `file: ~/.cache`. The unchanged GLM-1 project builds outside that sandbox (`out/fva-glm-iround-1.build.log`, rc 0, 1596 jobs); that successful build does not establish proof validity.
- Compatibility adaptation, scratch only: 147 claim definitions named by the archived trust reports receive `@[fva_claim]` and an explicit `import FVA.Spec.ClaimAttr`. Removing exactly those additions restores all 30 archived Spec files byte-for-byte. Per-run names + report provenance = `out/legacy-claims.json`; exact patches = `out/<run>.spec.diff`. Archived `bench/runs/**` files remain read-only.
- Requirement files = README preamble/interface + shared-domain conditions + exact requirement wording under `## R1` etc. Only context headings are demoted to `###` so they do not become requirements. Six files reused across five runs each; 75 requirements total.
- Shipped M3 census = 6 `faithful`, 22 `weaker`, 47 `not proven, reported`. Sources = reviewer decks 12, 18, 24, 37, 47, 55, each row retained in `out/m3.json` with reason and source anchor. T1 fva-7 R3 uses MAIN's shipped override (`bench/results.md`, `.scratch/u15/reruling.md`), not reviewer-12's superseded `weaker`.
- Original-pass binary sha256 = `68bbcffdd6e6a4fa6da8162fca7b89bac4e9add3005bf80bb6e79f2aeece7bb7`; Codex = 0.166.0 (original graded runs used 0.163.0). This is a post-hoc explanation exercise, not a new graded batch. No agreement percentage can be computed from execution failures.

explainer-d56-DONE-2
