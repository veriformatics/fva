# Verification of glm-iround.wasm

R1 **fails**. The shipped module returns `1` on the binary64 input with bits
`0x3fdfffffffffffff`, although `0` is strictly closer to that input. This input is
finite and satisfies both required bounds. There are no other numbered
requirements in README.md.

## Machine-checked result

The theorem in `Proofs/Proof.lean` is exactly:

```lean
theorem R1_counterexample_holds : R1_counterexample
```

Its fully qualified name is `Proofs.R1_counterexample_holds`. The claim is defined
in `Proofs/Spec.lean`, with the following exact statement (inside namespace
`Proofs`, opening `FVA.Wasm`, `FVA.Wasm.Exec`, and `FVA.Wasm.Num`):

```lean
def R1_counterexample : Prop :=
  let b : BitVec 64 := 0x3fdfffffffffffff
  let x := ofBits f64fmt b
  x.IsNum ∧
  x.toReal f64fmt = (9007199254740991 : ℝ) / 18014398509481984 ∧
  0 ≤ x.toReal f64fmt ∧ x.toReal f64fmt ≤ 2147483647 ∧
  Returns Lifted.module "iround" [.f64 b] [.i32 1] ∧
  |x.toReal f64fmt - (0 : ℝ)| < |x.toReal f64fmt - (1 : ℝ)|
```

Here `IsNum` excludes infinities and NaNs. `Returns` includes successful
instantiability and guarantees termination, no trap, and the specified result
under every host semantics and from every fresh instance. The final strict
inequality supplies an integer closer than the actual result; it directly
contradicts R1's nearest-integer requirement, including its permission for either
answer at a tie. We prove this counterexample, not the false universal R1.

The exact input is `1/2 - 2^(-54)`, approximately
`0.49999999999999994`. Its distance to `0` is `1/2 - 2^(-54)` and its distance to
`1` is `1/2 + 2^(-54)`. The artifact adds binary64 `0.5` and then executes
`i32.trunc_sat_f64_s`. The exact sum before floating-point rounding is
`1 - 2^(-54)`, halfway between adjacent binary64 values; ties-to-even rounds it
to `1.0`. Truncation therefore returns `1`. The Lean proof checks the addition
and conversion with FVA's executable numerics and uses FVA's soundness and
uniqueness proofs to establish the full `Returns` property.

## Connection to the shipped bytes

The subject is the unchanged 66-byte `glm-iround.wasm`, SHA-256:

```text
eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
```

`Proofs/Lifted.lean` was generated with `fva lift`. It embeds all 66 bytes as a
numeral, names `glm-iround.wasm` as its source, and defines the decoded module.
Its kernel-checked theorem is:

```lean
theorem decode_eq : decode bytes len = .ok module
```

The counterexample refers to that module. FVA's trust check compares the embedded
bytes with the shipped file, checks the generated lift, and independently replays
`decode_eq` together with the claim and proof. No source-code model, recompilation,
or assumption about the C++ compiler is used.

## Reproduction (offline, from this directory)

First build and check the artifact identity:

```sh
lake build
sha256sum glm-iround.wasm
```

The build must exit zero and print `Build completed successfully`; the hash must
match the value above. To run FVA from a separate package outside the project,
copy its unchanged sources and prebuilt libraries into a fresh temporary directory,
then force the executable to be linked there.
Only the copied package's dependency-location metadata is adjusted to use the
already installed packages:

```sh
checker_dir=$(mktemp -d /tmp/fva-iround-checker.XXXXXX)
cp -a fva/. "$checker_dir/"
python3 - "$checker_dir" <<'PY'
import json
import pathlib
import sys
root = pathlib.Path.cwd()
manifest = pathlib.Path(sys.argv[1]) / 'lake-manifest.json'
data = json.loads(manifest.read_text())
packages = json.loads((root / 'lake-manifest.json').read_text())['packagesDir']
data['packagesDir'] = str((root / packages).resolve())
manifest.write_text(json.dumps(data, indent=1) + '\n')
PY
rm "$checker_dir/.lake/build/bin/fva"
lake -d "$checker_dir" build fva
"$checker_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 30 > FVA-TRUST.txt
cat FVA-TRUST.txt
```

A warning about the copied manifest's packages directory changing is harmless;
no dependency download is required. The audit must exit zero with `PASS`, list
`Proofs.R1_counterexample` as proven and attached to the artifact, accept kernel
replays, and report no issues. `PASS` certifies the counterexample claim; it does
**not** mean R1 passes.

A separate runtime reproduction is:

```sh
XDG_CACHE_HOME=/tmp/fva-wasmtime-cache \
  wasmtime run --invoke iround glm-iround.wasm 0.49999999999999994
```

It prints `1` (experimental `--invoke` warnings may also appear). This runtime
check is corroboration; the Lean theorem supplies the formal result.

## Observed audit result

The external checker at `/tmp/fva-glm-iround-checker/.lake/build/bin/fva`
returned exit status 0 and `fva trust: PASS`. The report is saved in
`FVA-TRUST.txt`. It reported:

- `Proofs.R1_counterexample` proved by `Proofs.R1_counterexample_holds`.
- Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `leanchecker`: accepted (157 seconds); `con-leche`: accepted (113 seconds).
- `Proofs.Lifted (glm-iround.wasm) [lifted]: matches`.
- Review surface: **13 code lines**, all in `Proofs.Spec`.

Of 72 known-false canaries, leanchecker rejected 71 and accepted one;
con-leche rejected 69 and declined three. The Lean acceptance is a pinned,
known acceptance in FVA's `trust/canaries/known.tsv`; the audit policy permits
it because an independent kernel rejects that canary. No canary crashed or
timed out. Thus this report does not claim that every kernel rejected every
canary.

## Review and trust

The project-specific meaning to review is `Proofs/Spec.lean`: 21 physical lines,
766 bytes. It uses only FVA's specification vocabulary and the generated lift;
there are no custom execution models or axioms. `Proofs/Proof.lean` has 58 physical
lines, 2300 bytes, and `Proofs/Lifted.lean` has 42 physical lines, 1452 bytes.
These proofs and the generated decoding are machine checked. The one-line
`Proofs.lean` imports the proof; `lakefile.toml` has 15 lines and configures the
local FVA dependency. The shell/Python commands above only prepare the external
checker and invoke checks; they do not generate evidence or supply axioms.

The shared trust boundary is FVA's Wasm binary grammar, execution semantics,
IEEE-754 real-number semantics, claim vocabulary, and trust rules
(`fva/FVA/Spec/`: 23 files, 3606 physical lines, 161903 bytes), plus Lean
4.35.0, the pinned Mathlib v4.35.0, and the compiler and tool orchestration.
The main FVA audit glue (`FVA/Trust/*.lean` and
`FVA/Tool/Trust.lean`) totals 5 files, 1196 physical lines, 56949 bytes. FVA's
decoder, stepper, numerical implementation, and uniqueness proofs are verified against those specifications. The audit checks
proof dependencies for unsupported axioms and overrides, links the artifact,
and replays the exported proofs in Lean's checker and the independent con-leche
kernel, with known-false canaries. FVA sources were not modified.
