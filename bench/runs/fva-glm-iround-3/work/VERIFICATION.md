# Verification of `glm-iround.wasm`

## Result: R1 fails

The counterexample is the binary64 input with bits `0x3fdfffffffffffff`:

```text
x = 9007199254740991 / 18014398509481984
  = 0.499999999999999944488848768742172978818416595458984375
```

This is the representable value immediately below `0.5`. It is finite and
belongs to `[0, 2147483647]`. The shipped export returns the signed i32 integer
`1`, although integer `0` is strictly closer to `x`. This is a strict failure,
not a halfway case covered by R1's tie allowance.

The artifact executes `local.get 0; f64.const 0.5; f64.add;
i32.trunc_sat_f64_s`. The exact sum `x + 0.5 = 1 - 2^-54` rounds to binary64
`1.0`, which the conversion maps to integer `1`.

## Exact machine-checked statement

The theorem in [Proofs/Proof.lean](Proofs/Proof.lean) is:

```lean
theorem Proofs.r1_counterexample_holds : Proofs.r1_counterexample
```

Its complete claim, from [Proofs/Spec.lean](Proofs/Spec.lean), is the following
(inside namespace `Proofs`, with `FVA.Wasm`, `FVA.Wasm.Exec`, and
`FVA.Wasm.Num` open):

```lean
def r1_counterexample : Prop :=
  let b : BitVec 64 := 0x3fdfffffffffffff
  let x := ofBits f64fmt b
  x.IsNum ∧
  x.toReal f64fmt = (9007199254740991 : ℝ) / 18014398509481984 ∧
  0 ≤ x.toReal f64fmt ∧ x.toReal f64fmt ≤ 2147483647 ∧
  Returns Lifted.module "iround" [.f64 b] [.i32 1] ∧
  |x.toReal f64fmt - (0 : ℝ)| < |x.toReal f64fmt - (1 : ℝ)|
```

`IsNum` excludes NaNs and infinities. `toReal` is FVA's exact real value of the
binary64 input. `Returns` includes successful instantiability and says that,
under every host semantics and from every fresh instance, every execution
terminates without trapping and returns exactly the listed result. The final
strict inequality proves that the returned integer is not nearest. The proof
uses FVA's verified deterministic evaluator for this concrete call (16 units
of evaluator fuel suffice); the claim itself has no fuel restriction. The
input decoding and real arithmetic are also proved in Lean.

R1 is the only requirement in `README.md`; this counterexample refutes its
universal assertion. No claim of correctness over its remaining inputs is
made.

## Connection to the shipped bytes

[Proofs/Lifted.lean](Proofs/Lifted.lean) was generated with FVA from the existing
artifact, without rebuilding or changing it. It contains all 66 bytes as a
packed numeral, their length and source path, the decoded module, and:

```lean
theorem Proofs.Lifted.decode_eq :
  FVA.Wasm.Decode.decode Proofs.Lifted.bytes Proofs.Lifted.len =
    .ok Proofs.Lifted.module
```

The kernel checks this decoder equation. FVA's trust command additionally
compares the numeral with `glm-iround.wasm`, checks the generated module
against regenerated output, and independently replays the decoder equation
and the counterexample proof. Thus the result concerns the actual Wasm
artifact under FVA's WebAssembly semantics, rather than a separate model of
the C++ source. Its SHA-256 is:

```text
eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a
```

## Rechecking

Run from this directory with the supplied Lean 4.35.0, Mathlib v4.35.0,
prebuilt dependencies, and kernel executables on the installed toolchain.
No network or C++ compiler is needed.

```bash
sha256sum glm-iround.wasm
lake build
```

The hash must equal the value above, and `lake build` must exit zero with
`Build completed successfully`.

Use an FVA checker outside the judged project for the final verdict. The
following commands construct one from the supplied, unchanged FVA package;
only its dependency-location configuration is adjusted. They reuse the
installed dependency cache and force the checker executable to be rebuilt.

```bash
set -e
checker_dir=$(mktemp -d /tmp/fva-iround-checker.XXXXXX)
cp -a fva/. "$checker_dir/"
python3 - "$checker_dir" <<'PY'
import json
import sys
from pathlib import Path

root = Path(sys.argv[1])
packages = json.loads(Path('lake-manifest.json').read_text())['packagesDir']
manifest = root / 'lake-manifest.json'
data = json.loads(manifest.read_text())
data['packagesDir'] = packages
manifest.write_text(json.dumps(data, indent=2) + '\n')
config = root / 'lakefile.toml'
config.write_text(config.read_text().replace(
    'version = "0.1.0"',
    'version = "0.1.0"\npackagesDir = "' + packages + '"'))
for name in ['fva', 'fva.hash', 'fva.trace', 'fva.rsp']:
    (root / '.lake/build/bin' / name).unlink(missing_ok=True)
PY
lake -d "$checker_dir" build fva
"$checker_dir/.lake/build/bin/fva" trust . \
  --spec-module Proofs.Spec --root-module Proofs --surface-budget 20
```

Success is exit status zero and `fva trust: PASS`, with the counterexample
claim proved, the artifact linked, and both `leanchecker` and `con-leche`
accepting replay. A PASS certifies the stated counterexample; R1 itself
fails. The recorded report is [verification-trust.txt](verification-trust.txt).

The completed run used `/tmp/fva-glm-iround-checker/.lake/build/bin/fva`:
`leanchecker` accepted replay in 136 seconds and `con-leche` in 99 seconds.
The link matched and the measured review surface was 13 code lines. Of 72
known-false canaries, Lean rejected 71 and accepted its documented
replaced-prelude case; `con-leche` rejected 69 (including that case) and
declined 3. There were no crashes or timeouts. FVA's coverage and known
acceptance rules passed. The theorem's only axioms are the standard
`propext`, `Classical.choice`, and `Quot.sound`.

For an additional runtime reproduction:

```bash
XDG_CACHE_HOME=/tmp/fva-wasmtime-cache \
  wasmtime run --invoke iround glm-iround.wasm 0.49999999999999994
```

This prints `1` (wasmtime also emits experimental-interface warnings). This
runtime check corroborates the Lean proof and is not a proof assumption.

## Review and trust surface

The application-specific statement to review is `Proofs/Spec.lean`: 13 code
lines, 20 physical lines, 723 bytes, including its explanation and imports. It states
the finite input, domain, actual return, and strict error comparison
together. Match it to R1 in `README.md`. There is no application-specific
axiom, source model, or unproved arithmetic assumption.

`Proofs/Proof.lean` is 40 lines / 1,409 bytes; `Proofs/Lifted.lean` is 42 lines
/ 1,452 bytes; `Proofs.lean` is one line / 20 bytes. Their proofs and the
artifact link are checked by FVA and replayed by the kernels, so their proof
strategies and the lifting elaborator need not be trusted. The shell/Python
recipe above locates and builds the checker; it contributes no semantic
assumption about the program. The runtime command contributes no assumption.

The shared base is the supplied FVA package, unchanged. Its `FVA/Spec/`
definitions comprise 23 Lean files, 3,606 physical lines, 161,903 bytes. These
define Wasm decoding, execution, IEEE floating-point values and rounding,
and the claim/trust vocabulary. The verdict collection/orchestration files
(`FVA/Trust/*.lean` and `FVA/Tool/Trust.lean`) comprise 5 files, 1,196 lines,
56,949 bytes. Conservatively, the entire supplied FVA Lean package is 129
files, 24,215 lines, 1,106,254 bytes, including machine-checked implementation
proofs and unrelated facilities. FVA recognizes its base by content hashes.

Residual trust is the installed Lean compiler and kernel, the independent
replay kernel, the official Lean prelude, the pinned Mathlib/dependency
installation, the exporter and OS/file/process/hash tooling. The Mathlib
revision is `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0), as recorded
in `lake-manifest.json`. FVA checks kernel canaries and lists its trust
boundary and measured review surface in the report. The C++ headers,
wrapper, build script, C++ compiler, and wasmtime are not assumptions of the
formal result; the README's identification of which artifact to check and
its intended requirement remain the reviewer's responsibility.
