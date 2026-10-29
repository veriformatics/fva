#!/usr/bin/env python3
"""Offline, fail-closed reproduction of the R1 counterexample and kernel checks."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess

if not __debug__:
    raise RuntimeError("Run without Python optimization so assertions are checked")

ROOT = Path(__file__).resolve().parent
WORK = ROOT / ".verification"
WORK.mkdir(exist_ok=True)


def run(args, *, reject=False, save=None):
    p = subprocess.run([str(a) for a in args], cwd=ROOT, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    if save is not None:
        save.write_text(p.stdout)
    if (p.returncode != 0) != reject:
        raise RuntimeError(f"Unexpected exit {p.returncode}: {args}\n{p.stdout}{p.stderr}")
    return p.stdout + p.stderr if reject else p.stdout


def read_export(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    names = {0: ""}
    for row in rows:
        if "in" in row:
            name = row.get("str", row.get("num"))
            names[row["in"]] = (names[name["pre"]] + "." if name["pre"] else "") + str(
                name.get("str", name.get("i")))
    return rows, names


artifact = ROOT / "glm-iround.wasm"
data = artifact.read_bytes()
assert len(data) == 66
assert hashlib.sha256(data).hexdigest() == "eded7ae1f3c1ba100d618a98f8f86eb690577a8358e47e31f2039eb2f4a75a3a"
run(["wasm-tools", "validate", artifact])
run(["wasm-tools", "print", artifact], save=WORK / "artifact.wat")
bits = 0x3FDFFFFFFFFFFFFF
exponent = (bits >> 52) & 2047
assert bits >> 63 == 0 and 0 < exponent < 2047
# Positive normal binary64: (2^52 + fraction) * 2^(exponent - 1075).
n = (1 << 52) + (bits & ((1 << 52) - 1))
d = 1 << (1075 - exponent)
assert (n, d) == (9007199254740991, 18014398509481984)
# Supply the exact bit pattern, without a decimal floating-point CLI conversion.
wrapper = WORK / "invoke.wat"
wrapper.write_text(f'''(module
  (import "artifact" "iround" (func $iround (param f64) (result i32)))
  (func (export "run") (result i32)
    i64.const {bits}
    f64.reinterpret_i64
    call $iround))
''')
result = int(run(["wasmtime", "run", "-C", "cache=n", "--preload",
                  f"artifact={artifact}", "--invoke", "run", wrapper]).strip())
assert result == 1
assert abs(n) < abs(n - result * d)
print(f"Artifact: exact bits {bits:#018x}, x={n}/{d}, iround(x)={result}", flush=True)

bin_dir = Path(run(["lean", "--print-prefix"]).strip()) / "bin"
lib = ROOT / ".lake/build/lib/lean"
(lib / "Proofs").mkdir(parents=True, exist_ok=True)
# Always recompile the sources; never rely on cached project proof objects.
run(["lake", "env", "lean", "-o", lib / "Proofs/Counterexample.olean",
     "Proofs/Counterexample.lean"])
observation = WORK / "Observation.lean"
observation.write_text(f'''import Proofs.Counterexample
theorem observation_link :
    ({bits} : Nat) = 1021 * 2^52 + (2^52 - 1) ∧
    (0 : Nat) < 1021 ∧ (1021 : Nat) < 2047 ∧
    Counterexample.numerator = Int.ofNat (2^52 + (2^52 - 1)) ∧
    Counterexample.denominator = Int.ofNat (2^(1075 - 1021)) ∧
    Counterexample.output = {result} := by decide +kernel
''')
run(["lake", "env", "lean", "-o", lib / "Observation.olean", observation])
proofs = WORK / "proofs.ndjson"
run(["lake", "env", bin_dir / "leanexport", "Observation", "--",
     "Counterexample.domain_and_strictly_closer", "Counterexample.r1_counterexample",
     "observation_link"], save=proofs)
rows, names = read_export(proofs)
axioms = [names[r["axiom"]["name"]] for r in rows if "axiom" in r]
assert axioms == []
print(f"Proof export: {len(rows)} records, {proofs.stat().st_size} bytes, axioms={axioms}", flush=True)

# A well-formed positive control; corrupt ONLY a theorem's claimed type below.
controls = WORK / "Controls.lean"
controls.write_text('''import Init
def falseType : Prop := False
def unequalType : Prop := (0 : Nat) = 1
theorem trueProof : True := True.intro
theorem equalityProof : (0 : Nat) = 0 := rfl
''')
run(["lake", "env", "lean", "-o", lib / "Controls.olean", controls])
positive = WORK / "positive.ndjson"
run(["lake", "env", bin_dir / "leanexport", "Controls", "--", "falseType",
     "unequalType", "trueProof", "equalityProof"], save=positive)
control_rows, control_names = read_export(positive)
negative_files = []
for theorem, target in [("trueProof", "falseType"), ("equalityProof", "unequalType")]:
    altered = copy.deepcopy(control_rows)
    target_type = next(r["def"]["value"] for r in altered
                       if "def" in r and control_names[r["def"]["name"]] == target)
    victim = next(r["thm"] for r in altered
                  if "thm" in r and control_names[r["thm"]["name"]] == theorem)
    victim["type"] = target_type
    path = WORK / f"negative-{theorem}.ndjson"
    path.write_text("".join(json.dumps(r) + "\n" for r in altered))
    negative_files.append(path)

for kernel in ["leanchecker", "leanchecker-paranoid", "nanoda_bin"]:
    for path in [proofs, positive, *negative_files]:
        reject = path in negative_files
        if kernel == "nanoda_bin":
            config = WORK / "nanoda.json"
            config.write_text(json.dumps({
                "export_file_path": str(path),
                "permitted_axioms": [],
                "unpermitted_axiom_hard_error": True,
                "nat_extension": True, "string_extension": True,
                "print_success_message": True,
            }))
            command = [bin_dir / kernel, config]
        else:
            command = [bin_dir / kernel, "--from-export", path]
        output = run(command, reject=reject)
        (WORK / f"{kernel}-{path.stem}.log").write_text(output)
        # Require an actual checking success message, in addition to exit status.
        if not reject:
            assert ("accepts the solution" in output if kernel != "nanoda_bin"
                    else "no typechecker errors" in output)
        else:
            assert ("declaration type mismatch" in output if kernel != "nanoda_bin"
                    else "assertion failed: self.def_eq" in output)
    print(f"{kernel}: proof and positive control ACCEPT; False and 0=1 proofs REJECT", flush=True)

assert artifact.read_bytes() == data
print("PASS: R1 is refuted for the pinned shipped artifact; all kernel controls passed.")
