#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification/.build
out=verification/.build
python3 -I verification/extract.py
python3 -I verification/cases.py
lake build
lake build Proofs.Calibration
names=(Verification.empty_input)
for ((i=0;i<38;i++)); do names+=("Verification.checked$i"); done
lake env leanexport Proofs.Cases -- "${names[@]}" > "$out/proofs.ndjson"
python3 -I verification/exports.py audit "$out/proofs.ndjson"
lake env leanexport Proofs.Calibration -- Calibration.truth Calibration.arithmetic Calibration.falseType > "$out/calibration.ndjson"
python3 -I verification/exports.py negative "$out/calibration.ndjson" "$out"
cat > "$out/nanoda.json" <<'JSON'
{"use_stdin":true,"permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"print_success_message":true}
JSON
replay() {
  case "$1" in
    lean) lake env leanchecker --from-export "$2" ;;
    con-ron) /opt/lean/bin/con-ron --verified --jobs=1 "$2" ;;
    nanoda) /opt/lean/bin/nanoda_bin "$out/nanoda.json" < "$2" ;;
  esac
}
for kernel in lean con-ron nanoda; do
  echo "Checking all proof dependencies with $kernel"
  replay "$kernel" "$out/proofs.ndjson" > "$out/$kernel-valid.log" 2>&1
  cat "$out/$kernel-valid.log"
  replay "$kernel" "$out/calibration.ndjson" > "$out/$kernel-calibration.log" 2>&1
  for fixture in truth arithmetic; do
    set +e
    replay "$kernel" "$out/$fixture-false.ndjson" > "$out/$kernel-$fixture-negative.log" 2>&1
    status=$?
    set -e
    expected_status=1
    rejection_pattern='type mismatch'
    if [[ $kernel == nanoda ]]; then
      expected_status=101
      rejection_pattern='assertion failed: self.def_eq'
    fi
    if [[ $status != "$expected_status" ]] || ! rg -q "$rejection_pattern" "$out/$kernel-$fixture-negative.log"; then
      cat "$out/$kernel-$fixture-negative.log"
      echo "FAIL: $kernel false-proof control exited $status; expected a type-checking rejection" >&2
      exit 1
    fi
    echo "$kernel rejected $fixture false proof (exit $status)"
  done
done
node verification/runtime.js
python3 -I verification/make_wast.py "$out/cases.wast"
wasmtime wast -C cache=n "$out/cases.wast"
echo 'Wasmtime: 38 original-artifact executions agree'
python3 -I verification/sizes.py
echo 'PASS: partial results checked; universal R1/R2/R3 remain UNPROVED (see VERIFICATION.md)'
