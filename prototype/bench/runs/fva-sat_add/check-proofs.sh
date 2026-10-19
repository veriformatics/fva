#!/bin/sh
# Rebuild/lift the shipped artifact and replay the three proofs, offline.
# Run the installed kernel executables directly: this also works when the
# surrounding environment cannot create Lake's additional bubblewrap sandbox.
set -eu
cd "$(dirname "$0")"
mkdir -p .lake/verification

clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--strip-all \
  -Wl,--export=sat_add -o .lake/verification/sat_add.wasm sat_add.c
cmp sat_add.wasm .lake/verification/sat_add.wasm
printf '%s\n' 'C rebuild matches shipped WebAssembly: PASS'

uv run --offline --project ../.. fva lift sat_add.wasm \
  .lake/verification/Lifted.lean --ns SatAdd.Lifted
cmp SatAdd/Lifted.lean .lake/verification/Lifted.lean
printf '%s\n' 'FVA re-lift matches proof subject: PASS'

lake build
lake env leanexport SatAdd -- \
  SatAdd.Proof.r1_holds SatAdd.Proof.r2_holds SatAdd.Proof.r3_holds \
  > .lake/verification/proofs.ndjson
task_lean_prefix=$(lean --print-prefix)
for task_checker in leanchecker leanchecker-paranoid; do
  "$task_lean_prefix/bin/$task_checker" --silent --from-export .lake/verification/proofs.ndjson
  printf '%s: PASS\n' "$task_checker"
done
"$task_lean_prefix/bin/lean4lean" --import .lake/verification/proofs.ndjson
printf '%s\n' 'lean4lean: PASS'

cat > .lake/verification/nanoda.json <<'EOF'
{
  "use_stdin": false,
  "export_file_path": ".lake/verification/proofs.ndjson",
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "num_threads": 4,
  "nat_extension": true,
  "string_extension": true
}
EOF
"$task_lean_prefix/bin/nanoda_bin" .lake/verification/nanoda.json
printf '%s\n' 'nanoda: PASS'
for task_checker in con-leche con-ron; do
  "$task_lean_prefix/bin/$task_checker" .lake/verification/proofs.ndjson
  printf '%s: PASS\n' "$task_checker"
done
